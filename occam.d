import std.array, std.algorithm, std.stdio;
import mine, formula;
import hashtable;


private auto inferOccamSpecCommon(alias s,alias addOccamResult,T,string m1,string m2)(int numSamples){
	runExploration!(T,m1,m2,addOccamResult)(numSamples);
	s=s.maybeToNo();
	version(VERBOSE) writeln("inferring formula...");
	auto bp=extractRelevantBasicPredicates!(incompat,true)(s).array;
	version(VERY_VERBOSE) writeln(bp,"\n",s);
	//writeln(bp.length," ",bp);
	auto f=greedyEquivalentTo(s,bp);
	f=f.factorGreedily();
	//auto f=minimalEquivalentTo(s,bp);
	//auto f=monteCarloMarkovChainEquivalentTo(s,bp);
	if(!f) f=s.getFormula();
	return f;
}

auto inferOccamSpec(T, string m1, string m2)(int numSamples=5000){
	ResultStore s;
	bool[] isNew;
	void addOccamResult(Assignment a,bool c,ref T t){
		isNew~=EquivAssignment(a) !in s.map;
		s.addResult(a,c);
	}
	auto r=inferOccamSpecCommon!(s,addOccamResult,T,m1,m2)(numSamples);
	/*size_t window=min(1000,isNew.length);
	double rate=0;
	foreach(x;isNew[$-window..$]) rate+=x;
	rate/=window;
	writeln("rate of new logical types at end: ",rate);*/
	return r;
}

//version=VERBOSE;
//version=VERY_VERBOSE;
auto inferExistentialOccamSpec(T, string m1, string m2, methods...)(int numSamples=5000){
	ResultStore s;
	Terminal[] eterms;
	Terminal[] qterms;
	import std.traits,std.conv;
	import util,annotations;
	foreach(i,m;methods){
		alias method=ID!(mixin("T."~m));
		static assert(!is(ReturnType!method==void));
		alias argNames=ParameterIdentifierTuple!method;
		enum suffix=(delegate string(int i)=>
					 (i>10?__traits(parent,{})(i/10):"")
					 ~ text("₀₁₂₃₄₅₆₇₈₉"d[(i+3)%10]))(i);
		Terminal[] ceterms;
		foreach(arg;argNames){
			alias sampler=obtainSamplerFor!(method,arg);
			static assert(is(typeof({T t;sampler().exhaustive(t);})),"cannot enumerate parameter: "~arg);
			ceterms~=t(arg~suffix);
		}
		eterms~=ceterms;
		qterms~=ceterms;
		eterms~=t(m~"("~ceterms.map!(to!string).join(",")~")");
	}
	auto values=new Value[](eterms.length);
	void addOccamResult(Assignment a,bool c,ref T t){
		void go(int i,int j,int cur)(){
			static if(i>=methods.length){
				auto b=a.extend(Assignment(eterms,values));
				s.addResult(b,c);
			}else{
				alias method=ID!(mixin("T."~methods[i]));
				alias argNames=ParameterIdentifierTuple!method;
				static if(j==argNames.length){
					ParameterTypeTuple!method args;
					//args[0]=values[cur-1].int_; // TODO: fix this.
					foreach(i,ref arg;args){
						arg=values[cur-args.length+i].get!(typeof(arg))();
					}
					values[cur]=Value(mixin("t."~methods[i])(args));
					go!(i+1,0,cur+1);
				}else{
					alias arg=argNames[j];
					alias sampler=obtainSamplerFor!(method,arg);
					foreach(v;sampler().exhaustive(t).map!Value){
						values[cur]=v;
						go!(i,j+1,cur+1);
					}
				}
			}
		}
		go!(0,0,0);
	}
	auto f=inferOccamSpecCommon!(s,addOccamResult,T,m1,m2)(numSamples);	
	foreach_reverse(q;qterms){
		f=new Exists(q,f);
	}
	return f;
}

bool equivalentOn(Formula f,Formula g,ResultStore s){
	foreach(k,_;s.map) if(evaluate(f,k.a)!=evaluate(g,k.a)) return false;
	return true;
}

bool equivalentTo(Formula g,ResultStore s){
	foreach(k,v;s.map) if(incompat(evaluate(g,k.a)?Quat.yes:Quat.no,v)) return false;
	return true;
}

bool impliesOn(Formula f, Formula g, ResultStore s){
	foreach(k,_;s.map) if(evaluate(f,k.a)&&!evaluate(g,k.a)) return false;
	return true;
}

bool implies(Formula g, ResultStore s){
	foreach(k,v;s.map) if(evaluate(g,k.a)&&incompat(v,Quat.yes)) return false;
	return true;
}

size_t equivClassHashOn(Formula f,ResultStore s){
	size_t h=fnvb;
	foreach(k,_;s.map){
		auto b=evaluate(f,k.a);
		h=FNV(b,h);
	}
	return h;
}

size_t equivClassHashOf(ResultStore s){
	size_t h=fnvb;
	foreach(k,v;s.map){
		auto b=v==Quat.yes;
		h=FNV(b,h);
	}
	return h;
}

struct EquivOnFormula{
	Formula f;
	this(Formula f,ResultStore s){
		this.f=f; this.s=s;
		theHash=f.equivClassHashOn(s);
	}
	bool opEquals(EquivOnFormula rhs/+,ResultStore s+/){ return theHash == rhs.theHash && equivalentOn(f,rhs.f,s); }
	size_t toHash(){ return theHash; }
private:
	size_t theHash;
	ResultStore s; // this sux
}


struct NonEquivalentMinimalFormulasOn(T...){
	this(ResultStore st,size_t sizeLimit,Formula[] bp){
		this.st=st; this.sizeLimit=sizeLimit;
		foreach(index;0..2){
			memo[index].length=2;
			memo[index][1]=bp;
		}
	}
	int opApply(scope int delegate(EquivOnFormula) dg){
		foreach(s;0..sizeLimit){
			foreach(f;iterateThroughSize(s))
				if(auto r=dg(f)) return r;
		}
		return 0;
	}
	struct IterateThroughSize{
		size_t s;
		NonEquivalentMinimalFormulasOn* outer;
		int opApply(scope int delegate(EquivOnFormula) dg){
			foreach(g;allFormulasOfSize!(T,(f){
						auto feq=EquivOnFormula(f,outer.st);
						if(feq in outer.minSet) return false;
						outer.minSet.insert(feq);
						outer.hashesMap[f]=feq;
						return true;})(s,outer.memo)){
				if(g !in outer.hashesMap) outer.hashesMap[g]=EquivOnFormula(g,outer.st);
				if(auto r=dg(outer.hashesMap[g])) return r;
			}
			return 0;
		}
	}
	IterateThroughSize iterateThroughSize(size_t s){
		return IterateThroughSize(s,&this);
	}
private:
	ResultStore st;
	size_t sizeLimit;
	Formula[][][2] memo;
	HSet!(EquivOnFormula,(a,b)=>a.opEquals(b),a=>a.toHash()) minSet;
	HashMap!(Formula,EquivOnFormula,(a,b)=>a is b, a=>a.toHash()) hashesMap; // TODO: this is a hack.
}

// version=VERY_VERBOSE;
Formula minimalEquivalentTo(ResultStore s,Formula[] bp){
	auto fhash=equivClassHashOf(s);
	foreach(EquivOnFormula g;NonEquivalentMinimalFormulasOn!()(s,100,bp)){
		version(VERY_VERBOSE){ import std.stdio; writeln("s: ",g.f.size()," considering formula ",g.f," ",g.toHash()); }
		if(g.toHash()!=fhash) continue;
		if(g.f.equivalentTo(s))
			return g.f;
	}
	return null;
}
// version=VERY_VERBOSE;


size_t numSharedOn(Formula g, ResultStore s,size_t min){
	size_t num=0;
	size_t tot=s.map.length;
	foreach(k,v;s.map){
		if(!incompat(evaluate(g,k.a)?Quat.yes:Quat.no,v)) num++;
		tot--;
		if(tot+num<min) return 0;
	}
	return num;
}

ResultStore removeFrom(Formula f, ResultStore s){
	size_t num=0;
	typeof(s.map) map;
	foreach(k,v;s.map) if(!evaluate(f,k.a)) map[k]=v;
	return ResultStore(map);
}

ResultStore trueAssignments(ResultStore s){
	typeof(s.map) map;
	foreach(k,v;s.map) if(v==Quat.yes) map[k]=v;
	return ResultStore(map);
}

Formula greedyEquivalentTo(ResultStore s,Formula[] bp){
	if(ff.equivalentTo(s)) return ff;
	Formula[] formulas;
	Formula tryBuild(size_t maxNumDisjuncts)in{assert(formulas.length);}body{
		auto tmps=s.trueAssignments();
		Formula r=ff;
		foreach(d;0..maxNumDisjuncts){
			Formula best=null;
			double bestScore=0;
			foreach(xf;formulas){
				auto siz=xf.size();
				auto numShared=numSharedOn(xf,tmps,cast(size_t)(bestScore*siz));
				if(numShared==tmps.map.length)
					return r.or(xf).normalize;
				auto curScore=cast(double)numShared/siz;
				if(!best||curScore>bestScore){
					bestScore=curScore;
					best=xf;
				}
			}
			if(bestScore==0) return null;
			tmps=removeFrom(best,tmps);
			r=r.or(best);
			assert(tmps.map.length);
		}
		return null;		
	}
	auto minformulas=NonEquivalentMinimalFormulasOn!And(s,100,bp);
	foreach(curSiz;0..100){
		foreach(EquivOnFormula g;minformulas.iterateThroughSize(curSiz)){
			if(g.f.implies(s)) formulas~=g.f;
		}
		if(formulas.length) if(auto r=tryBuild(curSiz*2)) return r;
	}
	return null;
}


import std.random, std.math;
size_t numIncompatOn(Formula f, ResultStore s){
	size_t num;
	foreach(k,v;s.map) if(incompat(evaluate(f,k.a)?Quat.yes:Quat.no,v)) num++;
	return num;
}

Formula monteCarloMarkovChainEquivalentTo(ResultStore s,Formula[] bp){
	Formula current=tt;
	Formula bestEquivalent=null;
	immutable double gamma=1e-2;
	int i=0;
	Formula proposeTransition(Formula f){
		// TODO: ensure symmetry
		FormulaSet mutateFormulaSet(FormulaSet arg){
			auto o=arg.dup();
			Formula toRemove=null;
			size_t i=0,r=uniform(0,o.length);
			foreach(x;arg)
				if(++i==r){
					o.remove(x);
					if(uniform(0,2)){
						o.insert(proposeTransition(x));
					}
					break;
				}
			return o;
		}
		if(auto af=cast(And)f) return and(mutateFormulaSet(af.operands));
		if(auto of=cast(Or)f) return or(mutateFormulaSet(of.operands));
		if(!bp.length) return [tt,ff][uniform(0,$)];
		if(uniform(0,2)) return f.and(bp[uniform(0,$)]);
		else return f.or(bp[uniform(0,$)]);
	}
	double cost(Formula f){
		return (f.size()+1)*(numIncompatOn(f,s)*100.0/s.map.length+1);
	}
	auto currentCost=cost(current);
	auto bestCost=double.infinity;
	auto bound=100;
	for(;i<bound||bestEquivalent is null;i++){
		Formula candidate=proposeTransition(current);
		auto candidateCost=cost(candidate);
		//if(!(i%1000)) writeln(i,": ",current," ",currentCost," best: ",bestEquivalent," ",bestCost);
		//
		if(candidateCost < currentCost || uniform(0.0,1.0)<exp(gamma*(currentCost-candidateCost))){
			current=candidate;
			currentCost=candidateCost;
			if(currentCost<bestCost && current.equivalentTo(s)){
				bestEquivalent=current;
				bestCost=currentCost;
				if(i<bound) bound+=100;
				else bound=2*bound;
			}else bound--;
		}
	}
	//writeln(i);
	return bestEquivalent;
}
