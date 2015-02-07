module mine; // (this module is a huge ugly hack, but it works.)
import formula, datatypes;
import util, hashtable, options;
import std.traits, std.array, std.algorithm, std.range;
import std.typecons, std.random, std.math, std.conv;

import std.stdio;
auto dw()(){ writeln(); }
auto dw(T...)(T args){ write(args[0]," "); dw(args[1..$]); }

template staticFilter(alias F,T...){
	static if(T.length){
		static if(F!(T[0])) alias staticFilter=Seq!(T[0],staticFilter!(F,T[1..$]));
		else alias staticFilter=staticFilter!(F,T[1..$]);
	}else alias staticFilter=T;
}

template callFilter(T){
	enum callFilter(string a)=
		a!="opEquals"&&
		a!="toString"&&
		a!="clone"&&
		isCallable!(mixin("T."~a));
}

import annotations;
void modify(T)(ref T t){
	alias methods=staticFilter!(callFilter!T,__traits(allMembers,T));

 sw:switch(uniform(0,methods.length)){
		foreach(i,m;methods){
			case i:
				alias method=ID!(mixin("T."~m));
				alias argNames=ParameterIdentifierTuple!method;
				ParameterTypeTuple!method args;
				foreach(j,ref x;args){
					alias sampler=obtainSamplerFor!(method,argNames[j]);
					//x=construct!(typeof(x))();
					if(!sampler().canSample(t)) return;
					x=sampler().sample!(T,method)(t);
				}
				try{ auto nt=t.clone(); mixin("nt."~m)(args); t=nt; }catch{}
				// writeln(m,"(",args,")");
				break sw;
		}
		default: assert(0);
	}
}

struct MethodArgs{
	int[] ints;
	bool[] bools;
}

bool sampleArgsWithSamplers(alias method,T)(MethodArgs ma, ref T t){
	int[] ints=ma.ints;
	bool[] bools=ma.bools;
	alias argts=ParameterTypeTuple!method;
	alias argNames=ParameterIdentifierTuple!method;
	foreach(j,S;argts){
		alias sampler=obtainSamplerFor!(method,argNames[j]);
		static if(!is(sampler==useDefault!(argNames[j]))){
			if(!sampler().canSample(t)) return false;
			auto v=sampler().sample!(T,method)(t);
			static if(is(S==int)) ints.front=v;
			else{
				static assert(is(S==bool));
				bools.front=v;
			}
		}
		static if(is(S==int))
			ints.popFront();
		else{
			static assert(is(S==bool));
			bools.popFront();
		}
	}
	return true;
}

Value runMethod(string m,T)(ref T arg, MethodArgs args){
	alias ma=ID!(mixin("T."~m));
	alias ty=ParameterTypeTuple!ma;

	enum code={
		string r="arg."~m~"(";
		size_t ii=0,bi=0;
		foreach(t;ty){
			static if(is(t==bool)) r~="args.bools["~to!string(bi++)~"],";
			else static if(is(t==int)) r~="args.ints["~to!string(ii++)~"],";
			else static assert(0, "unsupported parameter type: "~t.stringof);
		}
		return r~")";
	}();
	static if(is(typeof(mixin(code))==void)){
		return mixin(code),Value();
	}else return Value(mixin(code));
}

bool doCommute(string m1, string m2, T)(ref T t,MethodArgs[2] args,ref Value[2][2] res){
	T t1=t.clone();
	T t2=t.clone();
	assert(t1==t2);
	res[0][0]=runMethod!m1(t1,args[0]);
	res[0][1]=runMethod!m2(t1,args[1]);
	res[1][1]=runMethod!m2(t2,args[1]);
	res[1][0]=runMethod!m1(t2,args[0]);
	if(res[0]!=res[1]) return false;
	return t1==t2;
}


enum Quat{
	dunno,
	maybe,
	no,
	yes,
}

bool incompat(Quat a,Quat b){
	return a==Quat.yes&&b==Quat.no||
		b==Quat.yes&&a==Quat.no;
}

struct ExploreStore{
	@disable this();
	this(Type[] split){
		this.split=split;
		if(split.length)
			r=new InternalNode(split[0]==Type.int_?1:2);
		else r=new Leaf();
	}
	size_t count(){
		return r.countLeaves();
	}
	bool foundAll(){ return r.full(); }
	void randomlyFindArgs(MethodArgs[2] a){
		auto ints=chain(a[0].ints,a[1].ints);
		auto bools=chain(a[0].bools,a[1].bools);
		assert(split.count!(a=>a==Type.int_)>=ints.length);
		assert(split.count!(a=>a==Type.bool_)>=bools.length);
		if(!split.length) return;
		OrderedPartition p;
		r.randomlyFind(0,split,p,ints,bools);
	}

	private static resfilter(string s)(Value[] r){
		return r[].filter!(a=>a.type==mixin(`Type.`~s)).map!(a=>mixin(`a.`~s));
	}
	void addResult(MethodArgs[2] a, Value[2] res, bool c){
		auto resints=resfilter!`int_`(res[].expandTuples());
		auto resbools=resfilter!`bool_`(res[].expandTuples());
		auto ints=chain(a[0].ints,a[1].ints,resints);
		auto bools=chain(a[0].bools,a[1].bools,resbools);
		OrderedPartition p;
		r.add(split,p,ints,bools,c);
	}
	Formula getFormula(Terminal[] ints, Terminal[] bools){
		OrderedPartition p;
		auto b=new bool[](bools.length);
		return r.getFormula(0,0,split,p,b,ints,bools); // TODO
	}
private:
	static class Node{
		alias CI2=typeof(chain((int[]).init,(int[]).init));
		alias CB2=typeof(chain((bool[]).init,(bool[]).init));
		void randomlyFind(size_t ci,Type[] split, ref OrderedPartition p, CI2 ints, CB2 bools){
			assert(ci==ints.length && !bools.length);
			p.assignRandomly(ints);
		}
		alias CI3=typeof(chain((int[]).init,(int[]).init,resfilter!`int_`((Value[]).init)));
		alias CB3=typeof(chain((bool[]).init,(bool[]).init,resfilter!`bool_`((Value[]).init)));
		abstract void add(Type[] split,ref OrderedPartition p,CI3 ints, CB3 bools,bool c);
		abstract bool full();
		abstract Formula getFormula(size_t ci,size_t cb,Type[] split, ref OrderedPartition p,bool[] b,Terminal[] ints, Terminal[] bools);
		abstract size_t countLeaves();
	}
	static class InternalNode: Node{
		this(size_t length){
			next = new Node[](length);
		}
		override void randomlyFind(size_t ci,Type[] split, ref OrderedPartition p, CI2 ints, CB2 bools){
			if(ci==ints.length && !bools.length)
				return super.randomlyFind(ci,split,p,ints,bools);
			assert(split.length);
			switch(split[0]){
			case Type.int_:
				auto l=uniform(0,next.filter!(a=>!a||!a.full||full).walkLength());
				foreach(i,ref n;next){
					if(n&&n.full&&!full||l--) continue;
					version(VERY_VERY_VERBOSE) writeln("adding ",ci," at ",i);
					p.addAt(cast(int)ci,i);
					version(VERY_VERY_VERBOSE) writeln(p);
					allocnext(split,i,p.length);
					return n.randomlyFind(ci+1,split[1..$],p,ints,bools);
				}
				assert(0);
			case Type.bool_:
				bools[0]=construct!bool();
				allocnext(split,bools[0],p.length);
				return next[bools[0]].randomlyFind(ci,split[1..$],p,ints,bools[1..$]);
			default: assert(0);
			}
		}
		void allocnext(Type[] split,size_t i, size_t plen){
			if(!next[i]){
				if(split.length==1)
					next[i]=new Leaf();
				else{
					assert(split.length);
					next[i]=new InternalNode(split[1]==Type.int_?2*plen+1:2);
				}
			}
		}
		override void add(Type[] split,ref OrderedPartition p,CI3 ints, CB3 bools,bool c){
			//dw(split,p,ints,bools,c);
			switch(split[0]){
			case Type.int_:
				assert(!ints.empty);
				auto i=p.getIndex(ints.front);
				p.addAt(ints.front,i);
				ints.popFront();
				allocnext(split,i,p.length);
				bool f=next[i].full();
				next[i].add(split[1..$],p,ints,bools,c);
				if(!f&&next[i].full) found++;
				break;
			case Type.bool_:
				assert(!bools.empty);
				auto i=bools.front;
				bools.popFront();
				allocnext(split,i,p.length);
				bool f=next[i].full();
				next[i].add(split[1..$],p,ints,bools,c);
				if(!f&&next[i].full) found++;
				break;
			default: assert(0);
			}
		}
		override bool full(){ return found==next.length; }
		override Formula getFormula(size_t ci, size_t cb, Type[] split,ref OrderedPartition p, bool[] b, Terminal[] ints,Terminal[] bools){
			Formula r=ff;
			void add(Formula φ){
				r=φ is ff?r:r is ff?φ:r.or(φ);
			}
			assert(split.length);
			switch(split[0]){
			case Type.int_:
				foreach(i,n;next){
					if(!n) continue;
					p.addAt(cast(int)ci,i);
					add(n.getFormula(ci+1,cb,split[1..$],p,b,ints,bools));
					p.remove(ci);
				}
				break;
			case Type.bool_:
				foreach(i,n;next){
					if(!n) continue;
					b[cb]=!!i;
					add(n.getFormula(ci,cb+1,split[1..$],p,b,ints,bools));
				}
				break;
			default: assert(0);
			}
			return r;
		}
		override size_t countLeaves(){
			return reduce!"a+b"(cast(size_t)0,next.map!(a=>a?a.countLeaves():0));
		}
	private:
		Type type;
		size_t found;
		Node[] next;
	}
	static class Leaf: Node{
		Quat value=Quat.dunno;
		override void add(Type[] split,ref OrderedPartition p,CI3 ints, CB3 bools,bool c){
			//if(c) writeln(p);
			assert(split.empty && ints.empty && bools.empty);
			final switch(value){
			case Quat.dunno: value=c?Quat.yes:Quat.no; break;
			case Quat.yes: if(!c) value=Quat.maybe; break;
			case Quat.no: if(c) value=Quat.maybe; break;
			case Quat.maybe: break;
			}
		}
		override bool full(){ return value != Quat.dunno; }
		override Formula getFormula(size_t ci, size_t cb,Type[] split,ref OrderedPartition p,bool[] b,Terminal[] ints,Terminal[] bools){
			assert(!split.length);
			assert(ci==ints.length&&cb==bools.length);
			if(value!=Quat.yes) return ff;
			Formula r=p.getFormula(ints);
			void add(Formula φ){
				r=φ is tt?r:r is tt?φ:r.and(φ);
			}
			foreach(i,x;b) add(x?bools[i]:not(bools[i]));
			return r;
		}
		override size_t countLeaves(){
			return 1;
		}
	}
	Type[] split;
	Node r;
}

struct EquivAssignment{
	Assignment a;
	static if(enableSampleSizeReduction){
		bool opEquals(EquivAssignment e){
			foreach(ta1,va1;a){
				if(va1.type==Type.bool_){
					if(va1!=e.a[ta1]) return false;
				}else foreach(tb2,vb2;e.a)
					if((va1<=a[tb2])!=(e.a[ta1]<=vb2))
						return false;
			}
			return true;
		}
		size_t toHash(){
			size_t hash=FNV(0);
			foreach(ta1,va1;a){
				if(va1.type==Type.bool_)
					hash=FNV(va1.bool_,hash);
				else foreach(ta2,va2;a)
					hash=FNV(va1<=va2,hash);
			}
			return hash;
		}
	}else{
		bool opEquals(EquivAssignment e){ return a==e.a; }
		size_t toHash(){ return typeid(a).getHash(&a); }
	}
	string toString(){ return a.toString()~"ₑ"; }

	Formula getFormula(){ // (for testing)
		Formula r=tt;
		foreach(ta1,va1;a){
			if(va1.type==Type.bool_){
				r=r.and(va1.bool_?ta1:not(ta1));
			}else foreach(ta2,va2;a){
				if(va2.type!=Type.int_) continue;
				Formula d;
				if(va1==va2) d=eq(ta1,ta2);
				else if(va1<va2) d=lt(ta1,ta2);
				else d=lt(ta2,ta1);
				r=r.and(d);
			}
		}
		return r.normalize;
	}
}

struct ResultStore{
	MapX!(EquivAssignment,Quat) map;

	Terminal[] terms(Type ty){
		foreach(k,v;map){
			Terminal[] r;
			foreach(t,val;k.a){
				if(val.type==ty)
					r~=t;
			}
			return r;
		}
		return [];
	}

	void addResult(Assignment a,bool c){
		auto ea=EquivAssignment(a);
		if(ea !in map)
			map[ea]=c?Quat.yes:Quat.no;
		else{
			final switch(map[ea]){
			case Quat.dunno: assert(0);
			case Quat.maybe: break;
			case Quat.yes: if(!c) map[ea]=Quat.maybe; break;
			case Quat.no: if(c) map[ea]=Quat.maybe; break;
			}
		}
	}

	Quat get(Assignment a){
		auto ea=EquivAssignment(a);
		if(ea !in map) return Quat.dunno;
		return map[ea];
	}

	bool[2] intSymmetric(alias incompat)(Terminal a, Terminal b){
		bool[2] r=[true,true];
		foreach(k,v;map){
			if(!(k.a[a]<k.a[b]&&k.a.areAdjacent(a,b))) continue;
			if(!incompat(v,get(k.a.updateAll(a,k.a[b])))) continue;
			if(incompat(v,get(k.a.swap(a,b)))){
				if(v!=Quat.yes) r[1]=false;
				else r[0]=false;
				if(!r[0]&&!r[1]) return r;
			}
		}
		return r;
	}

	bool[2] intEquatable(alias incompat,bool occam)(Terminal a, Terminal b){
		bool[2] r=[true,true];
		foreach(k,v;map){
			auto va=k.a[a], vb=k.a[b];
			if(va!=vb){
				// TODO: this works, but is not as awesome as it might be...
				if(!k.a.areAdjacent(a,b)) continue;
				if(incompat(v,get(k.a.swap(a,b)))) continue;
				if(incompat(v,get(k.a.updateAll(a,vb)))){
					if(v!=Quat.yes) r[0]=false;
					else r[1]=false;
					if(!r[0]&&!r[1]) return r;
				}
			}
		}
		return r;
	}

	bool[2] boolSymmetric(alias incompat)(Terminal t){
		bool[2] r=[true,true];
		foreach(k,v;map){
			auto vt=k.a[t].bool_;
			if(incompat(v,get(k.a.update(t,Value(!vt))))){
				if((v!=Quat.yes)^vt) r[0]=false;
				else r[1]=false;
				if(!r[0]&&!r[1]) return r;
			}
		}
		return r;
	}

	Formula getFormula(){ // (for debugging)
		Formula r=ff;
		foreach(k,v;map) if(v==Quat.yes) r=r.or(k.getFormula());
		return r.normalize;
	}
}

ResultStore maybeToNo(ResultStore s){
	typeof(s.map) map;
	foreach(k,v;s.map)
		if(v==Quat.maybe) map[k]=Quat.no;
		else map[k]=v;
	return ResultStore(map);
}

private bool soundincompat(Quat a,Quat b){ return (a==Quat.yes)^(b==Quat.yes); }
FormulaSet extractRelevantBasicPredicates(alias incompat=soundincompat,bool occam=false,bool returnAll=false)(ResultStore s){
	FormulaSet r;
	auto ints=s.terms(Type.int_);
	auto bools=s.terms(Type.bool_);
	foreach(x;bools){
		static if(!returnAll) auto b=s.boolSymmetric!incompat(x);
		else bool[2] b=[false,false];
		if(!b[0]||!occam&&!b[1]) r.insert(x);
		if(!b[1]||!occam&&!b[0]) r.insert(not(x));
	}
	foreach(x;ints){
		foreach(y;ints){
			if(x is y) continue;
			static if(!returnAll) auto be=s.intEquatable!(incompat,occam)(x,y);
			else bool[2] be=[false,false];
			if(!be[0]||!occam&&!be[1]) r.insert(x.eq(y));
			if(!be[1]||!occam&&!be[0]) r.insert(not(x.eq(y)));
		}
	}
	foreach(x;ints){
		foreach(y;ints){
			static if(!returnAll) auto bs=s.intSymmetric!incompat(x,y);
			else bool[2] bs=[false,false];
			if(!bs[0]||!occam&&!bs[1]) r.insert(x.lt(y));
			if(!bs[1]||!occam&&!bs[0]) r.insert(not(x.lt(y)));
		}
	}
	return r;
}


auto inferSoundSpec(T, string m1, string m2)(int numSamples){
	ResultStore s;
	void addSoundResult(Assignment a,bool c){
		s.addResult(a,c);
	}
	runExploration!(T,m1,m2,addSoundResult)(numSamples);
	auto bp=extractRelevantBasicPredicates(s).array;
	return s.getFormula().minimalEquivalent(bp);
}
private struct Void{}

struct ExplorationState(T, string m1, string m2, alias putResult=Void){
	alias m1a=ID!(mixin("T."~m1));
	alias m2a=ID!(mixin("T."~m2));
	alias ty1=Seq!(ParameterTypeTuple!m1a,ReturnType!m1a);
	alias ty2=Seq!(ParameterTypeTuple!m2a,ReturnType!m2a);
	alias i1=Seq!(ParameterIdentifierTuple!m1a);
	alias i2=Seq!(ParameterIdentifierTuple!m2a);
	Terminal[] t1,t2;

	Terminal[] tbools;
	Terminal[] tints;
	Type[] split;

	int[] ints1,ints2;
	bool[] bools1,bools2;

	ExploreStore exploration;

	static if(!is(putResult==Void)){
		size_t nrint=is(ty1[$-1]==int)+is(ty2[$-1]==int);
		size_t nrbool=is(ty1[$-1]==bool)+is(ty2[$-1]==bool);
		Terminal[] terms;
	}
	private void handle(T,bool isarg=true)(int methodIndex,ref int[] ints,ref bool[] bools,Terminal t){
		static if(is(T==bool)){
			tbools~=t;
			static if(isarg) bools~=false;
			split~=Type.bool_;
		}else static if(is(T==int)){
			tints~=t;
			static if(isarg) ints~=0;
			split~=Type.int_;
		}else static if(is(T==void)){
			// nothing to do
		}else static if(is(T==Tuple!U,U...)){
			foreach(i,S;U){
				static if(i+1>=U.length||!is(typeof(U[i+1])==string))
					string name="π"~lowSuffix(i+1)~"("~t.toString()~")";
				else string name=U[i+1]~lowSuffix(methodIndex);
				static if(is(S)) handle!(S,isarg)(methodIndex,ints,bools,.t(name));
			}
		}else static assert(is(T==void),"unsupported parameter type: "~T.stringof);
	}
	@disable this();
	this(int){
		t1=[i1,"r"].map!(a=>(a~"₁").t).array;
		t2=[i2,"r"].map!(a=>(a~"₂").t).array;
		foreach(i,tt;ty1[0..$-1]) handle!tt(1,ints1,bools1,t1[i]);
		foreach(i,tt;ty2[0..$-1]) handle!tt(2,ints2,bools2,t2[i]);
		terms=tints~tbools;
		auto intlen=tints.length, boollen=tbools.length;
		handle!(ty1[$-1],false)(1,ints1,bools1,t1[$-1]);
		terms~=tints[intlen..$]~tbools[boollen..$];
		intlen=tints.length, boollen=tbools.length;
		handle!(ty2[$-1],false)(2,ints2,bools2,t2[$-1]);
		terms~=tints[intlen..$]~tbools[boollen..$];
		exploration=ExploreStore(split);
	}
}

auto runExploration(T, string m1, string m2, alias putResult=Void)(int numSamples=0){
	auto state=ExplorationState!(T,m1,m2,putResult)(0);
	return runExplorationWithState!(T,m1,m2,putResult)(state,numSamples);
}

auto runExplorationWithState(T, string m1, string m2, alias putResult=Void)(ExplorationState!(T,m1,m2,putResult) state,int numSamples=0){ with(state){
	MethodArgs[2] a=[MethodArgs(ints1,bools1),MethodArgs(ints2,bools2)];

	void addResult(MethodArgs[2] a,Value[2] res,bool c,ref T t){
		exploration.addResult(a,res,c);
		static if(!is(putResult==Void)){
			putResult(Assignment(terms, chain(
						chain(ints1,ints2).map!Value,
						chain(bools1,bools2).map!Value,
						res[].expandTuples().filter!(a=>a.type!=Type.none_)).array),c,t);
		}
	}
	void randomExploration(int max){
		T t;
		auto maxNumInactive=long.max;
		int numInactive=0,i=0;
		for(;i<max;i++){
			if(!uniform(0,10)) t=T.init;
			foreach(_;0..uniform(0,10)) modify(t);
			static if(enableTypeAwareSampling){
				bool random=false;
				if(!exploration.foundAll()) exploration.randomlyFindArgs(a);
				else random=true;
			}else enum random=false;
			if(random||uniform(0,2)){ // try to observe the same class multiple times as well
				foreach(ref ar;a){
					foreach(ref x;ar.ints)x=construct!int();
					foreach(ref x;ar.bools)x=construct!bool();
				}
			}
			////
			if(!sampleArgsWithSamplers!m1a(a[0],t)){ --i; continue; }
			if(!sampleArgsWithSamplers!m2a(a[1],t)){ --i; continue; }
			////
			// if(!(i%10000)) writeln(i);
			Value[2][2] res;
			bool c;
			try c=doCommute!(m1,m2)(t,a,res); catch{ --i; continue; }
  			auto nr=exploration.count();
			scope(success) if(exploration.count()==nr) numInactive++; else numInactive=0;
			addResult(a,res[0],c,t);
			if(!c){ addResult(a,res[1],c,t); i++; }
			// if(nr!=exploration.count()) writeln("found result using ",t);
			version(VERBOSE) if(!(i%10000)) writeln("iteration #",i,"\t #results found: ",exploration.count());
		}
		version(VERBOSE_BOUNDS){
			assert(i>=max||numInactive>=maxNumInactive);
			writeln("hit bound of ",i>=max?"samples":"inactivity");
		}
	}
	void boundedExhaustiveExploration(int intLowerBound,int intUpperBound,size_t numOps){
		alias methods=staticFilter!(callFilter!T,__traits(allMembers,T));
		T t;
		T[] allArgs;
		version(VERY_VERBOSE) int cchecks=0;
		void run(size_t numOps){
			void checkCommutativity(size_t argPos){
				version(VERY_VERBOSE) if(!argPos&&!(++cchecks%1000)) writeln("check #",cchecks);
				if(argPos==a[0].ints.length+a[1].ints.length+a[0].bools.length+a[1].bools.length){
					auto tbefore=t.clone();
					Value[2][2] res;
					bool c;
					try c=doCommute!(m1,m2)(t,a,res); catch return;
					addResult(a,res[0],c,t);
					if(!c) addResult(a,res[1],c,t);
					t=tbefore;
				}else if(argPos>=a[0].ints.length+a[1].ints.length){
					auto boolPos=argPos-a[0].ints.length-a[1].ints.length;
					foreach(b;0..1){
						a[boolPos>=a[0].bools.length]
							.bools[boolPos>=a[0].bools.length?boolPos-a[0].bools.length:boolPos]=!!b;
						checkCommutativity(argPos+1);
					}
				}else{
					foreach(i;intLowerBound..intUpperBound+1){
						a[argPos>=a[0].ints.length].ints[argPos>=a[0].ints.length?argPos-a[0].ints.length:argPos]=i;
						checkCommutativity(argPos+1);
					}
				}
			}
			checkCommutativity(0);
			if(numOps==0) return;
			T tbefore=t.clone();
			foreach(i,m;methods){
				alias method=ID!(mixin("T."~m));
				ParameterTypeTuple!method args;
				// TODO: this repetition is very ugly
				void runIt(alias x,size_t argPos)(){
					static if(argPos<args.length){
						static if(is(typeof(args[argPos])==bool)){
							foreach(b;0..1){
								args[argPos]=!!b;
								runIt!(x,argPos+1)();
							}
						}else static if(is(typeof(args[argPos])==int)){
							foreach(i;intLowerBound..intUpperBound+1){
								args[argPos]=i;
								runIt!(x,argPos+1)();
							}
						}else{
							// TODO: be exhaustive here also?
							runIt!(x,argPos+1)();
						}
					}else{
						try mixin("t."~m)(args); catch return;
						//writeln(m," ",numOps," <<>> ",args);
						//writeln(t);
						if(t != tbefore) run(numOps-1);
					}
				}
				runIt!(i,0)();
			}
			t=tbefore.clone();
		}
		run(numOps);
	}
	//boundedExhaustiveExploration(-2,2,3);
	//boundedExhaustiveExploration(0,1,3);
	//randomExploration(2000000);
	//randomExploration(500000);
	//randomExploration(5000);
	randomExploration(numSamples);
	//writeln("tried ",numFound, " assignments");
	// if(numFound != (1<<atoms.length)) writeln("warning: not all combinations of atoms satisfied");
	version(VERBOSE) writeln("number of variations found: ",exploration.count());
	// version(VERBOSE){ exploration.randomlyFindArgs(a); writeln("not found: ",a); }
	static if(is(putResult==Void)){
		auto f=exploration.getFormula(tints,tbools);
		version(VERY_VERY_VERBOSE) writeln(f);
		f=f.simplify;
		return f;
	}
}}

//version=VERBOSE;
//version=VERY_VERBOSE;

//pragma(msg, __traits(allMembers, Set!int));
