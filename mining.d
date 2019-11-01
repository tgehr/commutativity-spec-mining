
module mining;

import std.stdio;
import std.traits, std.algorithm, std.array;
import formula, mine, occam;
import util;

//alias defaultInferenceMethod=inferSoundSpec;
alias defaultInferenceMethod=inferOccamSpec;

void printSpecs(T,alias inferenceMethod=defaultInferenceMethod)(int numSamples=0){
	writeln(T.stringof);
	alias m=Seq!(__traits(allMembers,T));
	bool dontConsider(string s){
		return s=="toString"||s=="clone"||s=="opEquals";
	}
	string formatReturnType(T)(int methodIndex){
		import std.typecons : Q=Tuple;
		static if(is(T==void)) return "()";
		else static if(is(T==Q!U,U...)){
			string s="(";
			int n=0;
			foreach(i,S;U){
				static if(i+1>=U.length||!is(typeof(U[i+1])==string))
					string name="π"~lowSuffix(i+1)~"(r"~lowSuffix(methodIndex)~")";
				else string name=U[i+1]~lowSuffix(methodIndex);
				if(is(S)){ if(n++) s~=","; s~=name; }
			}
			s~=")"; return s;
		}else return "r"~lowSuffix(methodIndex);
	}
	foreach(i,_;m){
		foreach(j,__;m){
			static if(!(j<i||dontConsider(m[i])||dontConsider(m[j]))){
				alias m1a=ID!(mixin("T."~m[i]));
				alias m2a=ID!(mixin("T."~m[j]));
				static if(isCallable!m1a&&isCallable!m2a){
					alias i1=Seq!(ParameterIdentifierTuple!m1a);
					alias i2=Seq!(ParameterIdentifierTuple!m2a);
					auto t1=(cast(string[])[i1]).map!(a=>(a~"₁")).array;
					auto t2=(cast(string[])[i2]).map!(a=>(a~"₂")).array;
					string r1=formatReturnType!(ReturnType!m1a)(1), r2=formatReturnType!(ReturnType!m2a)(2);
					write("φ(",m[i],"(",t1.join(","),")/",r1,", ",m[j],"(",t2.join(","),")/",r2,"): ");
					stdout.flush();
					auto spec=inferenceMethod!(T,m[i],m[j])(numSamples);
					//writeln("φ(",m[i],"(",t1.join(","),")/r₁, ",m[j],"(",t2.join(","),")/r₂): ",spec);
					writeln(spec);
				}
			}
		}
	}
}

Formula obtainDemoSpec(){
	ResultStore s;
	auto k1="k₁".t,k2="k₂".t,v1="v₁".t,v2="v₂".t,r1="r₁".t,r2="r₂".t;
	auto terms=[k1,v1,r1,k2,v2,r2];
	void add(int k1,int v1,int r1,int k2,int v2,int r2){
		writeln("(",k1,",",v1,",",r1,",",k2,",",v2,",",r2,") & ",k1!=k2||v1==r1&&v2==r2," \\\\");
		s.addResult(Assignment(terms,[Value(k1),Value(v1),Value(r1),Value(k2),Value(v2),Value(r2)]),
					k1!=k2||v1==r1&&v2==r2);
	}
	/+int[6][20] array;
	import std.random;
	foreach(ref a;array){
		foreach(ref x;a)
			x=uniform(0,5);
		add(a[0],a[1],a[2],a[3],a[4],a[5]);
	}
	writeln(array);+/
	/+foreach(a;[[0, 2, 1, 0, 2, 2], [2, 3, 4, 1, 0, 3], [1, 4, 3, 2, 2, 4]]){
		add(a[0],a[1],a[2],a[3],a[4],a[5]);
	}+/
	
	add(1,0,0,2,0,-1);
	add(2,0,-2,1,0,-1);
	add(1,2,2,1,1,2);
	add(1,-1,-1,1,1,-1);

	add(1,2,3,4,5,1);

	add(1,2,2,1,1,1);
	add(1,2,2,1,2,2);
	add(1,2,2,1,2,2);


	/*add(2,3,3,2,2,2);
	add(3,3,3,3,3,2);
	add(4,3,1,4,3,2);
	add(4,3,2,4,3,1);
	add(0,3,2,0,3,1);
	add(0,3,1,0,3,2);

	add(3,3,2,3,3,3);
	add(3,3,2,3,3,3);


	add(0,0,0,1,-3,0);
	add(0,0,0,1,3,0);
	add(1,2,-3,0,1,0);
	add(1,2,-3,1,3,2);
	add(1,2,3,1,3,-3);*/
	//[1, 3, 0, 4, 1, 3], [3, 2, 0, 2, 4, 1], [2, 0, 1, 0, 0, 0], [1, 1, 2, 1, 3, 4], [0, 1, 3, 2, 2, 0]
	//[3, 4, 3, 2, 4, 2], [1, 2, 0, 1, 2, 0], [0, 2, 0, 0, 4, 0], [4, 0, 0, 0, 4, 3]
	//[0, 2, 1, 0, 2, 2], [2, 3, 4, 1, 0, 3], [1, 4, 3, 2, 2, 4]
	auto bp=extractRelevantBasicPredicates!(incompat,true,true)(s);
	version(VERY_VERBOSE) writeln(bp,"\n",s);
	auto f=greedyEquivalentTo(s,bp);
	f=f.factorGreedily();
	//auto f=minimalEquivalentTo(s,bp);
	//auto f=s.getFormula();
	
	return f;
}

void main(){
	//writeln(obtainDemoSpec());
	//writeln(inferOccamSpec!(Map!(int,int),"put","put")(5));

	/+//code for generating some of the report
	/+auto a="a".t,b="b".t,c="c".t,d="d".t;
	//a < b ∧ b < c ∨ b < a ∧ b ≠ c
	auto φ=a.lt(b).and(b.lt(c)).or(b.lt(a).and(not(b.eq(c))));
	writeln(φ);
	writeln(φ.simplify);+/

	//a < b \land b < c \land a < d \land d=c \lor b=a \land b=c \land d\neq c\lor d < c \lor d < c\land d < c
	auto f = a.lt(b).and(b.lt(c)).and(a.lt(d)).and(d.eq(c)).or(b.eq(a).and(b.eq(c)).and(not(d.eq(c)))).or(d.lt(c)).or(d.lt(c).and(d.lt(c)));
	writeln(f);
	writeln(f.normalize());

	// computation of M in example 4.3
	int i=0;
	write("&");
	foreach(vbools,op;AllAssignments([a,b,c],[d])){
		writef("((%(\\{%(%s,%)\\},%)\\}),\\{d\\mapsto %s\\}),",op.p.map!(x=>x.map!(i=>[a,b,c][i])),["\\false","\\true"][vbools[d]]);
		if(!(++i%2)) writef("\\\\&");
	}
	writeln();
	// computation of s_. in example 4.3
	{auto ϕ=a.lt(b).or(not(b.eq(c)).and(d));
	auto φ=b.lt(c).and(d).or(a.lt(b).and(not(d))).or(d.and(c.lt(b))).or(a.lt(b).and(d));
	auto ψ=b.lt(c).and(d).or(a.lt(b).and(not(d))).or(d.and(c.lt(b)).and(not(a.lt(b))));
	writeln(ϕ);
	writeln(φ);
	writeln(ψ);
	string sϕ,sφ,sψ;
	foreach(vbools,op;AllAssignments([a,b,c],[d])){
		sϕ~=ϕ.evaluate(vbools,[a,b,c],op)?"1":"0";
		sφ~=φ.evaluate(vbools,[a,b,c],op)?"1":"0";
		sψ~=ψ.evaluate(vbools,[a,b,c],op)?"1":"0";
	}
	writeln("s_\\varphi&=",sϕ);
	writeln("s_\\phi&=",sφ);
	writeln("s_\\psi&=",sψ);}
	
	{auto φ=a.lt(b).and(b.lt(c)).or(b.lt(a).and(a.lt(c)));
		writeln(φ);
		//auto ψ=φ.simplify;
		auto ψ=not(a.eq(b)).and(b.lt(c)).or(not(a.eq(b)).and(a.lt(c)));
		writeln(ψ," ",φ.equivalent(ψ));
	}
	+/
	//writeln(inferOccamSpec!(Set!int,"has","add"));
	//writeln(inferOccamSpec!(RangeUpdate,"add2","square"));
	//writeln(inferOccamSpec!(MultiSet!int,"add","remove"));
	//writeln(inferOccamSpec!(Map!(int,int),"get","get"));
	//writeln(inferOccamSpec!(Map!(int,int),"put","put"));
	//writeln(inferOccamSpec!(RangeUpdate,"add2","add2"));

	/+import experiments;
	runExperiments();+/

	//printSpecs!VoidTest;
	//writeln(inferExistentialOccamSpec!(ExistentialTest,"add2until","squareFrom","get"));
	//writeln(inferExistentialOccamSpec!(ArrayList!int,"add_at","indexOf","get")(600000));
	//writeln(inferUniversalOccamSpec!(ArrayList!int,"add_at","indexOf","get")(600000)); // TODO: get this
	//printSpecs!(MultiSetTest!int);
	//writeln(inferExistentialOccamSpec!(MultiSetTest!int,"add","remove","contains"));
	//writeln(inferUniversalOccamSpec!(MultiSetTest!int,"add","remove","contains"));
	
	/+static existentialInferenceMethod(T,string m1,string m2)(int numSamples){
		return inferExistentialOccamSpec!(T,m1,m2,"contains");
	}

	printSpecs!(SetTest!int,existentialInferenceMethod);+/

	import experiments;
	//runExperiments();
	//printSpecs!(Map!(int,int));
	//writeln(inferOccamSpec!(BitList,"resize","findClosest")(5000));
	//writeln(inferOccamSpec!(Set!int,"add","remove"));
	//writeln(inferOccamSpec!(LexicographicProximityQuery,"insert","nextLarger"));
	//writeln(inferOccamSpec!(LexicographicProximityQuery,"remove","nextLarger"));
	//writeln(t.doCommute!("findFirst","shiftBlock")([MethodArgs([],[1]),MethodArgs([2,5])],res));
	//writeln(inferOccamSpec!(BitList,"findClosest","shiftBlock"));
	performMeasurements!printSpecs;
	//performMeasurements!measureTypeDiagrams();
	//runTypeCounting();
	// captured precisely in the fragment:
	/+printSpecs!(Set!int);
	printSpecs!(Map!(int,int));
	printSpecs!(MultiSet!int);
	printSpecs!(MaxRegister!int);
	printSpecs!RangeUpdate;
	printSpecs!(KDTree!int); // "1DTree"
	// not captured precisely in the fragment
	enum many=30000;
	enum more=50000;
	printSpecs!Accumulator;
	printSpecs!(UnionFind!("default",false))(many);
	printSpecs!(UnionFind!("min",false))(many);
	printSpecs!(UnionFind!("deterministic",false))(more);
	printSpecs!(UnionFind!"default")(many);
	printSpecs!(UnionFind!"min")(more);
	printSpecs!(UnionFind!"deterministic")(more);
	printSpecs!(ArrayList!int)(600000);
	//writeln(inferOccamSpec!(ArrayList!int,"indexOf","set")(30000));+/
 
	
	/+//(r₁ < v₁∨ v₂ ≤ r₁)∧ r₁ = r₂∧ (v₁ ≤ v₂∨ v₂ ≤ r₁)
	auto r1="r₁".t,r2="r₂".t,v1="v₁".t,v2="v₂".t;
	auto tbl=["r₁":r1,"r₂":r2,"v₁":v1,"v₂":v2];
	auto fapproach=r1.lt(v1).or(not(r1.lt(v2))).and(r1.eq(r2)).and(not(v2.lt(v1)).or(not(r1.lt(v2))));
	auto fours=not(r1.lt(v1)).and(not(r2.lt(v2))).and(r1.eq(r2));
	writeln(fapproach," ",fours);
	writeln("equivalent: ",equivalent(fapproach,fours));
	writeln("implies approach → ours: ",fapproach.checkImplies(fours));
	writeln("implies ours → approach: ",fours.checkImplies(fapproach));

	auto big=inferSpec!(MaxRegister!int,"set","set");
	Formula rew(Formula f){
		if(auto t=cast(Terminal)f){
			return tbl[t.name];
		}
		return f;
	}
	big=big.rewrite!rew;
	//writeln(big);

	writeln("implies big → ours: ",big.checkImplies(fours));
	writeln("implies ours → big: ",fours.checkImplies(big));

	writeln("implies big → approach: ",big.checkImplies(fapproach));
	writeln("implies approach → big: ",fapproach.checkImplies(big));+/

	/+Formula[][][2] memo;
	auto vbl=tuple(["e₁".t,"e₂".t,"e₃".t,"r₁".t,"r₂".t],/+["r₁".t,"r₂".t]+/(Terminal[]).init);
	//e₁ = e₂∧ e₁ = e₃∧ e₂ ≠ e₃;
	auto f = vbl[0][0].eq(vbl[0][1]).and(vbl[0][0].eq(vbl[0][2])).and(not(vbl[0][1].eq(vbl[0][2])));
	auto bp=vbl.allBasicPredicates(false);
	foreach(f;NonEquivalentMinimalFormulas(vbl,14,bp)){
		writeln(f);
	}+/
	/+foreach(f;NonEquivalentMinimalFormulas(tuple(["v₁".t,"v₂".t,"r₁".t,"r₂".t],(Terminal[]).init),10)){
		writeln(f);
	}+/
	//writeln("a".t.and("b".t.or("c".t.and(not("x".t.eq("d".t))))));

	//auto at="a".t, bt="b".t, ct="c".t, dt="d".t,et="e".t;
	//writeln(bt.eq(ct).and(at.lt(ct)).normalize);
	//writeln(at.eq(bt).and(bt.lt(ct)).and(at.lt(ct)).and(ct.lt(dt)).simplify);
	//auto f=at.lt(bt).or(bt.lt(at)).or(bt.eq(at));
	//writeln(f.simplify);

	/+auto spec=inferSpec!(Map!(int,int), "put", "size");
	writeln(spec);+/
	//auto spec=inferSpec!(Set!int,"add","add"); // ok
	//auto spec=inferSpec!(Set!int,"has","size"); // e1=r2 hard to satisfy
	//auto spec=inferSpec!(Set!int,"add","size"); // e1=r2 hard to satisfy
	//auto spec=inferSpec!(Set!int,"has","remove");
	//auto spec=inferSpec!(Set!int,"add","remove");
	//printSpecs!(MaxRegister!int);
	//printSpecs!(MultiSet!int);
	//writeln(inferSpec!(MultiSet!int,"num","num"));
	//printSpecs!RangeUpdate;
	//writeln(spec);
	//printSpecs!(Set!int)();
	//auto spec=inferSpec!(Set!int,"has","add",true);
	//writeln(spec);
	//printSpecs!(Map!(int,int))();
	//writeln(inferSpec!(Map!(int,int),"get","put")); 
	//writeln(inferSpec!(Map!(int,int),"get","get"));
	//writeln(inferSpec!(Map!(int,int),"put","put"));
	//writeln(inferSpec!(Map!(int,int),"get","size"));
	
	/+//key₂ = r₁∧ r₁ = r₂∨ key₁ ≠ r₁∧ r₁ = r₂∨ key₁ ≠ key₂
	auto k1="key₁".t, k2="key₂".t, r1="r₁".t, r2="r₂".t, v1="value₁".t, v2="value₂".t;
	//auto φ=k2.eq(r1).and(r1.eq(r2)).or(not(k1.eq(r1)).and(r1.eq(r2))).or(not(k1.eq(k2)));

	//key₁ ≠ r₁∧ r₁ = r₂∧ r₁ = value₂∨ key₁ = r₁∧ key₁ = value₂∧ key₁ = r₂∨
	//auto φ=not(k1.eq(r1)).and(r1.eq(r2)).and(r1.eq(v2)).or(k1.eq(r1).and(k1.eq(v2)).and(k1.eq(r2)));
	// r₁ = r₂∨ key₁ = r₁∧ key₁ = r₂
	//auto φ=r1.eq(r2).or(k1.eq(r1).and(k1.eq(r2)));
	// key₁ ≠ r₁∧ r₁ = r₂, key₁ = r₁∧ key₁ = r₂
	//auto φ = not(k1.eq(r1)).and(r1.eq(r2)).or(k1.eq(r1).and(k1.eq(r2)));
	//auto φ = k1.eq(k2).or(r1.eq(k1).and(r1.eq(k2)));
	//auto φ = k1.eq(r1).and(k1.eq(r2)).or(k1.lt(r1)).or(r1.lt(k1));
	//key₁ ≠ r₁∧ r₁ ≠ r₂∧ key₁ ≠ r₂ ∨ key₁ = r₁∧ key₁ ≠ r₂
	auto φ = not(k1.eq(r1)).and(not(r1.eq(r2))).and(not(k1.eq(r2))).or(k1.eq(r1).and(not(k1.eq(r2))));
	writeln(φ);
	writeln(φ.simplify);+/

	//printSpecs!(MaxRegister!int);
	//writeln(inferSpec!(Set!int,"add","add"));
}
