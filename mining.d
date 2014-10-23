
module mining;

import std.stdio;
import std.traits, std.algorithm, std.array;
import formula, mine, occam, datatypes;
import util;

//alias defaultInferenceMethod=inferSoundSpec;
alias defaultInferenceMethod=inferOccamSpec;

void printSpecs(T,alias inferenceMethod=defaultInferenceMethod)(){
	writeln(T.stringof);
	alias m=Seq!(__traits(allMembers,T));
	bool dontConsider(string s){
		return s=="toString"||s=="clone"||s=="opEquals";
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
					write("φ(",m[i],"(",t1.join(","),")/r₁, ",m[j],"(",t2.join(","),")/r₂): ");
					stdout.flush();
					auto spec=inferenceMethod!(T,m[i],m[j]);
					//writeln("φ(",m[i],"(",t1.join(","),")/r₁, ",m[j],"(",t2.join(","),")/r₂): ",spec);
					writeln(spec);
				}
			}
		}
	}
}

void main(){
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
	
	// captured precisely in the fragment:
	printSpecs!(Set!int);
	printSpecs!(MultiSet!int);
	printSpecs!(MaxRegister!int);
	printSpecs!(Map!(int,int));
	printSpecs!RangeUpdate;
	printSpecs!(KDTree!int); // "1DTree"
	
	// mpt captured precisely in the fragment
	//printSpecs!(ArrayList!int);
	//writeln(inferOccamSpec!(ArrayList!int,"indexOf","set"));
 
	
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
