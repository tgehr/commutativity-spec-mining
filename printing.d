module printing;

import std.stdio;
import std.traits, std.algorithm, std.array;
import formula, explore, occam;
import util;

//alias defaultInferenceMethod=inferSoundSpec;
alias defaultInferenceMethod=inferOccamSpec;

void printSpecs(T,alias inferenceMethod=defaultInferenceMethod)(int numSamples=0){
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
					printSpec!(T,m[i],m[j])(numSamples);
				}
			}
		}
	}
}

void printSpec(T,string m1,string m2,alias inferenceMethod=defaultInferenceMethod)(int numSamples=0){
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
	alias m1a=ID!(mixin("T."~m1));
	alias m2a=ID!(mixin("T."~m2));
	alias i1=Seq!(ParameterIdentifierTuple!m1a);
	alias i2=Seq!(ParameterIdentifierTuple!m2a);
	auto t1=(cast(string[])[i1]).map!(a=>(a~"₁")).array;
	auto t2=(cast(string[])[i2]).map!(a=>(a~"₂")).array;
	string r1=formatReturnType!(ReturnType!m1a)(1), r2=formatReturnType!(ReturnType!m2a)(2);
	write("φ(",m1,"(",t1.join(","),")/",r1,", ",m2,"(",t2.join(","),")/",r2,"): ");
	stdout.flush();
	auto spec=inferenceMethod!(T,m1,m2)(numSamples);
	//writeln("φ(",m1,"(",t1.join(","),")/r₁, ",m2,"(",t2.join(","),")/r₂): ",spec);
	writeln(spec);	
}
