
import std.stdio, std.datetime, std.traits, std.algorithm, std.array, std.conv;

import datatypes,mine,formula,occam,util;

struct TimedSpec{
	Formula formula;
	TickDuration time;

	bool timedOut;
}

struct SpecStats{
	int numSamples;
	int numClasses;
	int totNumClasses;
	TickDuration exploration;
	TimedSpec greedy[2];
	TimedSpec exhaustive[2];
}

enum searchTimeout=10;

auto obtainTimedSpec(alias dg, bool isATimeout=false)(int searchTimeout){
	TimedSpec spec;
	static if(isATimeout){ spec.timedOut=true; }
	else{
		auto sw=StopWatch(AutoStart.yes);
		spec.formula=dg();
		spec.time=sw.peek();
	}
	return spec;
}

int computeNumClasses(int numVariables){
	int go(int n,int k){
		if(!k) return !n;
		if(n<k) return 0;
		import std.functional;
		alias g=memoize!go;
		return k*(g(n-1,k)+g(n-1,k-1));
	}
	int tot=0;
	alias n=numVariables;
	foreach(k;0..n+1) tot+=go(n,k);
	return tot;
}

auto inferTimedOccamSpec(T, string m1, string m2)(int numSamples=5000, int searchTimeout=searchTimeout){
	scope(exit){
		resetUniqueMaps();
		import core.memory;
		GC.collect();
	}
	SpecStats stats;
	ResultStore s;
	int actualNumSamples=0;
	void addOccamResult(Assignment a,bool c,ref T t){
		actualNumSamples++;
		s.addResult(a,c);
	}
	auto sw=StopWatch(AutoStart.yes);
	runExploration!(T,m1,m2,addOccamResult)(numSamples);
	s=s.maybeToNo();
	stats.exploration=sw.peek();
	stats.numSamples=actualNumSamples;
	stats.numClasses=cast(int)s.map.length;
	stats.totNumClasses=computeNumClasses(cast(int)s.terms(Type.int_).length)*cast(int)(2^^(s.terms(Type.bool_).length));
	version(VERY_VERBOSE) writeln(bp,"\n",s);
	//writeln(bp.length," ",bp);
	enum tooLargeForExhaustive = [
		is(T==Map!(int,int)) && m1=="put" && m2=="put" ||
		is(T==RangeUpdate) && m1=="add2" && m2=="square" ||
		is(T==KDTree!int) && m1=="add" && m2=="nearest" ||
		is(T==KDTree!int) && m1=="remove" && m2=="nearest" || 
		is(T==UnionFind!("deterministic",false)) && m1=="unite" && m2=="unite" ||
		is(T==UnionFind!("min",true)) && m1=="unite" && m2=="unite" ||
		is(T==UnionFind!("deterministic",true)) && m1=="unite" && m2=="unite"||
		is(T==ArrayList!int) && m1=="set" && m2=="set" ||
		is(T==ArrayList!int) && m1=="lastIndexOf" && m2=="set" ||
		is(T==ArrayList!int) && m1=="indexOf" && m2=="set",
		is(T==RangeUpdate) && m1=="add2" && m2=="square"||
		is(T==UnionFind!("min",true)) && m1=="unite" && m2=="unite"||
		is(T==UnionFind!("deterministic",true)) && m1=="unite" && m2=="unite"||
		is(T==ArrayList!int) && m1=="lastIndexOf" && m2=="set"];
	enum tooLargeForGreedy = [
		false,
		false];
	version(VERBOSE) writeln("greedy w/o");
	stats.greedy[0]=obtainTimedSpec!({
		auto bp=extractRelevantBasicPredicates!(incompat,true,true)(s).array;
		auto f=greedyEquivalentTo(s,bp);
		f=f.factorGreedily();
		return f;
	},tooLargeForGreedy[0])(searchTimeout);
	version(VERBOSE) writeln(stats.greedy[0].formula);
	version(VERBOSE) writeln("exhaustive w/o");
	stats.exhaustive[0]=obtainTimedSpec!({
		auto bp=extractRelevantBasicPredicates!(incompat,true,true)(s).array;
		auto f=minimalEquivalentTo(s,bp);
		return f;
	},tooLargeForExhaustive[0])(searchTimeout);
	version(VERBOSE) writeln(stats.exhaustive[0].formula);
	version(VERBOSE) writeln("greedy w/");
	stats.greedy[1]=obtainTimedSpec!({
		auto bp=extractRelevantBasicPredicates!(incompat,true)(s).array;
		auto f=greedyEquivalentTo(s,bp);
		f=f.factorGreedily();
		return f;
	},tooLargeForGreedy[1])(searchTimeout);
	version(VERBOSE) writeln(stats.greedy[1].formula);
	version(VERBOSE) writeln("exhaustive w/");
	stats.exhaustive[1]=obtainTimedSpec!({
		auto bp=extractRelevantBasicPredicates!(incompat,true)(s).array;
		auto f=minimalEquivalentTo(s,bp);
		return f;
	},tooLargeForExhaustive[1])(searchTimeout);
	version(VERBOSE) writeln(stats.exhaustive[1].formula);
	version(VERBOSE) writeln("done");
	// if(!f) f=s.getFormula();
	return stats;
}

struct Spec{
	string dataType;
	string m1,m2;
	SpecStats stats;
}

Spec[] specs;

struct TimedSpecSummary{
	int total;
	int number;
	TickDuration time;

	void add(TimedSpec r){
		total++;
		if(r.timedOut) return;
		number++;
		time+=r.time;
	}

	void add(TimedSpecSummary r){
		total+=r.total;
		number+=r.number;
		time+=r.time;
	}

	void addTo(ref TickDuration td){
		td+=time;
	}
	void divBy(int x){
		assert(!(total%x));
		assert(!(number%x));
		total/=x;
		number/=x;
		time/=x;
	}
}


struct SpecSummary{
	int numStats;
	int numSamples;
	int numClasses;
	int totNumClasses;
	TickDuration exploration;
	TimedSpecSummary greedy[2];
	TimedSpecSummary exhaustive[2];
	void add(SpecStats r){
		numStats++;
		numSamples+=r.numSamples;
		numClasses+=r.numClasses;
		totNumClasses+=r.totNumClasses;
		exploration+=r.exploration;
		foreach(i;0..2){
			greedy[i].add(r.greedy[i]);
			exhaustive[i].add(r.exhaustive[i]);
		}
	}
	void add(SpecSummary r){
		numStats+=r.numStats;
		numSamples+=r.numSamples;
		numClasses+=r.numClasses;
		totNumClasses+=r.totNumClasses;
		exploration+=r.exploration;
		foreach(i;0..2){
			greedy[i].add(r.greedy[i]);
			exhaustive[i].add(r.exhaustive[i]);
		}
	}
	void addTo(ref TickDuration td){
		td+=exploration;
		foreach(i;0..2){
			greedy[i].addTo(td);
			exhaustive[i].addTo(td);
		}		
	}
	void divBy(int x){
		assert(!(numStats%x));
		numStats/=x;
		numSamples/=x;
		numClasses/=x;
		assert(!(totNumClasses%x));
		totNumClasses/=x;
		exploration/=x;
		foreach(i;0..2){
			greedy[i].divBy(x);
			exhaustive[i].divBy(x);
		}
	}
}

/+ // TODO:
void saveSpecs(Spec[] specs,string filename){
	import std.stdio;
	auto f=File("filename","w");
	f.writeln(specs);
}

Spec[] loadSpecs(string filename){
	return parseSpecs(readText(filename));
}+/

void measureSpecs(T,alias inferenceMethod=inferTimedOccamSpec)(int numSamples=5000){
	version(VERBOSE) writeln(T.stringof);
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
					version(VERBOSE){
						write("φ(",m[i],"(",t1.join(","),")/r₁, ",m[j],"(",t2.join(","),")/r₂): ");
						stdout.flush();
					}
					auto stats=inferenceMethod!(T,m[i],m[j])(numSamples);
					//writeln("φ(",m[i],"(",t1.join(","),")/r₁, ",m[j],"(",t2.join(","),")/r₂): ",stats);
					version(VERBOSE) writeln(stats);
					specs~=Spec(T.stringof,m[i],m[j],stats);
				}
			}
		}
	}
}

string prettyDataType(string dataType){
	switch(dataType){
	case "Set!int": return "Set";
	case "Map!(int, int)": return "Map";
	case "MultiSet!int": return "MultiSet";
	case "MaxRegister!int": return "MaxRegister";
	/+case `UnionFind!("default", false)`: return "UnionFind (def.)";
	case `UnionFind!("min", false)`: return "UnionFind (min.)";
	case `UnionFind!("deterministic", false)`: return "UnionFind (det.)";
	case `UnionFind!("default", true)`: return "UnionFind (def., u.r.s.)";
	case `UnionFind!("min", true)`: return "UnionFind (min., u.r.s)";
	case `UnionFind!("deterministic", true)`: return "UnionFind (det., u.r.s)";+/
case `UnionFind!("default", false)`: return "UnionFind 1";
	case `UnionFind!("min", false)`: return "UnionFind 2";
	case `UnionFind!("deterministic", false)`: return "UnionFind 3";
	case `UnionFind!("default", true)`: return "UnionFind 4";
	case `UnionFind!("min", true)`: return "UnionFind 5";
	case `UnionFind!("deterministic", true)`: return "UnionFind 6";
	case `ArrayList!int`: return "ArrayList";
	case `KDTree!int`: return "1DTree";
	default: return dataType;
	}
}


// version=NOSIGFIG;
double sigFig(double d, int fig){
	version(NOSIGFIG) return d;
	else{
		import std.math;
		double scale=10.0^^(cast(int)(log10(abs(d)))+1-fig);
		return scale*round(d/scale);
	}
}

string escape(string s){
	return s.replace("_",`\_`);
}

string[2] createTables(Spec[] specs){
	string t,s;
	t~=`\begin{tabular}{|l|l||l|l|l|l|l|l|l|}`~"\n";
	t~=`Type & Methods & \#Samples & \#Classes & Sampling & \multicolumn{2}{|c|}{Exhaustive} & \multicolumn{2}{|c|}{Greedy} \\\hline`~"\n";

	s~=`\begin{tabular}{lrcrcrcrccrccrc}\toprule`~"\n";
	s~=`Type  & \#Samples & \#Classes & Sampling && \multicolumn{4}{c}{Exhaustive} && \multicolumn{4}{c}{Greedy} \\`~"\n";
	s~=`\cmidrule{6-9} \cmidrule{11-14}`~"\n";
	s~=`      &           &           &          && \multicolumn{2}{c}{w/o pred. discovery} & \multicolumn{2}{c}{w. pred. discovery} && \multicolumn{2}{c}{w/o pred. discovery} & \multicolumn{2}{c}{w. pred. discovery} \\\midrule`~"\n";
	string formatTime(TickDuration time){
		if(to!Duration(time)>=1.dur!"seconds") return text(time.to!("seconds",double).sigFig(2),"s");
		return text(time.to!("msecs",double).sigFig(2),"ms");
	}
	string formatTimedSpec(TimedSpec spec){
		if(spec.timedOut) return "T/O";
		return formatTime(spec.time);
	}
	struct SpecSummaryContainer{
		string[] names;
		SpecSummary[] summaries;
		bool opBinaryRight(string op)(string s)if(op=="in"){
			return summaries.length && names[$-1]==s;
		}
		ref SpecSummary opIndex(string s){
			if(!summaries.length||names[$-1]!=s){
				names~=s;
				summaries~=SpecSummary.init;
			}
			return summaries[$-1];
		}
	}
	SpecSummaryContainer summaries;
	foreach(spec;specs){
		t~=text(`\verb|`,prettyDataType(spec.dataType),`|`," & ",spec.m1.escape,"/",spec.m2.escape," & ",
				spec.stats.numSamples," & ",
				spec.stats.numClasses,"/",spec.stats.totNumClasses," & ",
				formatTime(spec.stats.exploration)," & ",
				formatTimedSpec(spec.stats.exhaustive[0])," & ",
				formatTimedSpec(spec.stats.exhaustive[1])," & ",
				formatTimedSpec(spec.stats.greedy[0])," & ",
				formatTimedSpec(spec.stats.greedy[1]));
		t~=`\\`~"\n";
		if(spec.dataType !in summaries) summaries[spec.dataType]=SpecSummary.init;
		summaries[spec.dataType].add(spec.stats);
	}
	foreach(i,name;summaries.names){
		auto spec=summaries.summaries[i];
		s~=text(`\verb|`,prettyDataType(name),`|`," & ",
				spec.numSamples," & ",
				spec.numClasses,"/",spec.totNumClasses," & ",
				formatTime(spec.exploration)," && ",
				formatTime(spec.exhaustive[0].time),spec.exhaustive[0].number<spec.exhaustive[0].total?"*":"",
				"& (",spec.exhaustive[0].number,"/",spec.exhaustive[0].total,") && ",
				formatTime(spec.exhaustive[1].time),spec.exhaustive[1].number<spec.exhaustive[1].total?"*":"",
				"& (",spec.exhaustive[1].number,"/",spec.exhaustive[1].total,") && ",
				formatTime(spec.greedy[0].time),spec.greedy[0].number<spec.greedy[0].total?"*":"",
				"& (",spec.greedy[0].number,"/",spec.greedy[0].total,") && ",
				formatTime(spec.greedy[1].time),spec.greedy[1].number<spec.greedy[1].total?"*":"",
				"& (",spec.greedy[1].number,"/",spec.greedy[1].total,")");
		s~=`\\`~"\n";
	}
	t~=`\end{tabular}`~"\n";
	s~=`\bottomrule`~"\n";
	s~=`\end{tabular}`~"\n";
	return [t,s];
}

string createAverageTable(Spec[][] allSpecs){
	string s;
	s~=`     {\small\begin{tabular}{lrcrcrcrccrcrc}\toprule`~"\n";
	s~=`         {\bf Data structure} & {\bf \#Samples} & {\bf \#Types} & {\bf Samp.} & {\bf Pairs} & \multicolumn{4}{c}{{\bf Exhaustive}}      &                                          & \multicolumn{4}{c}{{\bf Greedy}}                                                            \\`~"\n";
	s~=`         \cmidrule{6-9} \cmidrule{11-14}`~"\n";
	s~=`                              &                 &               & \multicolumn{1}{c}{{\bf time}} &             & \multicolumn{2}{c}{{\bf w/o pred. disc.}} & \multicolumn{2}{c}{{\bf w. pred. disc.}} &      & \multicolumn{2}{c}{{\bf w/o pred. disc.}} & \multicolumn{2}{c}{{\bf w. pred. disc.}} \\`~"\n";
	s~=`         \midrule`~"\n";
	string formatTime(TickDuration time){
		if(to!Duration(time)>=1.dur!"seconds") return text(time.to!("seconds",double).sigFig(2),"s");
		return text(time.to!("msecs",double).sigFig(2)/+,"ms"+/);
	}
	string formatTimedSpec(TimedSpec spec){
		if(spec.timedOut) return "T/O";
		return formatTime(spec.time);
	}
	string thousandSeparate(int x){
		if((x<0?-x:x)>=1000) return thousandSeparate(x/1000)~" "~to!string(x%1000);
		return to!string(x);
	}
	struct SpecSummaryContainer{
		string[] names;
		SpecSummary[] summaries;
		bool opBinaryRight(string op)(string s)if(op=="in"){
			return summaries.length && names[$-1]==s;
		}
		ref SpecSummary opIndex(string s){
			if(!summaries.length||names[$-1]!=s){
				names~=s;
				summaries~=SpecSummary.init;
			}
			return summaries[$-1];
		}
	}
	auto summaries=new SpecSummaryContainer[](allSpecs.length);
	foreach(i,specs;allSpecs){
		foreach(spec;specs){
			if(spec.dataType !in summaries[i]) summaries[i][spec.dataType]=SpecSummary.init;
			summaries[i][spec.dataType].add(spec.stats);
		}
	}
	auto totalTime=new TickDuration[](allSpecs.length);
	foreach(i,name;summaries[0].names){
		SpecSummary spec;
		foreach(k;0..summaries.length){
			spec.add(summaries[k].summaries[i]);
			summaries[k].summaries[i].addTo(totalTime[k]);
		}
		spec.divBy(cast(int)summaries.length);
		s~=text(`\verb|`,prettyDataType(name),`|`," & ",
				thousandSeparate(spec.numSamples)," & ",
				spec.numClasses,"/",spec.totNumClasses," & ",
				formatTime(spec.exploration)," & ",
				spec.numStats," & ",
				formatTime(spec.exhaustive[0].time),spec.exhaustive[0].number<spec.exhaustive[0].total?"*":"",
				" & ",spec.exhaustive[0].number," & ",
				formatTime(spec.exhaustive[1].time),spec.exhaustive[1].number<spec.exhaustive[1].total?"*":"",
				" & ",spec.exhaustive[1].number," && ",
				formatTime(spec.greedy[0].time),spec.greedy[0].number<spec.greedy[0].total?"*":"",
				" & ",spec.greedy[0].number," & ",
				formatTime(spec.greedy[1].time),spec.greedy[1].number<spec.greedy[1].total?"*":"",
				" & ",spec.greedy[1].number);
		s~=`\\`~"\n";
		if(i==4) s~="\\midrule\n";
	}
	s~=`\bottomrule`~"\n";
	s~=`\end{tabular}`~"\n";
	TickDuration average=0;
	foreach(i;0..allSpecs.length)
		average+=totalTime[i];
	average/=allSpecs.length;
	s~=text("average total time: ",average.to!("msecs",double),"ms")~"\n";
	double variance=0;
	foreach(i;0..allSpecs.length){
		variance+=(totalTime[i].to!("msecs",double)-average.to!("msecs",double))^^2;
	}
	variance/=allSpecs.length-1;
	s~=text("variance of total time: ",variance,"ms^2")~"\n";
	import std.math;
	s~=text("std.dev. of total time: ",sqrt(variance),"ms")~"\n";
	return s;
}

void runExperiments()(){
	import std.stdio;
	//writeln(runWithTimeout!({ writeln("finished"); return 0; })(1));
	//Thread.sleep(5.dur!"seconds");	
	// measureSpecs!(UnionFind!("default",true)); // TODO: debug this!
	Spec[][] allSpecs;
	foreach(i;0..12){
		specs=[];
		measureSpecs!(Set!int);
		measureSpecs!(Map!(int,int));
		measureSpecs!(MaxRegister!int);
		measureSpecs!RangeUpdate;
		measureSpecs!(KDTree!int); // "1DTree"
		// not captured precisely in the fragment
		enum many=30000;
		enum more=50000;
		measureSpecs!Accumulator;
		measureSpecs!(MultiSet!int);
		measureSpecs!(UnionFind!("default",false))(many);
		measureSpecs!(UnionFind!("min",false))(many);
		measureSpecs!(UnionFind!("deterministic",false))(more);
		measureSpecs!(UnionFind!"default")(many);
		measureSpecs!(UnionFind!"min")(more);
		measureSpecs!(UnionFind!"deterministic")(more);
		measureSpecs!(ArrayList!int)(600000);
		auto tables=createTables(specs);
		writeln("run ",i,":");
		writeln("detailed:");
		writeln(tables[0]);
		writeln("summarized:");
		writeln(tables[1]);
		writeln("specs ",i);
		allSpecs~=specs;
		//writeln(inferTimedOccamSpec!(ArrayList!int,"indexOf","set")(600000));
	}
	writeln("average:");
	writeln(createAverageTable(allSpecs));
}

version=VERBOSE;
