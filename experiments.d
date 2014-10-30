
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
	TickDuration relevantPredicates;
	TimedSpec greedy;
	TimedSpec exhaustive;
	TimedSpec random;
}

enum searchTimeout=5;

auto obtainTimedSpec(alias dg)(int searchTimeout){
	TimedSpec spec;
	try spec=runWithTimeout!({
			TimedSpec spec;
			auto sw=StopWatch(AutoStart.yes);
			spec.formula=dg();
			spec.time=sw.peek();
			return spec;
		})(searchTimeout);
	catch{spec.timedOut=true;}
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
	SpecStats stats;
	ResultStore s;
	int actualNumSamples=0;
	void addOccamResult(Assignment a,bool c){
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
	sw.reset();
	auto bp=extractRelevantBasicPredicates!(incompat,true)(s).array;
	stats.relevantPredicates=sw.peek();
	version(VERY_VERBOSE) writeln(bp,"\n",s);
	//writeln(bp.length," ",bp);
	stats.greedy=obtainTimedSpec!({
		auto f=greedyEquivalentTo(s,bp);
		f=f.factorGreedily();
		return f;
	})(searchTimeout);
	stats.exhaustive=obtainTimedSpec!({
		auto f=minimalEquivalentTo(s,bp);
		return f;
	})(searchTimeout);
	stats.random=obtainTimedSpec!({
		auto f=monteCarloMarkovChainEquivalentTo(s,bp);
		return f;
	})(searchTimeout);
	// if(!f) f=s.getFormula();
	return stats;
}

struct Spec{
	string dataType;
	string m1,m2;
	SpecStats stats;
}

Spec[] specs;

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
					auto stats=inferenceMethod!(T,m[i],m[j])(numSamples);
					//writeln("φ(",m[i],"(",t1.join(","),")/r₁, ",m[j],"(",t2.join(","),")/r₂): ",stats);
					writeln(stats);
					if(stats.greedy.formula!is tt &&
					   stats.greedy.formula!is ff)
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
	case `UnionFind!("default", false)`: return "UnionFind (def.)";
	case `UnionFind!("min", false)`: return "UnionFind (min.)";
	case `UnionFind!("deterministic", false)`: return "UnionFind (det.)";
	case `UnionFind!("default", true)`: return "UnionFind (def., u.r.s.)";
	case `UnionFind!("min", true)`: return "UnionFind (min., u.r.s)";
	case `UnionFind!("deterministic", true)`: return "UnionFind (det., u.r.s)";
	case `ArrayList!int`: return "ArrayList";
	default: return dataType;
	}
}


double sigFig(double d, int fig){
	import std.math;
	double scale=10.0^^(cast(int)(log10(abs(d)))+1-fig);
	return scale*round(d/scale);
}

string createDetailedTable(Spec[] specs){
	string t;
	t~=`\begin{tabular}{|l|l||l|l|l|l|l|l|}`~"\n";
	t~=`Type & Methods & \#Samples & \#Classes & Sampling & Greedy & Exhaustive & Random \\\hline`~"\n";
	string formatTime(TickDuration time){
		if(to!Duration(time)>=1.dur!"seconds") return text(time.to!("seconds",double).sigFig(2),"s");
		return text(time.to!("msecs",double).sigFig(2),"ms");
	}
	string formatTimedSpec(TimedSpec spec){
		if(spec.timedOut) return "T/O";
		return formatTime(spec.time);
	}
	foreach(spec;specs){
		t~=text(`\verb|`,prettyDataType(spec.dataType),`|`," & ",spec.m1,"/",spec.m2," & ",
				spec.stats.numSamples," & ",
				spec.stats.numClasses,"/",spec.stats.totNumClasses," & ",
				formatTime(spec.stats.exploration)," & ",
				formatTimedSpec(spec.stats.greedy)," & ",
				formatTimedSpec(spec.stats.exhaustive)," & ",
				formatTimedSpec(spec.stats.random));
		t~=`\\`~"\n";
	}
	t~=`\end{tabular}`~"\n";
	return t;
}
void runExperiments(){
	import std.stdio;
	//writeln(runWithTimeout!({ writeln("finished"); return 0; })(1));
	//Thread.sleep(5.dur!"seconds");
	measureSpecs!(Set!int);
	measureSpecs!(Map!(int,int));
	measureSpecs!(MultiSet!int);
	measureSpecs!(MaxRegister!int);
	measureSpecs!RangeUpdate;
	measureSpecs!(KDTree!int); // "1DTree"
	// not captured precisely in the fragment
	enum many=30000;
	enum more=50000;
	measureSpecs!Accumulator;
	measureSpecs!(UnionFind!("default",false))(many);
	measureSpecs!(UnionFind!("min",false))(many);
	measureSpecs!(UnionFind!("deterministic",false))(many);
	measureSpecs!(UnionFind!"default")(many);
	measureSpecs!(UnionFind!"min")(many);
	measureSpecs!(UnionFind!"deterministic")(many);
	measureSpecs!(ArrayList!int)(400000);
	writeln(createDetailedTable(specs));
}

import core.thread, core.sys.posix.pthread, core.sys.posix.time,core.sys.linux.errno;
import std.c.stdlib, std.c.string;

auto runWithTimeout(alias a)(int seconds){
	typeof(a()) result;
	timespec max_wait;
	
	memset(&max_wait, 0, max_wait.sizeof);
	max_wait.tv_sec = seconds;
	if(do_or_timeout({ result=a(); }, &max_wait))
		throw new TimeoutException();
	import core.memory;
	GC.collect();
	return result;
}

extern(C)
void* call_delegate(void *data){
	int oldtype;
	pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, &oldtype);
	auto action=*cast(void delegate()*)data;
	action();
	return null;
}
static extern(C) int pthread_timedjoin_np(pthread_t thread, void** retval, const timespec* abstime);
int do_or_timeout(void delegate() dg, timespec *max_wait){
	import core.memory;
	GC.disable();
	scope(exit) GC.enable();
	timespec abs_time;
	pthread_t tid;
	int err;
	clock_gettime(CLOCK_REALTIME, &abs_time);
	abs_time.tv_sec += max_wait.tv_sec;
	abs_time.tv_nsec += max_wait.tv_nsec;
	pthread_create(&tid, null, &call_delegate, &dg);
	err=pthread_timedjoin_np(tid,null,&abs_time);
	if(err==ETIMEDOUT) pthread_cancel(tid);
	return err;
}

class TimeoutException: Exception{
	this(string file=__FILE__,int line=__LINE__){super("timeout",file,line);}
}
