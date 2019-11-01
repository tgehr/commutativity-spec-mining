// (for standard experiments, all options should be set to "true")
enum bool enableSampleSizeReduction=true;
enum bool enableTypeAwareSampling=true;
enum bool enablePredicateDiscovery=true;
enum int[2] intSamplingRange=[-24,24];

enum bool manualOutputRedirect=false;

//import annotations, std.stdio; // work around DMD forward reference bug
import datatypes, std.stdio;

struct ExampleDataType{
	int val=3;
	int[] a;

	int read(){ return val; }
	void write(int x){ val = x; }

	void append(){ a ~= val; }

	@bounded!(`i`,`0`,`cast(int)a.length`)
	void set(int i){ a[i] = val; }

	@either!(`x`,useDefault!(`x`),sampleFrom!(`x`,`a`))
	bool contains(int x){
		foreach(y;a) if(x==y) return true;
		return false;
	}

	ExampleDataType clone(){
		return ExampleDataType(val,a.dup);
	}
	bool opEquals(ExampleDataType rhs){
		return val==rhs.val && a==rhs.a; // (if opEquals is not implemented, this is the default)
	}
}

// implement your custom data types here: //
// ...
///////////////////////////////////////////

enum bool enableDefaultExperiments = true; // set to false to improve compilation time if default experiments are not needed

int run(){
	import printing;
	// learn and print all commutativity specifications for ExampleDataType:
	printSpecs!ExampleDataType; 
	writeln();
	// learn and print a specification for one method pair:
	printSpec!(ExampleDataType,"read","write");
	writeln();
	// the number of samples can be specified manually. This disables adaptive sample size:
	writeln("using 300 samples:");
	printSpecs!ExampleDataType(300); 
	writeln();
	printSpec!(ExampleDataType,"read","write")(300);
	writeln();
	// import data types used for experiments:
	import datatypes; 
	// learn and print specifications for one provided data type:
	printSpecs!(RangeUpdate);

	// Add your custom experiments here: //
	// ...
	//////////////////////////////////////
	return 0;
}


int main(string[] args){
	if(args.length==1){
		return run();
	}else if(enableDefaultExperiments&&args.length==2){
		static if(enableDefaultExperiments){
			switch(args[1]){
				import printing, experiments;
			case "specifications":
				performMeasurements!printSpecs; // obtain all specifications (Appendix D)
				break;
			case "experiments":
				runExperiments();               // measure data for Fig. 4
				break;
			case "diagram":
				import datatypes;
				measureTypeDiagrams!(Map!(int,int));          // measure data used for the diagram
				break;
			default: 
				writeln("unknown option: '",args[1]);
				printUsage(args);
				return 1;
			}
		}
	}else{
		printUsage(args);
		return 1;
	}
	return 0;
}

void printUsage(string[] args){
	static if(enableDefaultExperiments) writeln("usage: ",args[0]," [specifications|experiments|diagram]?");
	else writeln("usage: ",args[0]);
}
