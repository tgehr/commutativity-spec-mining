# Learning Commutativity Specifications

The enclosed tool can be used to learn commutativity specifications for data structures and to reproduce the reported results for the paper 'Learning Commutativity Specifications' published at CAV 2015.

The tool is written in the D programming language. Metaprogramming is used to automate most of the steps necessary for learning the commutativity specifications.

In addition to the code evaluated as a CAV 2015 artifact, this code base contains experimental code for learning existentially or universally quantified commutativity specifications.

## Build Instructions

### GNU/Linux

#### Quick build

1. Run 'dependencies-release.sh' to download the LDC D compiler and unzip it.

2. Run 'build-release.sh' to build the tool.

```
$ ./dependencies-release.sh && ./build-release.sh
```

##### Additional information

The tool is written in the D programming language. D compilers are available at http://dlang.org/download.html.

./build.sh will use DMD inside the current directory if it exists, otherwise it will attempt to use DMD from your path.

./build.sh creates a debug build.
./build-release creates a release build.

### Other platforms

The build instructions given here are for GNU/Linux. This tool also works on other platforms.

## Reproducing the results

The following commands can be run to reproduce the reported results:
```
$ ./mine specifications # Learn and print all specifications reported in Appendix D
```
```
$ ./mine experiments # Obtain raw data for Fig. 4
```
Note that the "P.d." column of the table was added manually by running the tool with changed options (see next section).
```
$ ./mine diagram # Run an experiment like the one depicted in Fig. 5
```
Note that the data series marked with (*) were obtained by setting the option `enableTypeAwareSampling=false`.

## Changing options

In order to change the learning options, it is currently necessary to edit the file `mine.d`.
Sample size reduction, type aware sampling and predicate discovery can be enabled/disabled independently via boolean flags. The int sampling range gives the inclusive range from which to sample integers during randomized state space exploration.

For example, the following settings were used to obtain the reported results:

```d
// default settings:
enum bool enableSampleSizeReduction=true;
enum bool enableTypeAwareSampling=true;
enum bool enablePredicateDiscovery=true;
enum int[2] intSamplingRange=[-24,24];
```
```d
// no predicate discovery:
enum bool enableSampleSizeReduction=true;
enum bool enableTypeAwareSampling=true;
enum bool enablePredicateDiscovery=false;
enum int[2] intSamplingRange=[-24,24];
```
```d
// no type-aware sampling:
enum bool enableSampleSizeReduction=true;
enum bool enableTypeAwareSampling=false;
enum bool enablePredicateDiscovery=true;
enum int[2] intSamplingRange=[-24,24];
```

Re-run `./build-release.sh` after changing the options.


## Using the tool on your own data structures

For running your own experiments, it is advisable to set the flag `enableDefaultExperiments` in `mine.d` to false. Doing so will disable the specifications/experiments/diagram options in order to improve the running time of `./build.sh` down to a couple of seconds.


### Provided data structures

The data structures we used for testing are all implemented in `datatypes.d` and can be used for reference.


### Implementing your own data structure

You should implement your data structure as a D `struct`, for example within `mine.d`.
Learning can be invoked from within the `run()` method in that same file.

The file already contains an `ExampleDataType` to illustrate the required steps. The procedure `run()` shows how to invoke the learning of commutativity specifications for this data structure.

Notes:

1. Exploration starts from the data structure's initial state, where all of its fields are set to suitable default values (the default values can be modified for value type fields by providing initializers for the field declarations).

2. The exploration needs to be able to clone an instance of the data structure via a provided `clone()` method.

3. Data type instances are compared for equality using the built-in `==` operator, which can be overridden by implementing the `opEquals` method.

4. Annotations can be used to improve the argument sampling strategy.

In order to invoke the 'run()' method, run `./mine` without additional options.
