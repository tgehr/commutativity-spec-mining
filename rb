#!/bin/bash
SUFFIX=$RANDOM$RANDOM$RANDOM
dmd -g -O -inline mining.d formula.d hashtable.d mine.d occam.d datatypes.d annotations.d util.d experiments.d -of./bin/mining$SUFFIX$1 && ulimit -c unlimited && time ./bin/mining$SUFFIX$1
