#!/bin/bash
SUFFIX=$RANDOM$RANDOM$RANDOM
dmd -g -O -inline *.d -of./bin/mining$SUFFIX$1 && ulimit -c unlimited && time ./bin/mine$SUFFIX$1
