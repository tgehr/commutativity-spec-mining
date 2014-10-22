#!/bin/bash
dmd -g -O -inline mining.d formula.d hashtable.d mine.d occam.d datatypes.d annotations.d util.d && time ./mining
