#!/bin/bash
dmd -g -O -J. -inline *.d -ofmining && ulimit -c unlimited && time ./mine

