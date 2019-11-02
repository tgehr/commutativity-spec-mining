#!/bin/bash

if [[ "$OSTYPE" == "linux-gnu" ]]; then
    BIN="linux/bin64"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    BIN="osx/bin"
fi

if [[ -d "dmd2" ]]; then
    DMD="./dmd2/$BIN/dmd"
else
    DMD="dmd"
fi

# release build
$DMD -O -inline -J. *.d -ofmine


# VERSION="1.18.0"

# if [[ "$OSTYPE" == "linux-gnu" ]]; then
#     NAME="ldc2-$VERSION-linux-x86_64"
# elif [[ "$OSTYPE" == "darwin"* ]]; then
#     NAME="ldc2-$VERSION-osx-x86_64"
# fi

# if [ -d $NAME ]; then
#     LDMD="./$NAME/bin/ldmd2";
# else
#     LDMD="ldmd2"
# fi

# # release build
# $LDMD -O -inline -J. *.d -ofmine
