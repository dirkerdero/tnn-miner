#!/bin/bash

g++ ./src/astrobwtv3/divsufsort.c ./src/astrobwtv3/sssort.c ./src/astrobwtv3/trsort.c test-op.cpp -o asdf.exe -g -std=c++20 -I./include/ -I./src/ -I./src/astrobwtv3/ -flax-vector-conversions -L/lib/aarch64-linux-gnu/ -lssl -lcrypto 
if [[ "$?" == "0" ]]; then
  ./asdf.exe $1
    if [[ "$?" != "0" ]]; then
      gdb --batch -ex "run" -ex "bt" --args ./asdf.exe $1
    fi
else
  echo "Fail"
fi
