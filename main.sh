#!/bin/sh

cd src || exit 1
rm -f main

time idris --V1 --warnreach -p contrib Main.idr -o main || exit 1

echo
time ./main
