#!/bin/sh
cd ~/pin-3.7/source/tools/ManualExamples/
cp /media/sf_Pintool/proccount.cpp ./
make all TARGET=intel64
cd
~/pin-3.7/pin -t ~/pin-3.7/source/tools/ManualExamples/obj-intel64/proccount.so -- ~/a.out
