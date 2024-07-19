#!/bin/bash

if [ $# -gt 1 ]; then
    echo "Error: at most one argument. "
    exit 1
fi

executable="main.exe"

if ! [ -x ./$executable ]
then
    echo "Error: $executable not found! Run 'dune build' first. "
    exit 1
fi

scenario=$1

port1="9000"
port2="9006"
port3="9012"
port4="9018"

if [ $# -eq 0 ] || [ $scenario == "0" ]; then
    # normal case
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port1 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 0.log
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port2 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 1.log
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port3 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 2.log
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port4 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 3.log
elif [ $scenario == "1" ]; then
    # one node dies
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port1 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 0.log
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port2 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 1.log
    (./main.exe -protocol PB -use_PKI -mode 1 -me 127.0.0.1 $port3 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 2.log
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port4 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 3.log
elif [ $scenario == "2" ]; then
    # two node die
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port1 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 0.log
    (./main.exe -protocol PB -use_PKI -mode 1 -me 127.0.0.1 $port2 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 1.log
    (./main.exe -protocol PB -use_PKI -mode 1 -me 127.0.0.1 $port3 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 2.log
    (./main.exe -protocol PB -use_PKI -me 127.0.0.1 $port4 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 3.log
else
    echo "Error: invalid argument. "
    exit 1
fi

sleep 90
pkill "main.exe"
