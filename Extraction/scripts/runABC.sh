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
duration=40     # how many seconds each node will run for

port1="9000"
port2="9001"
port3="9002"
port4="9003"

if [ $# -eq 0 ] || [ $scenario == "0" ]; then
    # normal case
    # every node submits the same value 9999 at a random time
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -me 127.0.0.1 $port1 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 0.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -me 127.0.0.1 $port2 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 1.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -me 127.0.0.1 $port3 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 2.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -me 127.0.0.1 $port4 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 3.log
elif [ $scenario == "1" ]; then
    # like the normal case, but one node dies from the beginning
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -me 127.0.0.1 $port1 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 0.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -me 127.0.0.1 $port2 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 1.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -mode 1 -me 127.0.0.1 $port3 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 2.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -me 127.0.0.1 $port4 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 3.log
elif [ $scenario == "2" ]; then
    # there are two non-faulty nodes and two active Byzantine nodes
    # one non-faulty node submits 1111, while the other submits 9999
    # the Byzantine nodes will submit both (and get caught eventually)
    (./main.exe -protocol ABC -use_PKI -extrainfo 1111 -me 127.0.0.1 $port1 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 0.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999.1111 -mode 2 -me 127.0.0.1 $port2 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 1.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 1111.9999 -mode 2 -me 127.0.0.1 $port3 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 2.log
    (./main.exe -protocol ABC -use_PKI -extrainfo 9999 -me 127.0.0.1 $port4 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 3.log
else
    echo "Error: invalid argument. "
    exit 1
fi

sleep $duration
pkill "main.exe"
