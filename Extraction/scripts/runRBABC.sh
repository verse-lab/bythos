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
duration=45     # how many seconds each node will run for

port1="9000"
port2="9001"
port3="9002"
port4="9003"

info="leader=127.0.0.1@$port2,round=3"  # ABC will be run after concluding the leader's RB round 3
info2="$info,value1=1111,value2=9999"

if [ $# -eq 0 ] || [ $scenario == "0" ]; then
    # normal case
    # the combination of the normal case in scripts/runRB.sh and scripts/runABC.sh
    (./main.exe -protocol RBABC -use_PKI -extrainfo $info -me 127.0.0.1 $port1 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 0.log
    (./main.exe -protocol RBABC -use_PKI -extrainfo $info -me 127.0.0.1 $port2 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 1.log
    (./main.exe -protocol RBABC -use_PKI -extrainfo $info -me 127.0.0.1 $port3 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 2.log
    (./main.exe -protocol RBABC -use_PKI -extrainfo $info -me 127.0.0.1 $port4 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 3.log
elif [ $scenario == "1" ]; then
    # there are two non-faulty nodes and two active Byzantine nodes
    # the Byzantine nodes will vote for two different values, and their votes will be sent to a subset of all nodes
    # this will make two non-faulty nodes output different values in RB, and find the culprits using ABC
    (./main.exe -protocol RBABC -use_PKI -extrainfo $info2,conspirator=127.0.0.1@$port3 -mode 2 -me 127.0.0.1 $port1 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 0.log
    (./main.exe -protocol RBABC -use_PKI -extrainfo $info -me 127.0.0.1 $port2 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 1.log
    (./main.exe -protocol RBABC -use_PKI -extrainfo $info2,conspirator=127.0.0.1@$port1 -mode 2 -me 127.0.0.1 $port3 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 2.log
    (./main.exe -protocol RBABC -use_PKI -extrainfo $info -me 127.0.0.1 $port4 -cluster 127.0.0.1 $port1 127.0.0.1 $port2 127.0.0.1 $port3 127.0.0.1 $port4 &) >& 3.log
else
    echo "Error: invalid argument. "
    exit 1
fi

sleep $duration
pkill "main.exe"
