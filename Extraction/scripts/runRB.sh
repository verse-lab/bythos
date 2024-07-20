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
duration=60     # how many seconds each node will run for

if [ $# -eq 0 ] || [ $scenario == "0" ]; then
    # normal case
    # each node initiates a new round of Reliable Broadcast every 10 seconds, with the broadcast value being a random number
    (./main.exe -protocol RB -me 127.0.0.1 9000 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 0.log
    (./main.exe -protocol RB -me 127.0.0.1 9001 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 1.log
    (./main.exe -protocol RB -me 127.0.0.1 9002 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 2.log
    (./main.exe -protocol RB -me 127.0.0.1 9003 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 3.log
elif [ $scenario == "1" ]; then
    # like the normal case, but one node dies from the beginning
    (./main.exe -protocol RB -me 127.0.0.1 9000 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 0.log
    (./main.exe -protocol RB -me 127.0.0.1 9001 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 1.log
    (./main.exe -protocol RB -mode 1 -me 127.0.0.1 9002 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 2.log
    (./main.exe -protocol RB -me 127.0.0.1 9003 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 3.log
elif [ $scenario == "2" ]; then
    # like the normal case, but two node die from the beginning
    (./main.exe -protocol RB -me 127.0.0.1 9000 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 0.log
    (./main.exe -protocol RB -mode 1 -me 127.0.0.1 9001 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 1.log
    (./main.exe -protocol RB -mode 1 -me 127.0.0.1 9002 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 2.log
    (./main.exe -protocol RB -me 127.0.0.1 9003 -cluster 127.0.0.1 9000 127.0.0.1 9001 127.0.0.1 9002 127.0.0.1 9003 &) > 3.log
else
    echo "Error: invalid argument. "
    exit 1
fi

sleep $duration
pkill "main.exe"
