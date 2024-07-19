# Extraction

Users can extract and run protocols. 

**WARNING:** Extracted protocol implementations can only serve as simple reference implementations. Their performance and security are far from being suitable for production-level applications. 

## Requirements

Apart from Coq:
- `dune` >= 3.6 (for compiling extracted protocol implementations)
- `mirage-crypto`, `mirage-crypto-rng`, `mirage-crypto-pk` (all version 1.0.0)

## Organization

Files in this directory: 
- `main.ml`: Entry point of the executable
- `Driver.v`: Coq code for extracting protocol implementations

The subdirectories: 
- `config/`: Configurations, including references to command-line inputs and some definitions
- `companion/`: *Companion files* (explained below)
- `extracted/`: Extracted protocol implementations (in OCaml)
- `shim/`: Code for the shim layer, including specifications for parsing the command-line input and network-related operations for communicating with other nodes
- `scripts/`: Shell scripts for running protocols

## Workflow

To make a protocol executable, a user need to: 
1. Extract the protocol implementation (typically a functor of the `Protocol` module type) into OCaml code. This can be done by modifying the `Driver.v`. Both single file extraction (*i.e.,* extracting the protocol implementation into one `.ml` file) and separate extraction should work. 
2. Write a *companion file* in OCaml to instantiate the implementation with concrete module arguments and control how the node executes. See `companion/RB.ml` for an example. 
3. Modify the `main_loop` function in `main.ml` to register the companion file written in the last step. 
4. Build the project (here, by using `dune build`) to obtain an executable node program `main.exe`. The `promote` mode is set to be on, so the executable will be automatically copied to this directory after building, and can be deleted using `dune clean`. 

## Running the Protocol

Users can run multiple instances of `main.exe` on a single machine to test the protocol execution. This can be achieved by writing a bash script. See `scripts/runRB.sh` for an example. 

The sample scripts use `pkill "main.exe"` to terminate all nodes after a certain time period. 

**Tip:** Run `./main.exe -help` to check the usage of `main.exe`. 

**Note:** Before executing a script for a specific protocol, the user needs to make sure that the `-protocol` argument is set properly, and this specific protocol has been registered in the `main_loop` function in `main.ml`. 

## Acknowledgement

- All definitions in `shim/Net.ml` and some definitions in `main.ml` are taken from [Toychain](https://github.com/verse-lab/toychain) and/or [DiSeL](https://github.com/DistributedComponents/disel/). 
- The adoption of `mirage-crypto` is inspired by [Velisarios](https://github.com/vrahli/Velisarios/), which uses `nocrypto`, the predecessor of `mirage-crypto`. The usage of `mirage-crypto` in code is inspired by [a testing file of `Mirage_crypto_pk.Dsa`](https://github.com/mirage/mirage-crypto/blob/main/tests/test_dsa.ml). 
