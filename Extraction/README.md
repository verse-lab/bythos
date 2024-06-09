# Extraction

Users can extract and run protocols. 

## Requirements

- Coq 8.19.0 
- dune 3.6 (for compiling extracted protocol implementations)

## Organization

Files in this directory: 
- `main.ml`: Entry point of the executable
- `Driver.v`: Coq code for extracting protocol implementations

The directories: 
- `config/`: Configurations, including references to command-line inputs and some definitions
- `companion/`: Companion files (explained below)
- `extracted/`: Extracted protocol implementations
- `shim/`: Code for the shim layer, including specifications for parsing the command-line input and network-related operations for communicating with other nodes
- `scripts/`: Shell scripts for running protocols

## Workflow

To make a protocol executable, a user need to: 
1. Extract the protocol implementation (typically a functor of the `Protocol` module type) into OCaml code. This can be done by modifying the `Driver.v`. 
   
   **Note:** Each protocol implementation is supposed to be extracted into a single `.ml` file. There can be many overlapping definitions across different protocols (e.g., the same module type `Round` may appear in different protocols), but this should not be very troublesome if the protocols are only executed in a small scale (rather than in production). 

2. Write a *companion file* in OCaml to instantiate the implementation with concrete module arguments and control how the node executes. See `companion/RB.ml` for an example. 
3. Build the project (here, by using `dune build`) to obtain an executable node program. The `promote` mode is set to be on, so the executable will be automatically copied to this directory after building, and can be deleted using `dune clean`. 

## Running the Protocol

See `scripts/runRB.sh` for an example. Use `pkill "main.exe"` to terminate all nodes. 
