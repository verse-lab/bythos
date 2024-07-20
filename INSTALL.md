# Building Instructions

You can choose to build this project using Docker or from source. The following two subsections respectively describe the steps for compilation using the two ways. The last subsection describes how to quickly check if the compilation was successful. 

## Using Docker

You can use the provided `Dockerfile` to build a Docker image with all required software and packages pre-installed and all files pre-compiled. The Docker image uses the `amd64` architecture. 

To build the Docker image, in the toplevel directory of the artefact, run

```bash
docker build -t bythos .
```

This process might take up to 10 minutes on a commodity laptop. It might take up to **8GB RAM** to build. 

Once the image has been built, you can launch a container using the image:

```bash
docker run --rm -it bythos bash
```

## From Source

### Prerequisites

The version of Coq used in our development is **8.19.0**, where the version of underlying OCaml compiler is **4.14.1**. We recommend installing Coq and the required packages via OPAM. [The official page of OPAM](https://opam.ocaml.org/doc/Install.html) describes how to install and configure OPAM, and [the official page of Coq](https://coq.inria.fr/opam-using.html) describes how to install Coq and Coq packages with OPAM. 

**Note:** Using the OCaml compiler with version 4.13.1 also works, since the Docker-based installation provided above uses it. We have not tested whether other versions of Coq or OCaml compilers would also work. 

The Coq development in Bythos only depends on `coq-tla`, which is present in the project directory, so no additional Coq package is required. 

The shim layer (see [`Extraction/README.md`](Extraction/README.md) for details) depends on some OCaml packages, which can be installed with OPAM using the following command: 

```bash
opam install dune mirage-crypto=1.0.0 mirage-crypto-pk=1.0.0 mirage-crypto-rng=1.0.0
```

### Building

In the toplevel directory of the artefact, run `make`. The console output should look like: 

```
coq_makefile -f _CoqProject -o Makefile.coq (... many .v files)
(... some Warnings; just ignore them)
COQDEP VFILES
COQC Utils/Tactics.v
COQC Utils/ListFacts.v
COQC Utils/Misc.v
COQC Utils/Fintype.v
(...)
(compiling all .v files)
cd Extraction/; dune build; cd ..
(... possibly some Warnings; just ignore them)
```

This process might take up to 5 minutes on a commodity laptop. It might take up to **2GB RAM** to build. 

**Note:** You can also use `make -j X` (*e.g.,* `make -j 4`) to build using more threads with shorter time (and, with more RAM consumption, though). 

**Note:** There might be warnings like `New coercion path [Is_true] : bool >-> Sortclass is ambiguous with existing [is_true] : bool >-> Sortclass. [ambiguous-paths,coercions,default]` or `ld: warning: -undefined suppress is deprecated` during the building process. Ignoring them should be fine. 

## Check Whether the Compilation is Successful

If you did not encounter any error while executing the above steps, you have successfully compiled all the Coq files. 

To check if the OCaml files have been compiled successfully, `cd` into `Extraction/` and run `bash scripts/runPB.sh`. This will create 4 nodes running Provable Broadcast, redirecting their outputs to the files `0.log`, `1.log`, `2.log`, and `3.log` under `Extraction/` respectively. These nodes will run for 90 seconds and will stop when `scripts/runPB.sh` is completed. 

Wait for 90 seconds and check the logs. If you can see long outputs like the one shown below, then the compilation was successful! 

```
Me IP: 127.0.0.1
Me port: 9000
Cluster:
  127.0.0.1@9000
  127.0.0.1@9006
  127.0.0.1@9012
  127.0.0.1@9018
listening on port 9000
check before spontaneous procInt ... 
sending:
  Init ([1, 1], 510692390, [some light sig]) to 127.0.0.1@9000
  Init ([1, 1], 510692390, [some light sig]) to 127.0.0.1@9006
  Init ([1, 1], 510692390, [some light sig]) to 127.0.0.1@9012
  Init ([1, 1], 510692390, [some light sig]) to 127.0.0.1@9018
new connection!
done processing new connection from node 127.0.0.1@9000; received its public key
new connection!
done processing new connection from node 127.0.0.1@9006; received its public key
new connection!
done processing new connection from node 127.0.0.1@9012; received its public key
new connection!
done processing new connection from node 127.0.0.1@9018; received its public key
receiving Echo ([1, 1], [some light sig]) from 127.0.0.1@9006
receiving Echo ([1, 1], [some light sig]) from 127.0.0.1@9012
receiving Echo ([1, 1], [some light sig]) from 127.0.0.1@9018
sending:
  Init ([1, 2], 510692390, [some combined sig]) to 127.0.0.1@9000
  Init ([1, 2], 510692390, [some combined sig]) to 127.0.0.1@9006
  Init ([1, 2], 510692390, [some combined sig]) to 127.0.0.1@9012
  Init ([1, 2], 510692390, [some combined sig]) to 127.0.0.1@9018
receiving Init ([1, 1], 510692390, [some light sig]) from 127.0.0.1@9000
sending:
  Echo ([1, 1], [some light sig]) to 127.0.0.1@9000
receiving Init ([1, 2], 510692390, [some combined sig]) from 127.0.0.1@9000
sending:
  Echo ([1, 2], [some light sig]) to 127.0.0.1@9000
(...)  
check before spontaneous procInt ... found existing delivery certificate ... 
(...)
```
