# Building Instructions

You can choose to build this project using Docker or from source. The following two subsections respectively describe the steps for compilation using the two ways. The last subsection describes how to quickly check if the compilation was successful. 

## Using Docker

You can use the provided `Dockerfile` to build a Docker image with all required software and packages pre-installed and all files pre-compiled. The Docker image uses the `amd64` architecture. 

To build the Docker image, in the toplevel directory of the artefact, run

```bash
docker build -t bythos .
```

This process might take up to 10 minutes on a commodity laptop. It might take around **8GB RAM** to build. 

Once the image has been built, you can launch a container using the image:

```bash
docker run --rm -it bythos bash
```

## From Source

### Prerequisites

The version of Coq used in our development is **8.19.0**, where the version of underlying OCaml compiler is **4.14.1**. We recommend installing Coq and the required packages via OPAM. [The official page of OPAM](https://opam.ocaml.org/doc/Install.html) describes how to install and configure OPAM, and [the official page of Coq](https://coq.inria.fr/opam-using.html) describes how to install Coq and Coq packages with OPAM. 

**Note:** We have not tested whether other versions of Coq or OCaml would also work. 

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

This process might take up to 5 minutes on a commodity laptop. It might take around **2GB RAM** to build. 

**Note:** You can also use `make -j X` (*e.g.,* `make -j 4`) to build using more threads with shorter time (and, with more RAM consumption, though). 

**Note:** There might be warnings like `New coercion path [Is_true] : bool >-> Sortclass is ambiguous with existing [is_true] : bool >-> Sortclass. [ambiguous-paths,coercions,default]` or `ld: warning: -undefined suppress is deprecated` during the building process. Ignoring them should be fine. 

## Check Whether the Compilation is Successful

If you did not encounter any error while executing the above steps, you have successfully compiled all the Coq files. 
