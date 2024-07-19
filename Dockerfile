# adapted from https://gitlab.com/math-comp/docker-mathcomp/blob/master/mathcomp/single/Dockerfile
ARG coq_image="coqorg/coq:8.19-ocaml-4.13-flambda"
FROM ${coq_image} as bythos

WORKDIR /home/coq/bythos

COPY . .

SHELL ["/bin/bash", "--login", "-o", "pipefail", "-c"]

RUN set -x \
  && opam switch \
  && eval $(opam env) \
  && opam update -y \
  && opam config list && opam repo list && opam list && coqc --version \
  && sudo chown -R coq:coq /home/coq/bythos \
  && opam install -y -v dune mirage-crypto=1.0.0 mirage-crypto-pk=1.0.0 mirage-crypto-rng=1.0.0 \
  && opam clean -a -c -s --logs \
  && opam config list && opam list \
  && make

SHELL ["/bin/sh", "-c"]
