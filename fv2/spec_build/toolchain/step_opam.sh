#!/bin/bash
set -ex
source /home/scratch/fortress/kunyanliu/e2e_tools/opam_env.sh
opam init --bare --disable-sandboxing -n
opam switch create sail ocaml-base-compiler.4.14.2
eval $(opam env --switch=sail --set-switch)
ocaml -version
cd $T/src/sail
opam install --deps-only ./
echo DEPS_DONE
