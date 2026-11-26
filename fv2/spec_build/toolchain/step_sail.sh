#!/bin/bash
set -ex
source /home/scratch/fortress/kunyanliu/e2e_tools/opam_env.sh
eval $(opam env --switch=sail --set-switch)
cd $T/src/sail
make sail
make install
which sail
sail --version
echo SAIL_DONE
