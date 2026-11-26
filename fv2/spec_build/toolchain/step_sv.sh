#!/bin/bash
set -x
source /home/scratch/fortress/kunyanliu/e2e_tools/opam_env.sh
eval $(opam env --switch=sail --set-switch)
export PATH=$PATH:/home/kunyanliu/riscdev/cheriot_tools/sail_tool_0.20.2/sail/bin
export LOWRISC_CHERIOT_SAIL_SRC=$T/src/cheriot-sail LOWRISC_SAIL_SRC=$T/src/sail SAIL_DIR=$T/src/sail
cd $T/ibex_formal
which sail z3 psgen python3
z3 --version
/usr/bin/time -v make sv SAIL=$(which sail)
echo "SV_RC=$?"
make psgen
echo "PSGEN_RC=$?"
ls -la build
