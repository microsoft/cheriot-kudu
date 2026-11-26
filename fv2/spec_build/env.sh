# Environment for building the kudu FV spec (sources Sail 0.17.1 lowRISC fork with SV backend)
export T=/home/scratch/fortress/kunyanliu/e2e_tools
export F=$T/upstream_spec
source $T/opam_env.sh
eval $(opam env --switch=sail --set-switch)
export PATH=$PATH:/home/kunyanliu/riscdev/cheriot_tools/sail_tool_0.20.2/sail/bin
export LOWRISC_CHERIOT_SAIL_SRC=$F/cheriot-sail LOWRISC_SAIL_SRC=$T/src/sail SAIL_DIR=$T/src/sail
