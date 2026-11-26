# Source this to use the CHERIoT-Ibex end-to-end formal toolchain (psgen + lowRISC Sail fork).
export T=/home/scratch/fortress/kunyanliu/e2e_tools
export OPAMROOT=$T/opam
export OPAMSWITCH=sail
export OPAM_SWITCH_PREFIX=$OPAMROOT/sail
export CAML_LD_LIBRARY_PATH=$OPAM_SWITCH_PREFIX/lib/stublibs:$OPAM_SWITCH_PREFIX/lib/ocaml/stublibs:$OPAM_SWITCH_PREFIX/lib/ocaml
export CARGO_HOME=$T/cargo RUSTUP_HOME=$T/rustup
export XDG_CACHE_HOME=$T/cache XDG_DATA_HOME=$T/share XDG_CONFIG_HOME=$T/config
export TMPDIR=$T/tmp PIP_CACHE_DIR=$T/cache/pip
export GOROOT=$T/go GOPATH=$T/gopath GOCACHE=$T/cache/go-build GOTOOLCHAIN=local
# sail fork (opam switch), psgen/opam ($T/bin), fusesoc venv ($T/py/bin), z3 (appended, z3 only)
export PATH=$OPAM_SWITCH_PREFIX/bin:$T/bin:$T/py/bin:$PATH:/home/kunyanliu/riscdev/cheriot_tools/sail_tool_0.20.2/sail/bin
export LOWRISC_SAIL_SRC=$T/src/sail
export LOWRISC_CHERIOT_SAIL_SRC=$T/src/cheriot-sail
export SAIL_DIR=$T/src/sail
# verify.tcl include dir: $LOWRISC_SAIL_SRC/lib/sv
# Formal working copy: $T/ibex_formal
#   make sv psgen ; make fusesoc IBEX_ROOT=/home/kunyanliu/riscdev/cheriot-ibex
