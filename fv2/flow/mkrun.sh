#!/bin/bash
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Instantiate a JasperGold run directory from a flow template (README.md §8).
# usage: mkrun.sh <template.tcl> <rundir> [mem_GB=64] [timeout_min=1200]
# Writes <rundir>/run.tcl (@RUNDIR@ and @FV2@ substituted), empty.init (the
# free initial state of the stage-2 step runs) and go.sh, which submits the
# job to the interactive LSF queue. Run <rundir>/go.sh to start it; the
# results go to <rundir>/res.txt, jg.out and, for each cex, a .vcd.
set -euo pipefail
[ $# -ge 2 ] || { sed -n 6,11p "$0"; exit 1; }
FV2="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TPL="$(readlink -f "$1")"; D="$(readlink -m "$2")"; MEM=${3:-64}; TMO=${4:-1200}
T=${T:-/home/scratch/fortress/kunyanliu/e2e_tools}
JG=${JG:-/home/cad/tools/cadence/jasper/jasper_2024.03/bin/jg}
mkdir -p "$D"
sed -e "s#@RUNDIR@#$D#g" -e "s#@FV2@#$FV2#g" "$TPL" > "$D/run.tcl"
: > "$D/empty.init"
cat > "$D/go.sh" <<EOF
#!/bin/bash
source $T/env.sh
cd $FV2
submit -i -q interactive -m $MEM -t $TMO --resource=CORES/6 $JG -batch -fpv -allow_unsupported_OS -proj $D/jgproj $D/run.tcl > $D/jg.out 2>&1
EOF
chmod +x "$D/go.sh"
echo "$D/go.sh"
