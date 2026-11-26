#!/usr/bin/env bash
# Regenerate the formal SV spec of the CHERIoT Sail model (kudu-fv port of
# CHERIoT-Platform/cheriot-sail dii-read-from-file) into $F/out/.
#
# Usage: ./build_spec.sh            (sources ./env.sh itself)
#
# Outputs (in $F/out/):
#   ibexspec.sv, sail_genlib_ibexspec.sv, extracted.sv  - the spec (module sail_ibexspec)
#   sail.log    - sail/post-processing output
#   time.log    - /usr/bin/time -v report (wall time, peak RSS)
#   VERSION     - source commits used
set -euo pipefail

F="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$F/env.sh"
export LOWRISC_CHERIOT_SAIL_SRC="$F/cheriot-sail"

mkdir -p "$F/out"
cd "$F/build"
rm -rf build

echo "sail: $(command -v sail) ($(sail -v 2>&1 | head -1))"
/usr/bin/time -v -o "$F/out/time.log" make sv LOWRISC_CHERIOT_SAIL_SRC="$LOWRISC_CHERIOT_SAIL_SRC" 2>&1 | tee "$F/out/sail.log"

cp build/ibexspec.sv build/sail_genlib_ibexspec.sv build/extracted.sv "$F/out/"
chmod a+r "$F/out/"*.sv
{
  echo "cheriot-sail: $(git -C "$F/cheriot-sail" rev-parse HEAD) ($(git -C "$F/cheriot-sail" rev-parse --abbrev-ref HEAD))"
  echo "sail-riscv:   $(git -C "$F/cheriot-sail/sail-riscv" rev-parse HEAD) ($(git -C "$F/cheriot-sail/sail-riscv" rev-parse --abbrev-ref HEAD))"
  echo "sail:         $(sail -v 2>&1 | head -1)"
  echo "dirty files:  $(git -C "$F/cheriot-sail" status --short --ignore-submodules=none | wc -l) top, $(git -C "$F/cheriot-sail/sail-riscv" status --short | wc -l) sail-riscv"
  echo "built:        $(date)"
} > "$F/out/VERSION"

grep -E "Elapsed \(wall clock\)|Maximum resident set size" "$F/out/time.log"
ls -l "$F/out/"
