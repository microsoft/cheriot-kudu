#!/bin/bash
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# KUDU-069: run $REPO/sim/run/vcscomp with flag combinations against a fake
# `vcs` that only logs its command line, and check that every requested
# define reaches both vcs invocations (simv32 and simv). Runs in the current
# directory (the run directory); vcscomp is invoked from sim/run with
# -outdir=<here>/out_<case>, so nothing is written to the repository.
# Prints "FAIL vcscomp <case>: ..." per problem and "VCSCOMP FLAGS PASS" at
# the end when every case passed.

: "${REPO:?REPO not set}"
HERE=$(pwd -P)
RUNDIR=$(cd "$REPO/sim/run" && pwd -P)
FAKE=$HERE/fakebin
mkdir -p "$FAKE"
cat > "$FAKE/vcs" <<'EOS'
#!/bin/bash
{
  printf 'CALL'
  printf ' %s' "$@"
  printf '\n'
  printf 'ENV %s|%s|%s|%s\n' "$rtlRoot" "$verifRoot" "$dwRoot" "$(pwd -P)"
} >> "$FAKE_VCS_LOG"
exit 0
EOS
chmod +x "$FAKE/vcs"

fails=0
fail() {
  echo "FAIL vcscomp $1: $2"
  fails=$((fails + 1))
}

# check_case <name> "<vcscomp flags>" <file list> <expected argument>...
check_case() {
  local name=$1 flags=$2 flist=$3
  shift 3
  local out=$HERE/out_$name log=$HERE/vcs_$name.log
  : > "$log"
  # shellcheck disable=SC2086
  (cd "$RUNDIR" && FAKE_VCS_LOG=$log PATH=$FAKE:$PATH ./vcscomp $flags -outdir="$out") \
    > "$HERE/vcscomp_$name.out" 2>&1
  local rc=$?
  [ $rc -eq 0 ] || fail "$name" "vcscomp exited $rc"
  if grep -q "Unknown option" "$HERE/vcscomp_$name.out"; then
    fail "$name" "$(grep -m1 'Unknown option' "$HERE/vcscomp_$name.out")"
  fi
  local ncall
  ncall=$(grep -c '^CALL' "$log")
  if [ "$ncall" -ne 2 ]; then
    fail "$name" "expected 2 vcs calls, got $ncall"
    return
  fi
  local i=0 line exe d rtl='' verif='' dw='' cwd=''
  while IFS= read -r line; do
    case "$line" in
      CALL*)
        i=$((i + 1))
        if [ $i -eq 1 ]; then exe=simv32; else exe=simv; fi
        echo "vcscomp $name call $i:${line#CALL}"
        [[ " $line " == *" -o ./$exe "* ]] || fail "$name" "call $i does not build ./$exe"
        if [ $exe = simv ]; then
          [[ " $line " == *" +define+CHERIoT "* ]] || fail "$name" "simv call lacks +define+CHERIoT"
        else
          [[ " $line " != *" +define+CHERIoT "* ]] || fail "$name" "simv32 call has +define+CHERIoT"
        fi
        for d in "$@"; do
          [[ " $line " == *" $d "* ]] || fail "$name" "$exe call lacks $d (flags: $flags)"
        done
        [[ " $line " == *" -f $RUNDIR/$flist "* ]] || \
          fail "$name" "$exe call does not use file list $RUNDIR/$flist"
        ;;
      ENV*)
        IFS='|' read -r rtl verif dw cwd <<< "${line#ENV }"
        [ "$cwd" = "$out" ] || fail "$name" "vcs ran in $cwd, not in -outdir $out"
        ;;
    esac
  done < "$log"
  # every source in the selected file list must exist
  local f p missing=0
  while IFS= read -r f; do
    f=${f%%//*}
    f=${f//[[:space:]]/}
    case "$f" in ''|+*|-*) continue ;; esac
    p=${f//\$rtlRoot/$rtl}
    p=${p//\$verifRoot/$verif}
    p=${p//\$dwRoot/$dw}
    if [ ! -e "$p" ]; then
      fail "$name" "$flist entry $f -> $p does not exist"
      missing=1
    fi
  done < "$RUNDIR/$flist"
  [ $missing -eq 0 ] && echo "vcscomp $name: every $flist entry exists"
}

check_case nowave_trace "-nowave -trace_dpi" kudu.vcs.f \
  +define+KUDU_PPL_CFG=1 +define+TraceDPI +define+NO_FSDB
check_case trace_nowave "-trace_dpi -nowave" kudu.vcs.f \
  +define+KUDU_PPL_CFG=1 +define+TraceDPI +define+NO_FSDB
check_case dw_trace_nowave "-dw -trace_dpi -nowave" kudu_dw.vcs.f \
  +define+KUDU_DW_MULT=1 +define+TraceDPI +define+NO_FSDB
check_case dw_nowave "-dw -nowave" kudu_dw.vcs.f \
  +define+KUDU_DW_MULT=1 +define+NO_FSDB
check_case conf3_dii_trace_nowave "-conf3 -dii -trace_dpi -nowave" kudu.vcs.f \
  +define+KUDU_PPL_CFG=3 +define+DII_SIM +define+TraceDPI +define+NO_FSDB
check_case cov_dii_trace_nowave "-cov -dii -trace_dpi -nowave" kudu.vcs.f \
  +define+DII_SIM +define+TraceDPI +define+NO_FSDB \
  "-f $RUNDIR/../fcov/kudu_fcov.f" "-cm line+cond+tgl+fsm+branch+assert"

if [ $fails -eq 0 ]; then
  echo "VCSCOMP FLAGS PASS"
else
  echo "VCSCOMP FLAGS: $fails problem(s)"
fi
