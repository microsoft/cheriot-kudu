#!/bin/bash
# Run the round-8 go.sh scripts given as arguments, at most 2 at a time, in order.
max=2; pids=()
for g in "$@"; do
  while :; do
    live=(); for p in "${pids[@]}"; do kill -0 $p 2>/dev/null && live+=($p); done; pids=("${live[@]}")
    [ ${#pids[@]} -lt $max ] && break; sleep 60
  done
  echo "$(date +%H:%M) launch $g"; bash $g & pids+=($!); sleep 120
done
wait; echo "$(date +%H:%M) all done"
