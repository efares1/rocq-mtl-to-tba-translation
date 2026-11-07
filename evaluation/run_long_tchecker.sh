#!/bin/bash
# Long TChecker runs for the configurations that are inconclusive at 600 s.
#
#   bash run_long_tchecker.sh            # LIMIT=3600 s per tool run and per check, 3 jobs in parallel
#
# One output file per configuration: long_<id>.tsv (same columns as
# compiled_bench.tsv); a timeout at the longer limit is recorded as such.
HERE="$(cd "$(dirname "$0")" && pwd)"
EXE=${EXE:-"$HOME/chain_build/_build/default/src/mtl2tba.exe"}
export EXE LIMIT=${LIMIT:-3600} SET=bench HERE
IDS=${IDS:-"R4 R5 N5 N6 N7 N8"}
JOBS=${JOBS:-3}
echo "start $(date -Is) limit=$LIMIT ids=$IDS jobs=$JOBS"
printf '%s\n' $IDS | xargs -P "$JOBS" -I{} bash -c '
  ONLY={} OUTFILE="$HERE/long_{}.tsv" bash "$HERE/run_compiled_eval.sh" > "$HERE/long_{}.log" 2>&1
  echo "done {} $(date -Is)"'
echo "end $(date -Is)"
