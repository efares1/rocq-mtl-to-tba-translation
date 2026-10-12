#!/bin/bash
# Per-stage times of compile(f) for ids of formulas.tsv (default: the R family).
#
#   IDS="R3 R4 R5 R6 R7 R8" LIMIT=600 bash stage_times.sh
#
# mtl2tba is run with the options of the paper (-noweak -norecur), with the
# optimization of the follow-up development disabled (-n 0) and with -v.  The
# verbose log is time-stamped line by line, and the run is stopped once
# compile(f) has been computed (the line "after reset completion"), so that
# the later stages (optimization and export, which are not part of compile(f))
# do not count.  Output: stage_times.tsv, one line per id:
#   id  status  parse_T_s  spot_s  compile_s  total_to_compile_s  locs  trans
# parse_T_s: parsing and the clocked-LTL translation T(f); spot_s: the call to
# Spot and the LBTT reading; compile_s: reading into the propositional
# automaton, relaxation and reset completion; locs/trans: size of compile(f).
# status: ok, timeout (LIMIT s without reaching compile(f)), or no-spot
# (Spot did not return within LIMIT s).
HERE="$(cd "$(dirname "$0")" && pwd)"
EXE=${EXE:-"$HERE/../tool/_build/default/src/mtl2tba.exe"}
LIMIT=${LIMIT:-600}
IDS=${IDS:-"R3 R4 R5 R6 R7 R8"}
OUT=${OUT:-"$HERE/stage_times.tsv"}
W=$(mktemp -d)
printf 'id\tstatus\tparse_T_s\tspot_s\tcompile_s\ttotal_to_compile_s\tlocs\ttrans\n' > "$OUT"
for id in $IDS; do
  f=$(awk -F'\t' -v i="$id" '$1==i{print $3}' "$HERE/formulas.tsv")
  [ -z "$f" ] && continue
  rm -f "$W"/*
  t0=$(date +%s.%N)
  ( cd "$W" && "$EXE" -noweak -norecur -nopdf -compile-only -v -o "x_$id" "$f" 2>&1 \
      | while IFS= read -r l; do echo "$(date +%s.%N) $l"; done > "$W/log" ) &
  pid=$!
  while kill -0 $pid 2>/dev/null; do
    if grep -q 'after reset completion' "$W/log" 2>/dev/null; then break; fi
    now=$(date +%s.%N)
    if awk -v a="$t0" -v b="$now" -v l="$LIMIT" 'BEGIN{exit !(b-a>l)}'; then break; fi
    sleep 1
  done
  pkill -f "mtl2tba.exe.*x_$id " 2>/dev/null
  pkill -f "ltl2tgba" 2>/dev/null
  wait $pid 2>/dev/null
  ts() { grep -m1 "$1" "$W/log" | cut -d' ' -f1; }
  tl=$(ts 'clocked LTL:'); tsp=$(ts ' Spot: '); tc=$(ts 'after reset completion')
  if [ -z "$tl" ]; then
    printf '%s\ttimeout\t\t\t\t\t\t\n' "$id" >> "$OUT"; echo "$id: timeout before Spot"; continue
  fi
  if [ -z "$tsp" ]; then
    printf '%s\tno-spot\t%.3f\t\t\t\t\t\n' "$id" "$(echo "$tl - $t0" | bc -l)" >> "$OUT"; echo "$id: Spot not finished"; continue
  fi
  if [ -z "$tc" ]; then
    printf '%s\ttimeout\t%.3f\t%.3f\t\t\t\t\n' "$id" "$(echo "$tl - $t0" | bc -l)" "$(echo "$tsp - $tl" | bc -l)" >> "$OUT"
    echo "$id: compile(f) not reached"; continue
  fi
  sz=$(grep -m1 'after reset completion' "$W/log" | sed -E 's/.*: ([0-9]+) locations, ([0-9]+) transitions.*/\1\t\2/')
  printf '%s\tok\t%.3f\t%.3f\t%.3f\t%.3f\t%s\n' "$id" "$(echo "$tl - $t0" | bc -l)" \
    "$(echo "$tsp - $tl" | bc -l)" "$(echo "$tc - $tsp" | bc -l)" "$(echo "$tc - $t0" | bc -l)" "$sz" >> "$OUT"
  echo "$id: ok"
done
rm -rf "$W"
