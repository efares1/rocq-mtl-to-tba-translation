#!/bin/bash
# Model-checking workflow of the railway-crossing case study (railway crossing).
# For each requirement phi and each controller model (ok, slow, counter, turnback: see railway.py):
#   1. mtl2tba translates !phi into compile(!phi), the verified construction
#      (-compile-only -noweak -norecur: no optimization, no unproved rewriting);
#   2. railway.py writes the model; tck_product.py composes it with compile(!phi)
#      over infinite timed words with strictly increasing, divergent timestamps;
#   3. tck-liveness (TChecker, Couvreur SCC) tests emptiness of the product:
#      empty => phi holds on every run of the model; non-empty => a run violates phi.
# A final row checks that each model has at least one run (no vacuous verdict).
HERE="$(cd "$(dirname "$0")" && pwd)"
EXE=${EXE:-"$HERE/../tool/_build/default/src/mtl2tba.exe"}
TCK=${TCK:-~/local/bin/tck-liveness}
OUT="$HERE/results.tsv"
W=$(mktemp -d)
printf 'req\tformula\tmodel\tcompile_locs\tcompile_trans\tclocks\tverdict\tsecs\n' > "$OUT"
declare -A F=(
  [R1]='[]((approach1 | approach2) -> <>[<=5] lower)'
  [R2]='[]((approach1 -> (!enter1 U lower)) & (approach2 -> (!enter2 U lower)))'
  [R3]='[]((enter1 -> (!raise U exit1)) & (enter2 -> (!raise U exit2)))'
  [R4]='[]((approach1 -> ^[][<5] !approach1) & (approach2 -> ^[][<5] !approach2))'
)
for r in R1 R2 R3 R4; do
  f=${F[$r]}
  EV=$(python3 -c "import re,sys; print(','.join(sorted(set(re.findall(r'\b[a-z][a-z0-9_]*\b', sys.argv[1])) - {'true','false'})))" "$f")
  rm -f "$W"/*
  st=$(cd "$W" && "$EXE" -compile-only -noweak -norecur -nopdf -tba -stats -o neg "!($f)" 2>/dev/null)
  locs=$(echo "$st" | cut -f5); trans=$(echo "$st" | cut -f6); clk=$(echo "$st" | cut -f7)
  for m in ok slow counter turnback; do
    python3 "$HERE/railway.py" $m "$W/$m.xml" "$EV"
    lab=$(python3 "$HERE/tck_product.py" "$W/$m.tck" "$EV" P:"$W/neg_tba.dot" S:"$W/$m.xml")
    t0=$(date +%s.%N)
    res=$(timeout 600 "$TCK" -a couvscc -l "$lab" "$W/$m.tck" 2>&1 | grep -E '^CYCLE')
    t1=$(date +%s.%N)
    case "$res" in
      "CYCLE false") v=holds ;; "CYCLE true") v=VIOLATED ;; *) v=timeout ;;
    esac
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%.2f\n' "$r" "$f" "$m" "$locs" "$trans" "$clk" "$v" "$(echo "$t1-$t0"|bc)" >> "$OUT"
  done
done
# vacuity: the model alone has an accepting infinite run
for m in ok slow counter turnback; do
  ALL=approach1,approach2,lower,enter1,enter2,exit1,exit2,raise
  python3 "$HERE/railway.py" $m "$W/$m.xml" $ALL
  lab=$(python3 "$HERE/tck_product.py" "$W/$m.tck" $ALL S:"$W/$m.xml")
  res=$(timeout 600 "$TCK" -a couvscc -l "$lab" "$W/$m.tck" 2>&1 | grep -E '^CYCLE')
  printf 'model-alone	-	%s	-	-	-	%s	-
' "$m" "$res" >> "$OUT"
done
column -t -s $'\t' "$OUT"
rm -rf "$W"
