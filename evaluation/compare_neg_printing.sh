#!/bin/bash
# Compare the default printing of the negated event atom ("!p", an independent
# quoted proposition) with -explicit-neg (!"p", the negation of the atom "p"),
# for ids of formulas.tsv.
#
#   EXE=<mtl2tba.exe> IDS="F1 F5 R3 R4" bash compare_neg_printing.sh
#
# Prints, for each id and mode, the Spot automaton (states, cubes) and the
# size of compile(f) (locations, transitions, clocks), without optimization.
HERE="$(cd "$(dirname "$0")" && pwd)"
EXE=${EXE:-"$HERE/../tool/_build/default/src/mtl2tba.exe"}
IDS=${IDS:-"F1 F5 F11 R2 R3 R4"}
LIMIT=${LIMIT:-300}
W=$(mktemp -d)
printf 'id\tmode\tspot_states\tspot_cubes\tlocs\ttrans\tclocks\n'
for id in $IDS; do
  f=$(awk -F'\t' -v i="$id" '$1==i{print $3}' "$HERE/formulas.tsv")
  [ -z "$f" ] && continue
  for mode in default explicit-neg; do
    opt=""; [ "$mode" = explicit-neg ] && opt="-explicit-neg"
    st=$(cd "$W" && timeout "$LIMIT" "$EXE" -noweak -norecur -nopdf -n 0 $opt -stats -o "x_$id" "$f" 2>/dev/null)
    if [ -z "$st" ]; then printf '%s\t%s\ttimeout\n' "$id" "$mode"; continue; fi
    echo "$st" | awk -F'\t' -v id="$id" -v m="$mode" 'BEGIN{OFS="\t"}{print id, m, $2, $3, $5, $6, $7}'
  done
done
rm -rf "$W"
