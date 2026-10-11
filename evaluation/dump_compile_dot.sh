#!/bin/bash
# Dump compile(f) (mtl2tba -noweak -norecur -tba, file <base>_tba.dot) for the
# benchmark configurations and the random formulas, as input of grouped_edges.py
# and lasso_check.py.
#   EXE=<mtl2tba.exe> bash dump_compile_dot.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
EXE=${EXE:-"$HERE/../tool/_build/default/src/mtl2tba.exe"}
LIMIT=${LIMIT:-600}
dump() {  # <formulas file> <id column> <formula column> <out dir> <skip-regex>
  mkdir -p "$4"
  grep -v '^#' "$1" | while IFS=$'\t' read -r -a F; do
    id=${F[0]}; f=${F[$3]}
    [ -z "$id" ] && continue
    [[ -n "$5" && "$id" =~ $5 ]] && continue
    d=$(mktemp -d); cd "$d"
    timeout "$LIMIT" "$EXE" -noweak -norecur -nopdf -tba -o c "$f" > /dev/null 2>&1
    [ -s c_tba.dot ] && cp c_tba.dot "$4/$id.dot"
    cd /; rm -rf "$d"
  done
}
dump "$HERE/formulas.tsv" 0 2 "$HERE/compile_dot" '^R[678]$'
dump "$HERE/random_formulas.tsv" 0 1 "$HERE/compile_dot_random" ''
