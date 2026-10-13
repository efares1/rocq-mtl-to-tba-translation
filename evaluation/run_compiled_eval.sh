#!/bin/bash
# Evaluation of the article on the verified translation compile(f): the TBA
# obtained by the clocked-LTL translation, Spot, relaxation and reset
# completion (mtl2tba -tba, <base>_tba.dot), before any optimization.
#
# For every benchmark configuration of formulas.tsv and every random formula
# of random_formulas.tsv:
#   sizes   locations / transitions / clocks of compile(f)   (mtl2tba -stats)
# and, when CASAAL automata of phi and !phi exist, with TChecker (couvscc):
#   P1  compile(phi) x CASAAL(!phi)     empty  =>  CASAAL(!phi) and compile(phi) disjoint
#   P2  CASAAL(phi)  x compile(!phi)    empty  =>  CASAAL(phi) and compile(!phi) disjoint
#   S   compile(phi) x compile(!phi)    empty  (self-consistency)
#   C   compile(phi) x CASAAL(phi)      non-empty unless phi is unsatisfiable (sanity)
# Products read infinite timed words, one event per position, strictly
# increasing and divergent timestamps, clocks at 0 at time 0 (tck_product.py).
#
#   EXE=<mtl2tba.exe> bash run_compiled_eval.sh        [SET=bench|random|all]
# Writes compiled_bench.tsv and compiled_random.tsv.  LIMIT seconds per tool
# run and per emptiness check (default 600).  ONLY="N7 N8" runs just those
# bench ids and writes compiled_bench_only.tsv (or $OUTFILE).
HERE="$(cd "$(dirname "$0")" && pwd)"
EXE=${EXE:-"$HERE/../tool/_build/default/src/mtl2tba.exe"}
TCK=${TCK:-~/local/bin/tck-liveness}
LIMIT=${LIMIT:-600}
SET=${SET:-all}
# The article's theorem covers compile(f) without the recur and weak-until
# rewritings, which are outside it.
OPTS=${OPTS:-"-noweak -norecur -compile-only"}
W=$(mktemp -d)

check() {
  lab=$(python3 "$HERE/tck_product.py" "$W/m.tck" "$EVENTS" "$@" 2>/dev/null) || { echo "convert-error"; return; }
  r=$(timeout "$LIMIT" "$TCK" -a couvscc -l "$lab" "$W/m.tck" 2>&1 | grep -E '^CYCLE')
  case "$r" in
    "CYCLE false") echo empty ;;
    "CYCLE true") echo NONEMPTY ;;
    *) echo timeout ;;
  esac
}

events() {
  python3 -c "import re,sys; print(','.join(sorted(set(re.findall(r'\b[a-z][a-z0-9_]*\b', sys.argv[1])) - {'true','false'})))" "$1"
}

# run <id> <formula> <casaal-pos.gv> <casaal-neg.gv> <out.tsv>
run() {
  id=$1; f=$2; cp=$3; cn=$4; out=$5
  rm -f "$W"/*
  EVENTS=$(events "$f")
  t0=$(date +%s.%N)
  st=$(cd "$W" && timeout "$LIMIT" "$EXE" $OPTS -nopdf -tba -stats -o pos "$f" 2>/dev/null)
  t1=$(date +%s.%N)
  if [ ! -s "$W/pos_tba.dot" ]; then
    printf '%s\t%s\t\t\t\t\ttool timeout\t\t\t\n' "$id" "$f" >> "$out"; echo "$id: tool timeout"; return
  fi
  locs=$(echo "$st" | cut -f5); trans=$(echo "$st" | cut -f6); clk=$(echo "$st" | cut -f7)
  secs=$(python3 -c "print(f'{$t1-$t0:.2f}')")
  (cd "$W" && timeout "$LIMIT" "$EXE" $OPTS -nopdf -tba -o neg "!($f)" > /dev/null 2>&1)
  if [ -z "$cp" ] || [ ! -f "$cp" ] || [ ! -f "$cn" ]; then
    s=$( [ -s "$W/neg_tba.dot" ] && check A:"$W/pos_tba.dot" C:"$W/neg_tba.dot" || echo "-")
    printf '%s\t%s\t%s\t%s\t%s\t%s\t-\t-\t%s\t-\n' "$id" "$f" "$locs" "$trans" "$clk" "$secs" "$s" >> "$out"
    echo "$id: $locs/$trans/$clk  S=$s (no CASAAL pair)"; return
  fi
  p1=$(check A:"$W/pos_tba.dot" B:"$cn")
  p2=$( [ -s "$W/neg_tba.dot" ] && check B:"$cp" C:"$W/neg_tba.dot" || echo "tool-timeout")
  s=$( [ -s "$W/neg_tba.dot" ] && check A:"$W/pos_tba.dot" C:"$W/neg_tba.dot" || echo "tool-timeout")
  c=$(check A:"$W/pos_tba.dot" B:"$cp")
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$f" "$locs" "$trans" "$clk" "$secs" "$p1" "$p2" "$s" "$c" >> "$out"
  echo "$id: $locs/$trans/$clk  P1=$p1 P2=$p2 S=$s C=$c"
}

HDR='id\tformula\tlocs\ttrans\tclocks\ttime_s\tP1\tP2\tS\tC\n'
if [ "$SET" = bench ] || [ "$SET" = all ]; then
  OUT="$HERE/compiled_bench.tsv"
  if [ -n "$ONLY" ]; then OUT="${OUTFILE:-$HERE/compiled_bench_only.tsv}"; fi
  printf "$HDR" > "$OUT"
  grep -v '^#' "$HERE/formulas.tsv" | while IFS=$'\t' read -r id desc ours cas; do
    [ -z "$id" ] && continue
    if [ -n "$ONLY" ] && ! echo " $ONLY " | grep -q " $id "; then continue; fi
    ex=$(awk -F'	' -v i="$id" '$1==i{print $2}' "$HERE/casaal_results.tsv")
    if [ "$ex" = yes ]; then
      run "$id" "$ours" "$HERE/casaal_out_x/$id.gv" "$HERE/casaal_out_neg/$id.gv" "$OUT"
    else
      run "$id" "$ours" "" "" "$OUT"
    fi
  done
fi
if [ "$SET" = random ] || [ "$SET" = all ]; then
  OUT="$HERE/compiled_random.tsv"; printf "$HDR" > "$OUT"
  grep -v '^#' "$HERE/random_formulas.tsv" | while IFS=$'\t' read -r id ours cas; do
    [ -z "$id" ] && continue
    run "$id" "$ours" "$HERE/casaal_out_rand/$id.gv" "$HERE/casaal_out_rand/${id}_neg.gv" "$OUT"
  done
fi
rm -rf "$W"
