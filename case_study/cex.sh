#!/bin/bash
# Extract a counterexample (symbolic lasso) for a violated requirement: bash cex.sh R1|R2|R3|R4 slow|counter|turnback
HERE="$(cd "$(dirname "$0")" && pwd)"
EXE="$HERE/../tool/_build/default/src/mtl2tba.exe"; TCK=~/local/bin/tck-liveness
declare -A F=(
  [R1]='[]((approach1 | approach2) -> <>[<=5] lower)'
  [R2]='[]((approach1 -> (!enter1 U lower)) & (approach2 -> (!enter2 U lower)))'
  [R3]='[]((enter1 -> (!raise U exit1)) & (enter2 -> (!raise U exit2)))'
  [R4]='[]((approach1 -> ^[][<5] !approach1) & (approach2 -> ^[][<5] !approach2))'
)
f=${F[$1]}; MV=$2
EV=$(python3 -c "import re,sys; print(','.join(sorted(set(re.findall(r'\b[a-z][a-z0-9_]*\b', sys.argv[1])) - {'true','false'})))" "$f")
W=$(mktemp -d); cd $W
"$EXE" -compile-only -noweak -norecur -nopdf -tba -o neg "!($f)" >/dev/null 2>&1
python3 "$HERE/railway.py" $MV bad.xml "$EV"
lab=$(python3 "$HERE/tck_product.py" bad.tck "$EV" P:neg_tba.dot S:bad.xml)
"$TCK" -a ndfs -C symbolic -l "$lab" bad.tck
