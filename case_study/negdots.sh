#!/bin/bash
# writes n1_tba.dot, n2_tba.dot (compile of the negated R1, R2, R3) next to this script
HERE="$(cd "$(dirname "$0")" && pwd)"
E=~/mtl2tba_tool/_build/default/src/mtl2tba.exe
W=$(mktemp -d); cd "$W"
$E -compile-only -noweak -norecur -nopdf -tba -o n1 '!([]((approach1 | approach2) -> <>[<=5] lower))' > /dev/null
$E -compile-only -noweak -norecur -nopdf -tba -o n2 '!([]((approach1 -> (!enter1 U lower)) & (approach2 -> (!enter2 U lower))))' > /dev/null
$E -compile-only -noweak -norecur -nopdf -tba -o n3 '!([]((enter1 -> (!raise U exit1)) & (enter2 -> (!raise U exit2))))' > /dev/null
cp n1_tba.dot n2_tba.dot n3_tba.dot "$HERE/"
