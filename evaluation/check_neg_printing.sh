#!/bin/bash
# Validate the -explicit-neg printing on one formula: the clocked-LTL formula
# is written by the two printers (-check), Spot reads the LBT text, and the
# automaton built by the reader (HOA) must be equivalent to Spot's own.
#
#   EXE=<mtl2tba.exe> bash check_neg_printing.sh '<formula>'
HERE="$(cd "$(dirname "$0")" && pwd)"
EXE=${EXE:-"$HERE/../tool/_build/default/src/mtl2tba.exe"}
F=${1:-"(<>[<=5] p) & ([][<2] !p)"}
W=$(mktemp -d)
cd "$W" || exit 1
for mode in default explicit-neg; do
  opt=""; [ "$mode" = explicit-neg ] && opt="-explicit-neg"
  "$EXE" -noweak -norecur -nopdf -n 0 $opt -check c -o o "$F" > /dev/null 2> err.txt
  echo "== $mode"
  if [ ! -s c_ltl.lbt ]; then echo "no c_ltl.lbt:"; head -3 err.txt; continue; fi
  echo "lbt: $(cat c_ltl.lbt)"
  ltl2tgba --lbt-input -F c_ltl.lbt -B > s.hoa 2>/dev/null
  if autfilt --equivalent-to=c_ba.hoa s.hoa > /dev/null 2>&1; then
    echo "reader automaton equivalent to Spot's: yes"
  else
    echo "reader automaton equivalent to Spot's: NO"
  fi
  rm -f c_ltl.lbt c_ba.hoa
done
rm -rf "$W"
