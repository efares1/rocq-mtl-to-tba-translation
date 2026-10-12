#!/bin/bash
# Full re-evaluation of the article with the current tool (explicit negation
# of the event atoms, !"p", and compile(f) computed with -compile-only).
#
#   bash run_all.sh            # all steps, in order, logs in run_all.log
#   STEPS="stage random" bash run_all.sh
#
# Steps (CPU-bound; run one after the other so that the times are comparable):
#   build    dune build of the tool
#   stage    per-stage times of compile(f), R3-R8        -> stage_times.tsv
#   dump     compile(f) as DOT for the word tests         -> compile_dot*/
#   lasso    differential test on random timed words      -> lasso_check*.tsv
#   random   TChecker products, 100 random formulas       -> compiled_random.tsv
#   spot     backend contract against ltl2ba              -> backend_validation.tsv
#   bench    TChecker products, 31 configurations         -> compiled_bench.tsv
# Machine: the times in the article were taken under WSL 2 on an i7-8650U.
HERE="$(cd "$(dirname "$0")" && pwd)"
STEPS=${STEPS:-"build stage dump lasso random spot bench"}
LOG="$HERE/run_all.log"
say() { echo "[$(date '+%F %T')] $*" | tee -a "$LOG"; }
cd "$HERE" || exit 1
IDS_NO_BIG="F1 F2 F3 F3b F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 R1 R2 R3 R4 R5 N1 N2 N3 N4 N5 N6 N7 N8"
for step in $STEPS; do
  say "start $step"
  case $step in
    build)  (cd "$HERE/../tool" && dune build ./src/mtl2tba.exe) >> "$LOG" 2>&1 ;;
    stage)  IDS="R3 R4 R5 R6 R7 R8" LIMIT=600 bash stage_times.sh >> "$LOG" 2>&1 ;;
    dump)   bash dump_compile_dot.sh >> "$LOG" 2>&1 ;;
    lasso)  python3 lasso_check.py 400 1 $IDS_NO_BIG >> "$LOG" 2>&1
            SET=random python3 lasso_check.py 150 1 >> "$LOG" 2>&1 ;;
    random) SET=random LIMIT=120 bash run_compiled_eval.sh >> "$LOG" 2>&1 ;;
    spot)   bash run_spot_validation.sh >> "$LOG" 2>&1 ;;
    bench)  SET=bench LIMIT=600 bash run_compiled_eval.sh >> "$LOG" 2>&1 ;;
    *)      say "unknown step $step" ;;
  esac
  say "end $step"
done
say "finished"
