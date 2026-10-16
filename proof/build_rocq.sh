#!/bin/bash
# Build the three Rocq files with the Windows Rocq Platform called from WSL,
# then check the assumptions and re-check the kernel proofs.
#   bash build_rocq.sh [build|assumptions|chk|all]
HERE="$(cd "$(dirname "$0")" && pwd)"
ROCQ_BIN=${ROCQ_BIN:-"/mnt/c/Rocq-Platform~9.0~2025.08/bin"}
COQC="$ROCQ_BIN/coqc.exe"
COQCHK="$ROCQ_BIN/coqchk.exe"
cd "$HERE" || exit 1
what=${1:-all}
if [ "$what" = build ] || [ "$what" = all ]; then
  make COQC="$COQC" || exit 1
fi
if [ "$what" = assumptions ] || [ "$what" = all ]; then
  "$COQC" CheckAssumptions.v || exit 1
fi
if [ "$what" = chk ] || [ "$what" = all ]; then
  "$COQCHK" -silent -o MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core \
    EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof OverlappingResponse_Example ZeroInit || exit 1
fi
echo "rocq: done ($what)"
