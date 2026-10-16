#!/bin/bash
# Regenerate proof/ASSUMPTIONS.txt and the logs of output/rocq/ from a clean
# build of the three Rocq files (Windows Rocq Platform called from WSL).
#   bash proof/regen_rocq_logs.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
ROCQ_BIN=${ROCQ_BIN:-"/mnt/c/Rocq-Platform~9.0~2025.08/bin"}
COQC="$ROCQ_BIN/coqc.exe"
COQCHK="$ROCQ_BIN/coqchk.exe"
LOG="$ROOT/output/rocq"
mkdir -p "$LOG"
cd "$HERE" || exit 1
make clean > /dev/null 2>&1
make COQC="$COQC" > "$LOG/build.log" 2>&1; mk=$?
"$COQC" CheckAssumptions.v > "$HERE/ASSUMPTIONS.txt" 2> "$LOG/assumptions.stderr"; as=$?
cp "$HERE/ASSUMPTIONS.txt" "$LOG/assumptions.txt"
"$COQCHK" -silent -o MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core \
  EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof OverlappingResponse_Example ZeroInit \
  > "$LOG/coqchk.txt" 2>&1; ck=$?
{
  "$COQC" --version | head -1
  date -u +%Y-%m-%dT%H:%MZ
  sha256sum CheckAssumptions.v EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.v \
    MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.v OverlappingResponse_Example.v ZeroInit.v
  echo "make exit: $mk"
  echo "assumptions exit: $as"
  echo "coqchk exit: $ck"
} > "$LOG/build_info.txt"
rm -f "$LOG/assumptions.stderr"
echo "make $mk, assumptions $as, coqchk $ck"
