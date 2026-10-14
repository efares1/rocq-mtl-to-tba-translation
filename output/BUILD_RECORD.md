# Build record of the snapshot tagged `v1.1`

Snapshot: the commit tagged `v1.1` of this repository, which is the revision described by
the article. The tag `v1.0` is an earlier snapshot (16-page PDF) and is not the described
revision. File digests of the sources, proofs, evaluation tables and PDF are in
`SNAPSHOT_MANIFEST.txt`.

| Component | Version / value |
|---|---|
| Rocq Prover | 9.0.1 (Rocq Platform 2025.08), `rocq compile`, `rocq check` |
| OCaml (tool build), dune | 5.4.0, 3.20.2 (WSL 2, Ubuntu) |
| Spot (`ltl2tgba`) | 2.16 |
| TChecker | 0.8 (`tck-liveness -a couvscc`) |
| TeX | MiKTeX 25.12, class `ieeeaccess.cls` |

## Proofs
`output/rocq/` was produced from the files of `proof/` (SHA-256 in `output/rocq/build_info.txt`):
compilation, the assumption audit and the independent kernel check all exit 0.
`reproduce-ieee-access.ps1` repeats these steps in a temporary directory and compares the
regenerated assumptions with `proof/ASSUMPTIONS.txt`.

## Long TChecker run
`evaluation/long_R4.tsv` and `evaluation/long_N5.tsv`: limit 1800 s per check, one job at a
time, 2026-10-11 22:02 to 2026-10-12 00:54 (+04). R4: P2 empty; P1 and S timed out; sanity
product non-empty. N5: P1, P2, S timed out; sanity product non-empty. A timeout may also
reflect memory exhaustion of the checker; the two are not distinguished.

## Re-run of 2026-10-12
After the change of the printing of negated event atoms (`-explicit-neg`) and of the
backend contract (action-consistent words), the tool-dependent evaluation was repeated
with `evaluation/run_all.sh` (build, dump, lasso, random, spot, bench; then `STEPS=stage`):
start 2026-10-12 10:53, bench 11:48 to 16:22 (+04), stage 16:23 to 16:35. Rocq files:
`output/rocq/build_info.txt` (regenerated). The long runs above (R4, N5) were not repeated;
their automata are unchanged. Report: `PAPER1_EVALUATION_REPORT.md`, section 8.

## Alarm-response example, 2026-10-13
`examples/spot/alarm_response_backend.{ltl,dot}` were regenerated with the default
explicit negation (`!alarm`; Spot 2.16, same three-state graph). The Rocq record
`alarm_response_spot_backend` now mentions only event atoms and its contract
(`alarm_response_spot_backend_contract`, `alarm_response_backend_contract`) is required
on action-consistent words only. `proof/regen_rocq_logs.sh`: make, assumptions and
coqchk exit 0; the assumptions are unchanged. `examples/assurance/check_spot_transcription.py
--self-test` passes.

## PDF (as in the commit)
| File | Pages | SHA-256 |
|---|---|---|
| `paper1.pdf` | 17 | `8044da5a0cea45efd2a1dab9cf03bfb3a48c0a2c6f9d618ca8aa16fdf2b404c3` |

Rebuild with `build-ieee-access.ps1` (Windows, MiKTeX). PDF byte hashes depend on build
timestamps; the page count and extracted text are stable.
