# A Mechanically Checked Translation of MTL<sub>0,∞</sub> into Timed Büchi Automata

Source, proofs, tool, and evaluation of the article on the mechanically checked MTL-to-TBA translation (unconditional with the verified breakpoint backend; relative to a backend contract for other backends such as Spot).

## Contents

| Path | Content |
|---|---|
| `paper.tex`, `references.bib`, `figures/`, `worked_translation.tex`, `evaluation_section.tex`, `build.ps1` | article source (ACM `acmart` format; built by `build.ps1`) |
| `proof/` | Rocq development: shared Core and Proof files, alarm-response example, the verified LTL-to-Büchi backend (`LTL_to_PBA_*.v`), `CheckAssumptions.v`, `ASSUMPTIONS.txt` |
| `tool/` | `mtl2tba` (OCaml): parser, call to Spot, LBTT reader, extracted Rocq functions (`src/optim.ml`), printers |
| `evaluation/` | evaluation of `compile(f)`: scripts, inputs, CASAAL outputs, raw results |
| `case_study/` | railway-crossing case study: timed model, model-checking workflow with `mtl2tba` and TChecker, counterexample extraction and checks, backend-contract check |
| `examples/` | Spot input/graph of the alarm-response example and the assurance scripts |
| `output/rocq/` | logs of the last fresh Rocq build, assumptions, and `coqchk` |
| `ROCQ_ASSUMPTIONS_AUDIT.md`, `CASAAL_COMPARISON_METHODOLOGY.md` | audit of the Rocq assumptions; methodology of the comparison with CASAAL |

## Main result

`MTL_to_TBA_correct_with` (file `EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.v`):
for every well-formed formula `f` and every propositional Büchi automaton `A`
that accepts exactly the models of the clocked-LTL formula `T f` on the
action-consistent propositional words (those in which `LNAct a` is the
complement of `LAct a`), the timed
Büchi automaton `compile_with A` accepts exactly the timed words that satisfy
`f`. It depends on four standard Rocq library axioms and on no project axiom;
the convenience theorem `MTL_to_TBA_correct` replaces the premise by the
project axiom `LTL_TO_BUCHI_CORRECT`.
`MTL_to_TBA_correct_verified` (file `LTL_to_PBA_Final.v`) removes the premise by
proving a breakpoint LTL-to-Büchi construction: the theorem has no contract
hypothesis and no project axiom.

Since v1.12, relaxation and reset completion are also proved for every positive
clocked-LTL formula over an abstract clock type that satisfies a polarity
condition (`abstract_compile_correct`, file `ClockedLTL_Abstract.v`), with the MTL
translation as an instance (`MTL_correct_via_abstract`, `ClockedLTL_Instance.v`)
and two counterexamples showing that the condition cannot be dropped
(`ClockedLTL_NonMTL.v`). No new axiom is used.

## Reproduction

Proofs (Rocq 9.0.1, Rocq Platform 2025.08):

```
cd proof
make COQC=<path>/coqc                 # Core, Proof, alarm example, zero-initialization corollary
<path>/coqc CheckAssumptions.v        # Print Assumptions of the main theorems
<path>/coqchk -silent -o MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core \
  EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof OverlappingResponse_Example ZeroInit LTL_to_PBA_Final
```

On Windows, `reproduce.ps1` runs the same steps and builds the PDF.

Tool and evaluation (Linux or WSL; OCaml ≥ 4.14, dune, menhir, Spot 2.16,
TChecker 0.8 for the language checks, ltl2ba 1.3 for the backend checks):

```
cd tool && dune build && cd ..
cd evaluation
bash run_compiled_eval.sh          # sizes of compile(f) and TChecker checks -> compiled_bench.tsv, compiled_random.tsv
bash run_spot_validation.sh        # Spot / ltl2ba / autfilt / LBTT checks   -> backend_validation.tsv
```

Both scripts run the tool with `-noweak -norecur`: the article's theorem covers
`compile(f)` without the weak-until and recurrence rewritings, which are
outside the article's theorem. The TChecker checks establish inclusions between
the languages of the two tools' automata, not equality, and they are tests,
not proofs.

Railway-crossing case study (same requirements: `tool` built, TChecker, Spot, ltl2ba):

```
bash case_study/run_case_study.sh            # R1-R4 on the correct (D=4) and faulty (D=7) controller -> case_study/results.tsv
bash case_study/cex.sh R1                    # counterexample (symbolic lasso) for a violated requirement
bash case_study/negdots.sh && python case_study/counterexample_check.py   # run drawn in the article
python case_study/crosscheck.py 3000 1       # independent evaluation on sampled runs of the models
bash case_study/backend_contract/run_spot_validation.sh   # backend contract on the four negated formulas
```

## Assurance boundary

Verified in Rocq: the clocked-LTL translation `T`, relaxation, reset
completion, and their composition with any backend automaton satisfying the
contract. Outside the proof: Spot and the LBTT reader (the backend contract is
tested, not proved), the parser and printers of `mtl2tba`, extraction, the
floating-point realization of bounds, and the use of the printed automata in
other tools.
