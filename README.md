# A Mechanically Verified Translation of MTL<sub>0,∞</sub> into Timed Büchi Automata

Source, proofs, tool, and evaluation of the IEEE Access article.

## Contents

| Path | Content |
|---|---|
| `paper1.tex`, `references.bib`, `figures/`, `worked_translation.tex` | article source (IEEE Access template files at the root) |
| `proof/` | Rocq development: shared Core and Proof files, alarm-response example, `CheckAssumptions.v`, `ASSUMPTIONS.txt` |
| `tool/` | `mtl2tba` (OCaml): parser, call to Spot, LBTT reader, extracted Rocq functions (`src/optim.ml`), printers |
| `evaluation/` | evaluation of `compile(f)`: scripts, inputs, CASAAL outputs, raw results |
| `examples/` | Spot input/graph of the alarm-response example and the assurance scripts |
| `output/rocq/` | logs of the last fresh Rocq build, assumptions, and `coqchk` |
| `ROCQ_*.md` | shared-foundation, build, and assumptions audits |

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

## Reproduction

Proofs (Rocq 9.0.1, Rocq Platform 2025.08):

```
cd proof
make COQC=<path>/coqc                 # Core, Proof, alarm example, zero-initialization corollary
<path>/coqc CheckAssumptions.v        # Print Assumptions of the main theorems
<path>/coqchk -silent -o MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core \
  EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof OverlappingResponse_Example ZeroInit
```

On Windows, `reproduce-ieee-access.ps1` runs the same steps and builds the PDF.

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

## Assurance boundary

Verified in Rocq: the clocked-LTL translation `T`, relaxation, reset
completion, and their composition with any backend automaton satisfying the
contract. Outside the proof: Spot and the LBTT reader (the backend contract is
tested, not proved), the parser and printers of `mtl2tba`, extraction, the
floating-point realization of bounds, and the use of the printed automata in
other tools.
