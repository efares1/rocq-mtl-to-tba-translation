# Rocq source for Paper 1

The clocked-LTL translation, its semantics, relaxation, reset completion, and
correctness proof are in the first two modules below. The third module gives a
concrete alarm-response instance, including a three-state Spot propositional
automaton transcribed into Rocq and checked against the clocked-LTL formula.
The development imports only Rocq standard-library modules.

| File | Role |
|---|---|
| `MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.v` | MTL syntax and semantics, formula-keyed clocks, clocked-LTL translation, automata, relaxation, reset completion, and the LTL-to-Büchi correctness contract |
| `EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.v` | canonical reset policy, residual obligations, soundness/completeness, `EncodingCorrect_proved`, and `MTL_to_TBA_correct_with` |
| `OverlappingResponse_Example.v` | bounded alarm-response formula, Spot automaton transcription, proved backend/formula language equivalence, concrete TBA specialization, and fixed infinite counterexample trace |

The development is intended to be checked with Rocq 9.0.1 (OCaml 4.14.2,
Rocq Platform 2025.08). The canonical PowerShell reproduction command is in
the parent [Access README](../README.md#build-and-reproduce). It independently
checks freshly compiled proof objects and compares a fresh assumption report
with the checked-in audit without overwriting that audit.

The convenience theorem `MTL_to_TBA_correct` uses the core axiom
`LTL_TO_BUCHI_CORRECT`. The theorem with suffix `_with`, which is the one
stated in the paper, takes backend language equivalence as an explicit
argument. `CheckAssumptions.v` prints the assumptions of the encoding
theorem, both end-to-end theorems, the concrete Spot backend contract and TBA
theorem, the fixed-trace violation lemma, and the rejection corollaries. The
captured Rocq 9.0.1 output is preserved in `ASSUMPTIONS.txt`.

The alarm-response instance uses Spot 2.16 to generate a propositional
automaton from the exact translated formula. The DOT graph is manually
transcribed into the Rocq `PBuchi` record; Rocq then proves the record's
acceptance equivalent to the formula on all propositional words (the generic
theorem needs it only on the action-consistent words, in which the negated
event atom is the complement of the event atom) and instantiates the generic
MTL-to-TBA theorem. The infinite trace has alarms at
times 0 and 2 and a handled event at time 4; Rocq proves that the concrete
Spot-instance TBA rejects it. This does not verify Spot or the DOT
transcription and does not export the TBA.
