# Rocq assumptions audit (2026-10-11)

Source: `Print Assumptions` (logs in `output/rocq/assumptions*.txt`) and `coqchk` context summaries.

## Two different kinds of dependency

| Assumption | Kind | Meaning |
|---|---|---|
| `LTL_TO_BUCHI_CORRECT` (project `Axiom`, Core) | **project-specific hypothesis about an external component** | states the existence of a correct LTL-to-Büchi translator; used only by the convenience theorems without the suffix `_with` (`MTL_to_TBA_correct`). The `_with` theorems take the backend contract as an explicit premise instead. It is not a mathematical axiom of the logic and is not discharged by Rocq. |
| `ClassicalDedekindReals.sig_forall_dec` | standard library | used by the construction of the real numbers (decidable comparisons of bounds) |
| `FunctionalExtensionality.functional_extensionality_dep` | standard library | functional extensionality |
| `Description.constructive_definite_description` | standard library | definite description (used by the classical Boolean reflection `decide_b`) |
| `Classical_Prop.classic` | standard library | excluded middle |

`coqchk` also lists `ClassicalDedekindReals.sig_not_dec` in the global context of the loaded
libraries; it does not appear in `Print Assumptions` of any principal theorem below.

## Principal theorems (fresh builds)

| Theorem | Project | Assumptions |
|---|---|---|
| `EncodingCorrect_proved`, `canonical_encoding_all` | both | 4 standard |
| `MTL_to_TBA_correct_with` | both | 4 standard |
| `MTL_to_TBA_correct` | both | 4 standard + `LTL_TO_BUCHI_CORRECT` |
| `alarm_response_tba_correct_with`, `alarm_response_spot_backend_contract`, `alarm_response_spot_tba_correct`, `alarm_overlap_trace_accepted_by_spot_tba`, `alarm_response_trace_rejected_by_any_correct_backend`, `alarm_response_trace_rejected_by_spot_tba` | this article | 4 standard |
| `alarm_response_trace_violates`, `alarm_overlap_trace_satisfies` | this article | `sig_forall_dec`, `functional_extensionality_dep` |
| `optimize_accepts`, `export_accepts`, `export_all_accepts` | the follow-up development | 4 standard |
| `split_accepts`, `split_all_accepts`, `export_guards_conjunctive`, `export_invariants_conjunctive`, `export_all_guards_conjunctive`, `export_all_invariants_conjunctive`, `symbolic_ext_accepts` | the follow-up development | `classic`, `functional_extensionality_dep`, `sig_forall_dec` |
| `MTL_to_exported_correct_with`, `MTL_to_exported_correct0_with`, `MTL_to_exported_all_correct_with` | the follow-up development | 4 standard |
| `MTL_to_exported_correct_recur_weak_with`, `MTL_to_exported_correct0_recur_weak_with` (default front end: recur + weak until) | the follow-up development | 4 standard |

Before unification, this article's copy additionally depended on
`IndefiniteDescription.constructive_indefinite_description` (through `functional_choice`) for
`MTL_to_TBA_correct_with` and six alarm-response theorems; that dependency is gone.

## Verified versus unverified components

Kernel-checked: everything stated by the theorems above, for the formula-indexed definitions
of the Core file. Not covered by Rocq: correctness of Spot and of its graph-to-record
transcription (backend contract), the parser and printers of `mtl2tba`, the floating-point
realization of real bounds in extracted code, the extraction mechanism, and the use of the
printed automata in UPPAAL or TChecker.
