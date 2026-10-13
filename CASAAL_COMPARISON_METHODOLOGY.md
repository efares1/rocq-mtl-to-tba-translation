# CASAAL comparison methodology

CASAAL implements the MTL<sub>0,∞</sub>-to-timed-automaton construction of Li et al.
(SPIN 2017). The CASAAL automata used here were produced earlier with the
scripts `run_casaal.py` (with `--exclusive`) and `run_casaal_neg.py` and are
stored in `evaluation/casaal_out_x/`, `casaal_out_neg/`, `casaal_out_rand/`;
CASAAL was not re-run in this revision.

## Semantic reconciliation

| Aspect | mtl2tba (Rocq model) | CASAAL output, as compared |
|---|---|---|
| words | one event per position, strictly increasing, divergent timestamps | Boolean valuations of propositions; run with mutually exclusive events (`--exclusive`) so that exactly one event holds per position |
| bounds | real (rational in practice) | integer |
| initial clocks | existential in the theorem; 0 in the products | 0 |
| acceptance | location-based Büchi | transition marks `{Acc[...]}` |
| hatted operators | native (F3, F13) | not available; the closest encoding with X is not equivalent, so F3 and F13 are not compared |

The products (`tck_product.py`) synchronize the automata on each event, add a
process forcing strictly increasing timestamps (clock z > 0 at each event)
and a process forcing time divergence and infinitely many events, start all
clocks at 0, and are checked by TChecker 0.8 (`tck-liveness -a couvscc`).

## What each check establishes

For a formula φ, with O = our automaton for φ, O′ for ¬φ, C, C′ CASAAL's:

| Check | Empty means | Does not mean |
|---|---|---|
| P1 = O × C′ | no word accepted by O and by C′ | O ⊆ L(φ) unless C′ accepts every model of ¬φ |
| P2 = C × O′ | no word accepted by C and O′ | — |
| S = O × O′ | our two automata are disjoint (self-consistency) | completeness |
| C-check = O × C | (sanity) non-empty for a satisfiable φ: both accept a common word | equality |

If CASAAL's automata for φ and ¬φ are complementary (not checked), P1 and P2
empty imply L(C) ⊆ L(O) and L(C′) ⊆ L(O′), i.e. agreement. Without that
assumption the checks establish only these inclusions (as stated in
this article). A timeout is inconclusive.

## Sizes

CASAAL prints Boolean transition labels; Spot's output, and hence
`compile(f)`, uses one transition per cube over the propositions and clock
literals. This article reports `compile(f)` sizes (before any optimization) and
explains this difference. It does not treat CASAAL as an optimizer baseline.

## X74 (random formulas)

φ = ◇(q ∧ r) → ¬p. Under mutual exclusion, ¬φ = ◇(q ∧ r) ∧ p is
unsatisfiable; our automaton for ¬φ has no accepting location. The CASAAL
output read by the converter has states labeled with the pending eventuality
`F(q & r)` but no acceptance mark. The converter used to read an unmarked
automaton as accepting every infinite run, so P1 was non-empty. This was an
acceptance-marking / format issue in the comparison, not a parsing
(parenthesization) problem.

Resolution (2026-10-12): `tck_product.py` now reads an unmarked CASAAL
automaton as follows. A state whose label contains an unbounded eventuality
(`F` or `U` without an upper bound, including lower-bounded `F[x>d]`,
`U[x>=d]`) is not accepting; the other states are accepting; with no
accepting state the language is empty. An automaton without such labels is
read as before (every run accepting). 16 of the 260 CASAAL files are affected
(all in `casaal_out_rand`). Rerunning the 100 random formulas changes only
X74 (P1 now empty); the other 99 rows are unchanged. The reading is our
interpretation of CASAAL's output, not a documented convention. Regression
test: `evaluation/test_tck_product_acceptance.py`.
