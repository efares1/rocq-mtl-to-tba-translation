"""Checks the counterexample run drawn in the paper (two-train model, controller
`counter`, requirement R3).

The run repeats approach1@1, approach2@2, lower@3, enter1@6, exit1@8, enter2@9,
raise@12, exit2@13 with period 15 (times in time units, scaled by 2 below).  It
is a behavior of the `counter` model of railway.py: the one-bit busy flag is
cleared by exit1 while train 2 is still approaching, so the gate is raised while
train 2 is in the crossing.  It violates R3 only, and it is accepted by
compile(not R3).  Run negdots.sh first (writes n3_tba.dot).
python counterexample_check.py
"""
import lasso_check as lc, tck_product as tp
full = ['approach1', 'approach2', 'lower', 'enter1', 'exit1', 'enter2', 'raise', 'exit2']
gaps = [3, 1, 1, 3, 2, 1, 3, 1]
REQ = {'R1': '[]((approach1 | approach2) -> <>[<=5] lower)',
       'R2': '[]((approach1 -> (!enter1 U lower)) & (approach2 -> (!enter2 U lower)))',
       'R3': '[]((enter1 -> (!raise U exit1)) & (enter2 -> (!raise U exit2)))',
       'R4': '[]((approach1 -> ^[][<5] !approach1) & (approach2 -> ^[][<5] !approach2))'}
g2 = [2 * g for g in gaps]
for k, f in REQ.items():
    print(k, 'holds on the run:', lc.holds(lc.parse(f), full, g2, 0, len(full)))
ev = ['enter1', 'enter2', 'raise', 'exit1', 'exit2']
w = ([e if e in ev else 'other' for e in full], g2, 0, len(full))
A = tp.from_tbadot('A', 'n3_tba.dot', ev)
print('n3 accepted by compile(neg R3):', lc.accepts(A, w, lc.initial_valuations(A)))
