"""Independent cross-check of the model-checking verdicts of the case study.

Random runs of the two-train railway model are sampled directly from the
timed automaton written by railway.py (locations, invariants, guards, resets;
times on a half-unit grid), as closed walks from the initial location (the
initial location resets every clock before use, so such a walk can be repeated
forever).  Each requirement is evaluated on the resulting lassos with the
independent semantics evaluator of lasso_check.py.  A requirement that TChecker
reports as holding must hold on every sampled run; a violated one should be
violated by some.   python3 crosscheck.py [N] [SEED]
"""
import random, re, subprocess, sys, os, tempfile
import xml.etree.ElementTree as ET
import lasso_check as lc

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
HERE = os.path.dirname(os.path.abspath(__file__))
ALL = 'approach1,approach2,lower,enter1,enter2,exit1,exit2,raise'
REQ = {'R1': '[]((approach1 | approach2) -> <>[<=5] lower)',
       'R2': '[]((approach1 -> (!enter1 U lower)) & (approach2 -> (!enter2 U lower)))',
       'R3': '[]((enter1 -> (!raise U exit1)) & (enter2 -> (!raise U exit2)))',
       'R4': '[]((approach1 -> ^[][<5] !approach1) & (approach2 -> ^[][<5] !approach2))'}
PHI = {k: lc.parse(v) for k, v in REQ.items()}


def load(model):
    out = os.path.join(tempfile.mkdtemp(), model + '.xml')
    subprocess.run([sys.executable, os.path.join(HERE, 'railway.py'), model, out, ALL],
                   check=True, capture_output=True)
    t = ET.parse(out).getroot().find('template')
    inv = {}
    for l in t.findall('location'):
        v = l.findtext("label[@kind='invariant']")
        inv[l.get('id')] = [(c, int(b) * 2) for c, b in re.findall(r'(x\d)<=(\d+)', v)] if v else []
    edges = {}
    for tr in t.findall('transition'):
        g = tr.findtext("label[@kind='guard']")
        guard = [(c, int(b) * 2) for c, b in re.findall(r'(x\d)>=(\d+)', g)] if g else []
        a = tr.findtext("label[@kind='assignment']") or ''
        edges.setdefault(tr.find('source').get('ref'), []).append(
            (tr.findtext("label[@kind='synchronisation']").rstrip('?'), guard,
             re.findall(r'(x\d)=0', a), tr.find('target').get('ref')))
    return t.find('init').get('ref'), inv, edges


def walk(init, inv, edges, maxlen=40):
    """closed walk from init: (events, gaps in half units)"""
    while True:
        loc, clk = init, {'x0': 0, 'x1': 0, 'x2': 0}
        ev, gaps = [], []
        while len(ev) < maxlen:
            opts = edges.get(loc, [])
            rng.shuffle(opts)
            for e, guard, resets, tgt in opts:
                hi = min([b - clk[c] for c, b in inv[loc]] + [30])
                lo = max([1] + [b - clk[c] for c, b in guard])
                if lo > hi:
                    continue
                d = rng.randint(lo, hi)
                c2 = {c: v + d for c, v in clk.items()}
                for r in resets:
                    c2[r] = 0
                if any(c2[c] > b for c, b in inv[tgt]):
                    continue
                ev.append(e); gaps.append(d); loc, clk = tgt, c2
                break
            else:
                break                                 # time lock: restart
            if loc == init and len(ev) >= 2 and rng.random() < 0.6:
                return ev, gaps
        # restart


for model in ('ok', 'slow', 'counter', 'turnback'):
    init, inv, edges = load(model)
    viol = {k: 0 for k in REQ}
    for _ in range(N):
        ev, gaps = walk(init, inv, edges)
        for k, f in PHI.items():
            if not lc.holds(f, ev, gaps, 0, len(ev)):
                viol[k] += 1
    print(model, 'runs', N, 'violating runs:', viol)
