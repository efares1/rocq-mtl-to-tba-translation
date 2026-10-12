"""LaTeX table of the Article 1 evaluation, generated from the raw results.

    python3 make_compiled_table.py      ->  compiled_table.tex, prints a summary

Inputs: compiled_bench.tsv (run_compiled_eval.sh), backend_validation.tsv
(run_spot_validation.sh), casaal_exclusive.tsv (CASAAL sizes, mutually
exclusive events), formulas.tsv.
"""
import csv
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def read(name):
    with open(os.path.join(HERE, name), encoding='utf-8') as f:
        return {r['id']: r for r in csv.DictReader((l for l in f if not l.startswith('#')), delimiter='\t')}


ours = read('compiled_bench.tsv')
back = read('backend_validation.tsv')
cas = read('casaal_exclusive.tsv')
grp = read('grouped_edges.tsv')
with open(os.path.join(HERE, 'formulas.tsv'), encoding='utf-8') as f:
    ids = [l.split('\t')[0] for l in f if l.strip() and not l.startswith('#')]
NOT_RUN = {'locs': '', 'trans': '', 'clocks': '', 'P1': '', 'P2': '', 'S': '', 'C': ''}


def verdict(r):
    """Summary of the TChecker checks P1, P2 (inclusions) and S (self-consistency)."""
    if r['P1'] == '-':
        return 'S only' if r['S'] == 'empty' else 'S ' + r['S']
    v = [r['P1'], r['P2'], r['S']]
    if all(x == 'empty' for x in v):
        return 'empty'
    if 'NONEMPTY' in v:
        return 'NONEMPTY'
    return 'timeout'


def cell(x):
    return x if x not in ('', None) else '--'


rows = []
for i in ids:
    o = ours.get(i)
    if o is None:
        c = cas.get(i)
        cas_cell = f"{c['states']}/{c['transitions']}/{c['clocks']}" if c and c['exact'] == 'yes' else 'n/a'
        rows.append((i, 'not run', '--', cas_cell, 'not run', cell(back.get(i, {}).get('equivalent', ''))))
        continue
    c = cas.get(i)
    b = back.get(i, {})
    cas_cell = f"{c['states']}/{c['transitions']}/{c['clocks']}" if c and c['exact'] == 'yes' and c['states'] else 'n/a'
    if o['locs'] == '':
        size = 'timeout'
    else:
        size = f"{o['locs']}/{o['trans']}/{o['clocks']}"
    eq = b.get('equivalent', '')
    g = grp.get(i, {}).get('grouped', '--') if o['locs'] else '--'
    rows.append((i, size, g, cas_cell, verdict(o) if o['locs'] else '--', cell(eq)))

with open(os.path.join(HERE, 'compiled_table.tex'), 'w', encoding='utf-8', newline='\n') as f:
    f.write('\\begin{table}[t]\n\\centering\n')
    f.write('\\caption{Automaton $\\mathsf{compile}(f)$ before any optimization, for the 31 configurations of '
            'Section~\\ref{sec:evaluation} (patterns in Table~\\ref{tab:patterns}; R$k$, N$k$ in the text). '
            'L/T/X: reachable locations/transitions/clocks. Grp.\\ T: transitions after grouping edges with the '
            'same source, target, guard, and resets into one (a count, not a transformation). CASAAL: '
            'locations/symbolic transitions/clocks with mutually exclusive events (n/a: no exact CASAAL '
            'encoding). $P_1,P_2,S$: TChecker products (``empty\'\': all three empty; ``S only\'\': only $S$ '
            'computed, hatted formulas; ``timeout\'\': undecided within 600~s). Backend: test of Spot\'s '
            'automaton against ltl2ba with Spot\'s tools (``yes\'\': both products empty; the three failures '
            'are timeouts, not discrepancies: equivalence check 600~s, ltl2ba and Spot 300~s). ``timeout\'\' in '
            'L/T/X: Spot did not finish, so \\texttt{compile} did not run. ``--\'\': not run. '
            'Tools: Spot 2.16, ltl2ba 1.3, TChecker 0.8.}\n')
    f.write('\\label{tab:compiled}\n\\scriptsize\n\\setlength{\\tabcolsep}{3pt}\n')
    f.write('\\begin{tabular}{@{}lrrrcc@{}}\n\\toprule\n')
    f.write('ID & L/T/X & Grp.\\ T & CASAAL & $P_1,P_2,S$ & Backend\\\\\n\\midrule\n')
    for r in rows:
        f.write(' & '.join(r) + '\\\\\n')
    f.write('\\bottomrule\n\\end{tabular}\n\\end{table}\n')

from collections import Counter
print('verdicts', Counter(r[4] for r in rows))
print('backend', Counter(r[5] for r in rows))
for r in rows:
    print('\t'.join(r))
