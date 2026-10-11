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
    f.write('\\caption{Automaton $\\mathsf{compile}(f)$ before any optimization: '
            'locations/transitions/clocks (L/T/X), the transitions after grouping edges with the same '
            'source, target, guard, and resets into one (Grp.\\ T; a count, not a transformation), '
            'CASAAL output with mutually exclusive events '
            '(locations/symbolic transitions/clocks; n/a: no exact CASAAL encoding), TChecker products '
            '$P_1,P_2,S$ (``empty\'\': all three empty), and the tested backend contract.}\n')
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
