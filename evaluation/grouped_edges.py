"""Count the transitions of compile(f) after grouping parallel edges.

    python3 grouped_edges.py      ->  grouped_edges.tsv

compile_dot/<id>.dot are the compile(f) automata (mtl2tba -noweak -norecur -tba,
file <base>_tba.dot).  An edge label has up to three lines (guard, events, resets); empty guards
are omitted, so the parts are classified by content (a reset contains ':=').
Edges with the same source, target, guard and reset set are one *grouped*
transition whose label is the union of their event sets.  This changes no
automaton: it is a way of counting that matches the Boolean labels printed by
CASAAL (casaal_exclusive.tsv).  Explicit counts are those of Table 7.
"""
import csv, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'compile_dot')
cas = {}
with open(os.path.join(HERE, 'casaal_exclusive.tsv'), encoding='utf-8') as f:
    for r in csv.DictReader((l for l in f if not l.startswith('#')), delimiter='\t'):
        if r.get('exact') == 'yes' and r.get('transitions'):
            cas[r['id']] = int(r['transitions'])
EDGE = re.compile(r'^\s*(\S+)\s*->\s*(\S+)\s*\[label="(.*)"\];?\s*$')
rows = []
order = [l.split('\t')[0] for l in open(os.path.join(HERE, 'formulas.tsv'), encoding='utf-8') if l.strip() and not l.startswith('#')]
for i in order:
    p = os.path.join(D, i + '.dot')
    if not os.path.exists(p):
        continue
    explicit, groups = 0, set()
    for l in open(p, encoding='utf-8'):
        m = EDGE.match(l)
        if not m or m.group(1) in ('0', 'I'):
            continue
        parts = m.group(3).split(chr(92) + 'n')   # DOT labels contain the two characters backslash, n
        guard = next((p.strip() for p in parts if ':=' not in p and re.search(r'[<>]|==', p)), '')
        resets = next((p.strip() for p in parts if ':=' in p), '')
        explicit += 1
        groups.add((m.group(1), m.group(2), guard, resets))
    rows.append((i, explicit, len(groups), cas.get(i, '')))
with open(os.path.join(HERE, 'grouped_edges.tsv'), 'w', encoding='utf-8') as f:
    f.write('id\texplicit\tgrouped\tcasaal\n')
    for r in rows:
        f.write('\t'.join(str(x) for x in r) + '\n')
for r in rows:
    print(*r, sep='\t')
