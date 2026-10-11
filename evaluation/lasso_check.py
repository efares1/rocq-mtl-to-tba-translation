"""Differential test on ultimately periodic timed words.

    python3 lasso_check.py [N_WORDS] [SEED] [IDS...]  ->  lasso_check.tsv

For each benchmark configuration and N random lasso words w = u v^omega
(events u, v with integer timestamps, strictly increasing, divergent), three
verdicts are compared:

  SEM   the formula, evaluated with the pointwise semantics of the article
        (independent Python evaluator, below);
  OURS  acceptance by compile(f)  (compile_dot/<id>.dot, mtl2tba -tba);
  CAS   acceptance by CASAAL's automaton (casaal_out_x/<id>.gv).

The automata read one event per position (propositions mutually exclusive;
the event `other` stands for any other event).  Clocks of CASAAL start at 0;
for OURS the theorem allows any initial clock values, which are tried on a
grid (<= 3 clocks) and otherwise 0 is used.  Time is scaled by 2 so that gaps
of one half time unit occur.  Acceptance is generalized Buechi on the
reachable graph of (location, capped clocks) at loop boundaries.

This is a test of finitely many words, not a proof.
"""
import csv, itertools, os, random, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tck_product as tp

S = 2  # time scale

# ---------------------------------------------------------------- formulas
TOK = re.compile(r'\s*(\[\]|<>|->|\^|\[(?:<=|<|>=|>)\d+\]|[()!&|]|[A-Za-z_]\w*)')


def tokenize(s):
    pos, out = 0, []
    while pos < len(s):
        m = TOK.match(s, pos)
        if not m:
            raise ValueError('cannot tokenize %r at %d' % (s, pos))
        out.append(m.group(1))
        pos = m.end()
    return out


def parse(text):
    t = tokenize(text)
    i = [0]

    def peek():
        return t[i[0]] if i[0] < len(t) else None

    def eat(x=None):
        v = peek()
        assert x is None or v == x, (x, v, text)
        i[0] += 1
        return v

    def interval():
        v = peek()
        if v and v.startswith('[') and v != '[]':
            eat()
            m = re.fullmatch(r'\[(<=|<|>=|>)(\d+)\]', v)
            return (m.group(1), int(m.group(2)) * S)
        return ('>=', 0)

    def imp():
        a = orr()
        if peek() == '->':
            eat()
            return ('or', ('not', a), imp())
        return a

    def orr():
        a = andd()
        while peek() == '|':
            eat()
            a = ('or', a, andd())
        return a

    def andd():
        a = untl()
        while peek() == '&':
            eat()
            a = ('and', a, untl())
        return a

    def untl():
        a = unary()
        if peek() == 'U':
            eat()
            I = interval()
            return ('until', I, a, unary())
        return a

    def unary():
        v = peek()
        if v == '!':
            eat()
            return ('not', unary())
        if v in ('[]', '<>'):
            eat()
            I = interval()
            return (('always' if v == '[]' else 'ev'), I, False, unary())
        if v == '^':
            eat()
            k = eat()
            assert k in ('[]', '<>'), text
            I = interval()
            return (('always' if k == '[]' else 'ev'), I, True, unary())
        if v == '(':
            eat()
            a = imp()
            eat(')')
            return a
        eat()
        if v == 'true':
            return ('true',)
        if v == 'false':
            return ('false',)
        return ('ap', v)

    f = imp()
    assert i[0] == len(t), (text, t[i[0]:])
    return f


def inI(I, d):
    op, c = I
    return {'<=': d <= c, '<': d < c, '>=': d >= c, '>': d > c}[op]


def holds(f, events, gaps, P, L):
    """truth of f at position 0 of the word whose first P events form the
    prefix and the next L events the loop (events, gaps: the P+L positions;
    gaps[i] = t_i - t_{i-1}, t_{-1} = 0).  The loop repeats forever."""
    R = 40
    N = P + L * R
    ev = [events[c] if c < P + L else events[P + (c - P) % L] for c in range(N)]
    gp = [gaps[c] if c < P + L else gaps[P + (c - P) % L] for c in range(N)]
    # the gap before the first loop event is the same in every pass
    tm = []
    t = 0
    for g in gp:
        t += g
        tm.append(t)
    canon = lambda u: u if u < P + L else P + (u - P) % L
    memo = {}

    def T(f, c):
        key = (id(f), c)
        if key in memo:
            return memo[key]
        r = ev_(f, c)
        memo[key] = r
        return r

    def at(f, u):
        return T(f, canon(u))

    def ev_(f, c):
        k = f[0]
        if k == 'true':
            return True
        if k == 'false':
            return False
        if k == 'ap':
            return ev[c] == f[1]
        if k == 'not':
            return not T(f[1], c)
        if k == 'and':
            return T(f[1], c) and T(f[2], c)
        if k == 'or':
            return T(f[1], c) or T(f[2], c)
        if k == 'ev':      # (ev, I, hat, phi)
            _, I, hat, phi = f
            for u in range(c + (1 if hat else 0), N):
                d = tm[u] - tm[c]
                if I[0] in ('<=', '<') and not inI(I, d):
                    break
                if inI(I, d) and at(phi, u):
                    return True
            return False
        if k == 'always':
            _, I, hat, phi = f
            for u in range(c + (1 if hat else 0), N):
                d = tm[u] - tm[c]
                if I[0] in ('<=', '<') and not inI(I, d):
                    break
                if inI(I, d) and not at(phi, u):
                    return False
            return True
        if k == 'until':   # (until, I, p, q)
            _, I, p, q = f
            for u in range(c, N):
                d = tm[u] - tm[c]
                if I[0] in ('<=', '<') and not inI(I, d):
                    return False
                if inI(I, d) and at(q, u):
                    return True
                if not at(p, u):
                    return False
            return False
        raise ValueError(k)

    return T(f, 0)


# ---------------------------------------------------------------- automata
GUARD = re.compile(r'(\w+?)(<=|<|>=|>)(\d+)')


def prep(a):
    """effective edges (src, tgt, ev, [(clock, op, c)], resets, labels) with
    committed intermediate locations of CASAAL's transition marks collapsed."""
    comm = {l for l, v in a.locs.items() if v[2]}
    tau = {}
    for s, t, ev, g, r, _ in a.edges:
        if s in comm:
            tau[s] = t
    out = []
    for s, t, ev, g, r, _ in a.edges:
        if s in comm:
            continue
        labels = frozenset()
        if t in comm:
            labels = frozenset(a.locs[t][0])
            t = tau[t]
        elif a.state_based:
            labels = frozenset(a.locs[t][0])
        gs = []
        if g:
            for part in g.split('&&'):
                m = GUARD.fullmatch(part.strip())
                gs.append((m.group(1), m.group(2), int(m.group(3)) * S))
        out.append((s, t, ev, gs, list(r), labels))
    alllabels = frozenset(l for e in out for l in e[5])
    return out, alllabels


def accepts(a, word, inits):
    edges, alllab = prep(a)
    byev = {}
    for e in edges:
        byev.setdefault((e[0], e[2]), []).append(e)
    clocks = sorted(f'{a.name}_{x}' for x in a.clocks)   # Auto.clk() returns the prefixed name
    cap = max([c for e in edges for (_, _, c) in e[3]] + [0]) + 1
    idx = {c: i for i, c in enumerate(clocks)}
    events, gaps, P, L = word

    def step(cfg, ev, gap):
        loc, vals = cfg
        vals = tuple(min(v + gap, cap) for v in vals)
        res = []
        for e in byev.get((loc, ev), []):
            ok = True
            for (x, op, c) in e[3]:
                v = vals[idx[x]]
                if not {'<=': v <= c, '<': v < c, '>=': v >= c, '>': v > c}[op]:
                    ok = False
                    break
            if ok:
                nv = list(vals)
                for r in e[4]:
                    nv[idx[r]] = 0
                res.append(((e[1], tuple(nv)), e[5]))
        return res

    starts = set()
    for iv in inits:
        starts.add((a.init, tuple(iv)))
    cur = starts
    for k in range(P):
        nxt = set()
        for cfg in cur:
            for c2, _ in step(cfg, events[k], gaps[k]):
                nxt.add(c2)
        cur = nxt
        if not cur:
            return False
    # loop graph
    graph, work, seen = {}, list(cur), set(cur)
    while work:
        n = work.pop()
        outs = {(n, frozenset())}
        states = {(n, frozenset())}
        for k in range(P, P + L):
            nxt = set()
            for (cfg, lab) in states:
                for c2, l2 in step(cfg, events[k], gaps[k]):
                    nxt.add((c2, lab | l2))
            states = nxt
            if not states:
                break
        graph[n] = list(states)
        for (c2, lab) in states:
            if c2 not in seen:
                seen.add(c2)
                work.append(c2)
    # SCCs (Kosaraju, iterative)
    nodes = list(graph)
    order, vis = [], set()
    for s in nodes:
        if s in vis:
            continue
        st = [(s, iter(graph[s]))]
        vis.add(s)
        while st:
            n, it = st[-1]
            adv = False
            for (m, _) in it:
                if m not in vis:
                    vis.add(m)
                    st.append((m, iter(graph[m])))
                    adv = True
                    break
            if not adv:
                order.append(n)
                st.pop()
    rev = {}
    for n in nodes:
        for (m, lab) in graph[n]:
            rev.setdefault(m, []).append(n)
    comp = {}
    for s in reversed(order):
        if s in comp:
            continue
        stack = [s]
        comp[s] = s
        while stack:
            n = stack.pop()
            for m in rev.get(n, []):
                if m not in comp:
                    comp[m] = s
                    stack.append(m)
    labs = {}
    for n in nodes:
        for (m, lab) in graph[n]:
            if comp.get(m) == comp.get(n):
                labs[comp[n]] = labs.get(comp[n], frozenset()) | lab
    for l in labs.values():
        if alllab <= l:
            return True
    return False


def initial_valuations(a, nclk_max=3, grid=None):
    k = len(a.clocks)
    if k == 0:
        return [()]
    if k > nclk_max:
        return [tuple([0] * k)]
    cap = (grid or 11)
    return list(itertools.product(range(cap + 1), repeat=k))


# ---------------------------------------------------------------- driver
def random_word(rng, alphabet, guided=False):
    """a random lasso word; guided words cycle through the propositions in
    order with small gaps, so that nested and chained formulas are met"""
    P = rng.randint(0, 4)
    L = rng.randint(1, 5)
    if guided:
        props = [a for a in alphabet if a != 'other'] or alphabet
        n = P + L
        start = rng.randrange(len(props))
        events = [props[(start + i) % len(props)] if rng.random() < 0.8 else rng.choice(alphabet) for i in range(n)]
        gaps = [rng.choice([1, 1, 1, 2, 2, 3]) for _ in range(n)]
        return events, gaps, P, L
    gaps = [rng.choice([1, 1, 2, 2, 3, 4, 6, 12]) for _ in range(P + L)]
    events = [rng.choice(alphabet) for _ in range(P + L)]
    return events, gaps, P, L


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    only = set(sys.argv[3:])
    rand = os.environ.get('SET') == 'random'
    dotdir = 'compile_dot_random' if rand else 'compile_dot'
    gvdir = 'casaal_out_rand' if rand else 'casaal_out_x'
    with open(os.path.join(HERE, 'random_formulas.tsv' if rand else 'formulas.tsv'), encoding='utf-8') as f:
        rows_ = [l.rstrip('\n').split('\t') for l in f if l.strip() and not l.startswith('#')]
    forms = [(r[0], '', r[1], '') for r in rows_] if rand else [tuple(r[:4]) for r in rows_]
    exact = {}
    with open(os.path.join(HERE, 'casaal_exclusive.tsv'), encoding='utf-8') as f:
        for r in csv.DictReader((l for l in f if not l.startswith('#')), delimiter='\t'):
            exact[r['id']] = r.get('exact') == 'yes'
    out = open(os.path.join(HERE, 'lasso_check_random.tsv' if rand else 'lasso_check.tsv'), 'w', encoding='utf-8')
    out.write('id\twords\tsem_true\tours_true\tcas_true\tsem_ne_ours\tours_acc_not_sem\tsem_not_ours\tsem_ne_cas\tours_ne_cas\n')
    for fid, desc, ours, cas in forms:
        if only and fid not in only:
            continue
        dot = os.path.join(HERE, dotdir, fid + '.dot')
        if not os.path.exists(dot):
            continue
        phi = parse(ours)
        props = sorted(set(re.findall(r'\b[a-z]\w*\b', ours)) - {'true', 'false', 'U'})
        A = tp.from_tbadot('A', dot, props)
        gv = os.path.join(HERE, gvdir, fid + '.gv')
        C = None
        if (rand or exact.get(fid)) and os.path.exists(gv):
            try:
                C = tp.from_gv('C', gv, props)
            except Exception:
                C = None
        inits = initial_valuations(A)
        zero = [tuple([0] * len(A.clocks))]
        alphabet = props + ['other']
        rng = random.Random(seed)
        c = dict(w=0, s=0, o=0, k=0, so=0, oa=0, sn=0, sc=0, oc=0)
        for _ in range(n):
            word = random_word(rng, alphabet, guided=(c['w'] % 2 == 1))
            sem = holds(phi, *word)
            o_ex = accepts(A, word, inits)
            o_zero = accepts(A, word, zero) if inits is not zero else o_ex
            c['w'] += 1
            c['s'] += sem
            c['o'] += o_ex
            if sem != o_ex:
                c['so'] += 1
            if o_zero and not sem:
                c['oa'] += 1           # soundness violated (must never happen)
            if sem and not o_ex:
                c['sn'] += 1           # completeness violated
            if C is not None:
                ca = accepts(C, word, [tuple([0] * len(C.clocks))])
                c['k'] += ca
                if sem != ca:
                    c['sc'] += 1
                if o_zero != ca:
                    c['oc'] += 1
        cas_cols = (str(c['k']), str(c['sc']), str(c['oc'])) if C is not None else ('', '', '')
        out.write('\t'.join([fid, str(c['w']), str(c['s']), str(c['o']), cas_cols[0], str(c['so']), str(c['oa']), str(c['sn']), cas_cols[1], cas_cols[2]]) + '\n')
        out.flush()
        print(fid, c, 'casaal' if C is not None else 'no-casaal', flush=True)
    out.close()


if __name__ == '__main__':
    main()
