"""Sensitivity of the word-level test to the reading of unmarked CASAAL automata.

    python3 casaal_unmarked_sensitivity.py [N_WORDS] [SEED]  ->  casaal_unmarked_sensitivity.tsv

CASAAL prints some automata without acceptance marks.  tck_product.from_gv reads
such an automaton in one of two ways:
  all      (previous reading) the automaton accepts every infinite run;
  pending  (current reading)  a state whose label has an unbounded eventuality
           is not accepting; the language is empty if no state is accepting.
For every random formula phi, the CASAAL automata of phi and of !phi that carry
no mark are compared, on N random lasso words, with the pointwise semantics of
phi (resp. !phi) evaluated by the Python evaluator of lasso_check.py.  The
columns count the words on which each reading disagrees with the semantics.
This is a test of finitely many words, not a proof, and the oracle is the
authors' own evaluator.
"""
import os, random, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tck_product as tp
import lasso_check as lc


def accepts_with(a, word, zero, mode):
    """acceptance of a CASAAL automaton read in mode 'all' or 'pending'.

    lasso_check.accepts reads acceptance from the labels of the edges; the
    'pending' reading puts its label on the good states (state-based
    acceptance), or on an unreachable location when no state is good (empty
    language), so both cases are handled here."""
    if mode == 'pending' and a.acc_labels:
        if 'unreach' in a.locs:
            return False
        a.state_based = True
    return lc.accepts(a, word, zero)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(HERE, 'random_formulas.tsv'), encoding='utf-8')
            if l.strip() and not l.startswith('#')]
    out = open(os.path.join(HERE, 'casaal_unmarked_sensitivity.tsv'), 'w', encoding='utf-8')
    out.write('id\tautomaton\twords\tsem_true\tall_true\tpending_true\tall_ne_sem\tpending_ne_sem\n')
    unmarked_found = 0
    for r in rows:
        fid, ours = r[0], r[1]
        phi = lc.parse(ours)
        props = sorted(set(re.findall(r'\b[a-z]\w*\b', ours)) - {'true', 'false', 'U'})
        alphabet = props + ['other']
        for kind, suffix, neg in (('pos', '', False), ('neg', '_neg', True)):
            gv = os.path.join(HERE, 'casaal_out_rand', fid + suffix + '.gv')
            if not os.path.exists(gv):
                continue
            try:
                c_all = tp.from_gv('C', gv, props, unmarked='all')
                c_pend = tp.from_gv('C', gv, props, unmarked='pending')
            except Exception:
                continue
            if c_all.acc_labels:        # carries acceptance marks: both readings coincide
                continue
            unmarked_found += 1
            rng = random.Random(seed)
            cnt = dict(w=0, s=0, a=0, p=0, an=0, pn=0)
            zero = [tuple([0] * len(c_all.clocks))]
            for _ in range(n):
                word = lc.random_word(rng, alphabet, guided=(cnt['w'] % 2 == 1))
                sem = lc.holds(phi, *word)
                if neg:
                    sem = not sem
                a_ = accepts_with(c_all, word, zero, 'all')
                p_ = accepts_with(c_pend, word, zero, 'pending')
                cnt['w'] += 1
                cnt['s'] += sem
                cnt['a'] += a_
                cnt['p'] += p_
                cnt['an'] += (a_ != sem)
                cnt['pn'] += (p_ != sem)
            out.write('\t'.join([fid, kind, str(cnt['w']), str(cnt['s']), str(cnt['a']), str(cnt['p']),
                                 str(cnt['an']), str(cnt['pn'])]) + '\n')
            out.flush()
            print(fid, kind, cnt, flush=True)
    out.close()
    print('unmarked automata:', unmarked_found)


if __name__ == '__main__':
    main()
