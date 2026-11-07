"""Hand-built accepted and rejected words for the nested family N5-N8, checked by lasso_check.py.

    python3 -I lasso_nested_words.py
"""
import sys, os
sys.path.insert(0,'.')
import lasso_check as lc, tck_product as tp
forms={l.split('\t')[0]:l.split('\t')[2] for l in open('formulas.tsv') if l.strip() and not l.startswith('#')}
for k in (5,6,7,8):
    fid=f'N{k}'; props=[f'p{i}' for i in range(1,k+1)]
    A=tp.from_tbadot('A',f'compile_dot/{fid}.dot',props)
    C=tp.from_gv('C',f'casaal_out_x/{fid}.gv',props)
    phi=lc.parse(forms[fid])
    z=lambda a:[tuple([0]*len(a.clocks))]
    ini=lc.initial_valuations(A)
    res=[]
    for name,(ev,gaps,P,L) in {
        'in-order, gaps 0.5 (accept)': (props+['other'], [1]*(k+1), k, 1),
        'in-order, gaps 1.0 (accept: total 5 per step)': (props+['other'], [2]*(k+1), k, 1),
        'p1 then silence (reject)': (['p1','other'], [1,1], 1, 1),
        'in-order but one gap 6 units (reject)': (props+['other'], [1]*(k-1)+[12,1], k, 1),
        'p1..p_{k-1} then loop (reject)': (props[:-1]+['other'], [1]*k, k-1, 1),
    }.items():
        w=(ev,gaps,P,L)
        s=lc.holds(phi,*w); o=lc.accepts(A,w,ini); c=lc.accepts(C,w,z(C))
        res.append((name,s,o,c))
    print(fid,[ (n,s,o,c) for n,s,o,c in res])
    assert all(s==o==c for _,s,o,c in res), 'DISAGREEMENT'
print('all agree')
