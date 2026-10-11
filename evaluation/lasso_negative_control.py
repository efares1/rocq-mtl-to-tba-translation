"""Negative control for lasso_check.py: mutated formulas must disagree with compile(F1).

    python3 -I lasso_negative_control.py
"""
import sys, random
sys.path.insert(0, '.')
import lasso_check as lc, tck_product as tp
variants={'correct':'[](p -> <>[<=5] q)','bound 4 instead of 5':'[](p -> <>[<=4] q)','strict <5':'[](p -> <>[<5] q)','always instead of eventually':'[](p -> [][<=5] q)'}
A=tp.from_tbadot('A','compile_dot/F1.dot',['p','q'])
for name,f in variants.items():
    phi=lc.parse(f); rng=random.Random(7); d=0; n=300
    for _ in range(n):
        w=lc.random_word(rng,['p','q','other'])
        if lc.holds(phi,*w)!=lc.accepts(A,w,lc.initial_valuations(A)): d+=1
    print(f'{name:30} disagreements with compile(F1): {d}/{n}')
