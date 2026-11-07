"""Two-train railway-crossing model for the railway-crossing case study.

    python railway.py MODEL out.xml EVENTS

writes the system as one timed automaton (UPPAAL XML, template Property, all
locations accepting), the explicit product of three components:

  Train i (i = 1, 2): Far --approach_i, x_i := 0--> Appr (x_i <= 10)
                      --enter_i, x_i >= 5--> In (x_i <= 20) --exit_i--> Far.
  Controller:         counts the trains between approach and exit (c), keeps
                      the gate state (Up/Down), and acknowledges every approach
                      by the event `lower`.  p is 1 when some approach is
                      not yet acknowledged; one `lower` acknowledges all of
                      them, and one clock x0, reset by the earliest pending
                      approach, bounds the time to acknowledge them (x0 <= D).
                      The gate is raised (`raise`) within 10 time units after
                      the crossing is clear (c = 0, no pending approach).

MODEL is one of
  ok        D = 4: the correct controller;
  slow      D = 7: lowering may take 7 time units, so a train can enter before
            the gate is down;
  counter   D = 4: the controller keeps a one-bit `busy` flag instead of a
            counter, so the exit of one train clears it while the other train
            is still approaching, and the gate may be raised too early;
  turnback  D = 4: a train may turn back while approaching (exit from Appr),
            so it can approach again too soon.

Events: approach1, approach2, lower, enter1, enter2, exit1, exit2, raise.
Events that EVENTS (the events of the requirement) does not mention are renamed
to `other`, which is how the automata of mtl2tba and tck_product.py represent
them.  One event per position; every location is accepting.
"""
import sys

model = sys.argv[1]; out = sys.argv[2]; evs = set(sys.argv[3].split(','))
D = 7 if model == 'slow' else 4
BOOL = model == 'counter'          # one-bit busy flag instead of a counter
TURN = model == 'turnback'


def ev(e):
    return e if e in evs else 'other'


def esc(s):
    return s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


def kind(s):
    t1, t2, g, c, p = s
    if p > 0:
        return 'P'                 # an approach waits for its `lower`
    if g == 'D' and c == 0:
        return 'R'                 # the gate is down and the crossing is clear
    return None


def inv(s):
    t1, t2, g, c, p = s
    parts = []
    for i, t in ((1, t1), (2, t2)):
        if t == 'A':
            parts.append(f'x{i}<=10')
        elif t == 'N':
            parts.append(f'x{i}<=20')
    k = kind(s)
    if k == 'P':
        parts.append(f'x0<={D}')
    elif k == 'R':
        parts.append('x0<=10')
    return ' && '.join(parts)


def succ(s):
    """(event, guard, resets, target) for every transition from s"""
    t1, t2, g, c, p = s
    ts = [t1, t2]
    res = []

    def go(e, guard, resets, t, g2, c2, p2):
        s2 = (t[0], t[1], g2, c2, p2)
        r = list(resets)
        k2 = kind(s2)
        if k2 is not None and k2 != kind(s) and 'x0' not in r:
            r.append('x0')
        res.append((e, guard, r, s2))

    for i in (1, 2):
        t = ts[i - 1]
        def upd(new):
            u = list(ts); u[i - 1] = new; return u
        if t == 'F':
            go(f'approach{i}', None, [f'x{i}'], upd('A'), g,
               1 if BOOL else c + 1, 1)
        if t == 'A':
            go(f'enter{i}', f'x{i}>=5', [], upd('N'), g, c, p)
            if TURN:
                go(f'exit{i}', None, [], upd('F'), g, c - 1, p)
        if t == 'N':
            go(f'exit{i}', None, [], upd('F'), g,
               0 if BOOL else c - 1, p)
    if p > 0:
        go('lower', None, [], ts, 'D', c, 0)
    if g == 'D' and p == 0 and c == 0:
        go('raise', None, [], ts, 'U', c, p)
    return res


init = ('F', 'F', 'U', 0, 0)
states = [init]; seen = {init}; edges = []
i = 0
while i < len(states):
    s = states[i]; i += 1
    for e, guard, resets, s2 in succ(s):
        edges.append((s, e, guard, resets, s2))
        if s2 not in seen:
            seen.add(s2); states.append(s2)

ids = {s: f'l{k}' for k, s in enumerate(states)}
x = '<nta>\n<template><name>Property</name><declaration>clock x0, x1, x2;</declaration>\n'
for s in states:
    nm = 'A' + ''.join(str(v) for v in s)
    x += f'<location id="{ids[s]}"><name>{nm}</name>'
    v = inv(s)
    if v:
        x += f'<label kind="invariant">{esc(v)}</label>'
    x += '</location>\n'
x += f'<init ref="{ids[init]}"/>\n'
for s, e, guard, resets, s2 in edges:
    x += f'<transition><source ref="{ids[s]}"/><target ref="{ids[s2]}"/>'
    if guard:
        x += f'<label kind="guard">{esc(guard)}</label>'
    x += f'<label kind="synchronisation">{ev(e)}?</label>'
    if resets:
        x += '<label kind="assignment">' + ', '.join(f'{r}=0' for r in resets) + '</label>'
    x += '</transition>\n'
x += '</template></nta>\n'
open(out, 'w').write(x)
print(len(states), 'locations', len(edges), 'transitions', file=sys.stderr)
