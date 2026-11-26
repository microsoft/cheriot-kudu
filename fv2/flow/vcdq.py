#!/usr/bin/env python3
# vcdq.py <vcd> <regex> : print value changes of vars whose full name matches regex
import sys, re
f, rx = sys.argv[1], re.compile(sys.argv[2])
ids = {}; scope = []; t = 0; out = {}
for line in open(f):
    l = line.split()
    if not l: continue
    h = l[0]
    if h == '$scope': scope.append(l[2])
    elif h == '$upscope': scope.pop()
    elif h == '$var':
        name = '.'.join(scope + [l[4]])
        if rx.search(name): ids.setdefault(l[3], []).append(name)
    elif h[0] == '#': t = int(h[1:])
    elif h[0] in 'bB' and len(l) > 1 and l[1] in ids:
        v = h[1:]
        v = hex(int(v, 2)) if set(v) <= set('01') else v
        for n in ids[l[1]]: out.setdefault(n, []).append((t, v))
    elif h[0] in '01xz' and h[1:] in ids:
        for n in ids[h[1:]]: out.setdefault(n, []).append((t, h[0]))
for n in sorted(out): print(n, out[n])
