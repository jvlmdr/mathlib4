#!/usr/bin/env python3

import sys
import os
import shutil
from pathlib import Path

missers=dict()

contents = open('missing.align2').read().splitlines()
for line in contents:
    fn, ln, s = line.split(sep="::")
    missers.setdefault(fn, [])
    missers[fn].append((int(ln), s + "\n"))

def zipLeft(l, c, r):
    r.insert(0, c)
    c, *l = l
    return l, c, r

def zipRight(l, c, r):
    l.insert(0, c)
    c, *r = r
    return l, c, r

def zipFix(l, c, r, data):
    if data == []:
        res = list(reversed(l))
        res.append(c)
        res += r
        return res
    (ln, align), *data = data
    while c[0] + 1 > ln:
        l, c, r = zipLeft(l, c, r)
    while c[1] != "\n":
        l, c, r = zipRight(l, c, r)
    r.insert(0, (c[0]+1, c[1]))
    c = (c[0], align)
    return zipFix(l, c, r, data)

def fixFile(fn, data):
    fnbak = fn + ".bak"
    shutil.copyfile(fn, fnbak)
    c, *l = reversed(list(enumerate(open(fnbak).readlines())))
    fixed = zipFix(l, c, [], data)
    open(fn, 'w').writelines([line for _, line in fixed])
    os.remove(fn + ".bak")

for k, v in missers.items():
    fn = k.replace('.', '/') + ".lean"
    print("===", fn)
    data = list(reversed(sorted(v, key=lambda p: p[0])))
    fixFile(fn, data)

