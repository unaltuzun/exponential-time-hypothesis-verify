#!/usr/bin/env python3
"""Compute the transitive import closure of a Lean module within the OAI library
and report which Mathlib modules are imported directly. Usage:
  python3 -I import_closure.py <lean_root> <Module.Name>
"""
import re, sys, os
from collections import deque

root = sys.argv[1]
start = sys.argv[2]
imp_re = re.compile(r'^\s*import\s+([A-Za-z0-9_.«»]+)', re.M)

def path_of(mod):
    return os.path.join(root, *mod.split('.')) + '.lean'

seen, mathlib_direct, external = set(), set(), set()
q = deque([start])
total_lines = 0
while q:
    m = q.popleft()
    if m in seen: continue
    seen.add(m)
    p = path_of(m)
    if not os.path.exists(p):
        external.add(m); seen.discard(m); continue
    with open(p, encoding='utf-8', errors='replace') as f:
        txt = f.read()
    total_lines += txt.count('\n')
    for dep in imp_re.findall(txt):
        if dep.startswith('Mathlib') or dep == 'Mathlib':
            mathlib_direct.add(dep)
        elif dep.startswith('OAI') or dep.startswith('ComparatorChallenges'):
            q.append(dep)
        else:
            external.add(dep)

print(f"OAI modules in closure of {start}: {len(seen)}")
print(f"total lines: {total_lines}")
print(f"direct Mathlib imports ({len(mathlib_direct)}):")
for m in sorted(mathlib_direct): print("  ", m)
print(f"other external imports: {sorted(external)}")
