"""Classify each public pin declaration of a file against the whole port:
  IDENTICAL / DIFFERENT (with both statements) / ABSENT.
Usage: python3 classify_tmp.py <pinrel>
"""
import importlib.util, sys
from pathlib import Path

spec = Path("/home/haitao/proj/reasonix-sandbox/flt_for_human/lean/spec/check_flt_statements.py")
s = importlib.util.spec_from_file_location("ck", spec)
m = importlib.util.module_from_spec(s); s.loader.exec_module(m)
flt = Path.home()/"proj"/"fermats-last-theorem"
LEAN = Path("/home/haitao/proj/reasonix-sandbox/flt_for_human/lean")

pub, priv, where = {}, {}, {}
for p in sorted((LEAN/"FLTForHuman").rglob("*.lean")):
    text = p.read_text()
    for raw, kind, stmt in m.raw_declarations(text):
        pub.setdefault(raw.rsplit(".", 1)[-1], []).append((kind, stmt, p.name))
    for raw, kind, stmt in m.raw_declarations(text, include_private=True):
        priv.setdefault(m.promoted_key(raw), []).append((kind, stmt, p.name))
        priv.setdefault(raw.rsplit(".", 1)[-1], []).append((kind, stmt, p.name))

def has(cands, kind, stmt):
    return any(c[0] == kind and c[1] == stmt for c in (cands or ()))

pinrel = sys.argv[1]
pint = (flt/pinrel).read_text()
for raw, kind, stmt in m.raw_declarations(pint, include_private=False):
    name = raw.rsplit(".",1)[-1]
    if has(pub.get(name), kind, stmt) or has(priv.get(m.promoted_key(raw)), kind, stmt):
        continue
    cands = pub.get(name) or priv.get(m.promoted_key(raw)) or priv.get(name)
    if not cands:
        print(f"ABSENT\t{raw}")
    else:
        for ck, cs, cwhere in cands:
            same = (ck == kind and cs == stmt)
            print(f"DIFFERENT\t{raw}\t[{cwhere}]\n   pin : {kind} {stmt}\n   port: {ck} {cs}")
