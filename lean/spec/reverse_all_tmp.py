"""Reverse check against the whole port tree. Usage:
  python3 reverse_all_tmp.py <pinrel> [<pinrel> ...]
Reports every public pin declaration with no (kind, stmt)-identical public
declaration anywhere under FLTForHuman (by last name or promoted dotted key).
"""
import importlib.util, sys
from pathlib import Path

spec = Path("/home/haitao/proj/reasonix-sandbox/flt_for_human/lean/spec/check_flt_statements.py")
s = importlib.util.spec_from_file_location("ck", spec)
m = importlib.util.module_from_spec(s); s.loader.exec_module(m)
flt = Path.home()/"proj"/"fermats-last-theorem"
LEAN = Path("/home/haitao/proj/reasonix-sandbox/flt_for_human/lean")

pub, priv = {}, {}
for p in sorted((LEAN/"FLTForHuman").rglob("*.lean")):
    text = p.read_text()
    for raw, kind, stmt in m.raw_declarations(text):
        pub.setdefault(raw.rsplit(".", 1)[-1], []).append((kind, stmt))
    for raw, kind, stmt in m.raw_declarations(text, include_private=True):
        priv.setdefault(m.promoted_key(raw), []).append((kind, stmt))
        priv.setdefault(raw.rsplit(".", 1)[-1], []).append((kind, stmt))

def has(cands, kind, stmt):
    return any(c[0] == kind and c[1] == stmt for c in (cands or ()))

for pinrel in sys.argv[1:]:
    pint = (flt/pinrel).read_text()
    print(f"### {pinrel}")
    for raw, kind, stmt in m.raw_declarations(pint, include_private=False):
        name = raw.rsplit(".",1)[-1]
        if has(pub.get(name), kind, stmt) or has(priv.get(m.promoted_key(raw)), kind, stmt):
            continue
        print(f"NOT PORTED  {raw} [{kind}]")
