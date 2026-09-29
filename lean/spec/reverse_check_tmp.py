"""Reverse check: every public pin declaration of a Def_*.lean has a public
port declaration with the same (kind, normalized statement), by last name or
promoted dotted name. Usage:
  python3 reverse_check_tmp.py <pinrel> <portrel>[;<portrel>...] ...
Relative to pin root and lean root respectively.
"""
import importlib.util, sys
from pathlib import Path

spec = Path("/home/haitao/proj/reasonix-sandbox/flt_for_human/lean/spec/check_flt_statements.py")
s = importlib.util.spec_from_file_location("ck", spec)
m = importlib.util.module_from_spec(s); s.loader.exec_module(m)
flt = Path.home()/"proj"/"fermats-last-theorem"
LEAN = Path("/home/haitao/proj/reasonix-sandbox/flt_for_human/lean")

def collect(paths):
    pub, priv = {}, {}
    for p in paths:
        text = p.read_text()
        for raw, kind, stmt in m.raw_declarations(text):
            pub.setdefault(raw.rsplit(".", 1)[-1], []).append((kind, stmt))
        for raw, kind, stmt in m.raw_declarations(text, include_private=True):
            priv.setdefault(m.promoted_key(raw), []).append((kind, stmt))
            priv.setdefault(raw.rsplit(".", 1)[-1], []).append((kind, stmt))
    return pub, priv

def has(cands, kind, stmt):
    return any(c[0] == kind and c[1] == stmt for c in (cands or ()))

bad = 0
args = sys.argv[1:]
for i in range(0, len(args), 2):
    pinrel, portrels = args[i], args[i+1].split(";")
    pint = (flt/pinrel).read_text()
    pport, ppriv = collect([LEAN/r for r in portrels])
    for raw, kind, stmt in m.raw_declarations(pint, include_private=False):
        name = raw.rsplit(".",1)[-1]
        if has(pport.get(name), kind, stmt) or has(ppriv.get(m.promoted_key(raw)), kind, stmt):
            continue
        print(f"NOT PORTED  {pinrel}: {raw} [{kind}]")
        bad += 1
print(f"done, {bad} pin declarations not found in port")
