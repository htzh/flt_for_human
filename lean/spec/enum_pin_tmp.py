import importlib.util, sys
from pathlib import Path
spec = Path("/home/haitao/proj/reasonix-sandbox/flt_for_human/lean/spec/check_flt_statements.py")
s = importlib.util.spec_from_file_location("ck", spec)
m = importlib.util.module_from_spec(s); s.loader.exec_module(m)
flt = Path.home()/"proj"/"fermats-last-theorem"
for rel in sys.argv[1:]:
    t = (flt/rel).read_text()
    for raw, kind, stmt in m.raw_declarations(t, include_private=True):
        print(f"{kind}\t{raw}\t{stmt}")
