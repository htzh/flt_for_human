#!/usr/bin/env bash
# Manager's SET-M1 review harness (read-only). Run from the repo root.
# Usage: bash .recon/review-setm1.sh
set -u
cd "$(dirname "$0")/.." || exit 1
LEAN=lean; PORT=$LEAN/FLTForHuman

echo "== date =="; date
echo
echo "== new modules (SET-M1: m1 defs, m2 defs, m3 analytic) =="
for f in \
  $PORT/ModularCurve/Defs/HeckeOperator.lean \
  $PORT/ModularCurve/Defs/DegeneracyTower.lean \
  $PORT/ModularCurve/Defs/HeckeTotal.lean \
  $PORT/ModularCurve/Defs/HeckeModule.lean \
  $PORT/ModularCurve/Defs/ArithmeticGalois.lean \
  $PORT/ModularCurve/Defs/GeometricBaseChange.lean \
  $PORT/ModularCurve/Defs/QAdicPlace.lean \
  $PORT/ModularCurve/Defs/CuspidalClass.lean \
  $PORT/ModularCurve/Defs/AtkinLehner.lean \
  $PORT/ModularCurve/Defs/ModularUnit.lean \
  $PORT/ModularCurve/Defs/JqCoeff.lean \
  $PORT/ModularCurve/Analytic/QParamUnique.lean \
  $PORT/ModularCurve/Analytic/ModularUnitQExpansion.lean \
  $PORT/ModularCurve/Analytic/Gamma0Cosets.lean ; do
  if [ -f "$f" ]; then
    printf "%-72s %5s lines  %4s decls  sorry=%s\n" "${f#$PORT/}" \
      "$(wc -l < "$f")" \
      "$(grep -cE '^\s*(theorem|lemma|def|abbrev|structure|instance|private)' "$f")" \
      "$(grep -c 'sorry\|admit' "$f")"
  else
    printf "%-72s MISSING\n" "${f#$PORT/}"
  fi
done
echo
echo "== real sorry/admit (comments excluded) =="
python3 - "$PORT" <<'PY'
import re, sys
from pathlib import Path
bad = []
for p in Path(sys.argv[1]).rglob('*.lean'):
    for i, line in enumerate(p.read_text(encoding='utf-8').splitlines(), 1):
        code = re.sub(r'--.*$', '', line)          # strip line comments
        if re.search(r'(?<![\w`])sorry(?![\w])', code) or re.search(r'(?<![\w`])admit(?![\w])', code):
            bad.append(f"{p}:{i}: {line.strip()}")
print(len(bad), "real occurrences")
for b in bad: print("  ", b)
PY
echo
echo "== statement checker =="
( cd $LEAN && timeout 300 python3 spec/check_flt_statements.py 2>&1 | tail -3 )
echo
echo "== dedup evidence (must be 0 = never re-written) =="
echo -n "laurentBaseChange_mono re-declared (expect 1: the promoted public one): "
grep -rn 'theorem laurentBaseChange_mono' $PORT --include='*.lean' | wc -l
echo -n "qExpand_mem_laurentBaseChange re-declared (expect 1): "
grep -rn 'theorem qExpand_mem_laurentBaseChange' $PORT --include='*.lean' | wc -l
echo -n "TS/conj prelude re-declared in the m3 analytic modules (expect 0): "
grep -rn 'theorem conj_zero_eq\|theorem roots_prime_at_slot\|def phiAtSeed' $PORT/ModularCurve/Analytic --include='*.lean' 2>/dev/null | wc -l
echo -n "modularunit hasSum prelude declarations (expect 1 module): "
grep -rln 'hasSum_modularUnit\b\|private theorem hasSum_modularUnit' $PORT/ModularCurve/Analytic --include='*.lean' 2>/dev/null | wc -l
echo
echo "== consumer =="
if [ -f $LEAN/spec/ModularCurveHeckeConsumer.lean ]; then
  echo "consumer exists: $(wc -l < $LEAN/spec/ModularCurveHeckeConsumer.lean) lines"
else
  echo "consumer MISSING"
fi
