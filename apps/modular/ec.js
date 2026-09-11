/* ec.js — exact elliptic-curve arithmetic for the modularity demo app.
 *
 * Everything here is elementary and self-contained (BigInt only, no deps):
 *   - Weierstrass invariants b2,b4,b6,b8,c4,c6,Delta,j
 *   - a minimal integral model, by running Tate's algorithm at every bad
 *     prime (ported from the standard description; see the note for the
 *     connection to the Lean formalisation)
 *   - the conductor N = prod p^{f_p}, Kodaira type, Tamagawa number c_p,
 *     split/non-split multiplicative reduction
 *   - point counts #E(F_p) and traces a_p = p + 1 - #E(F_p)
 *   - the Hecke recursion turning {a_p} into {a_n}, n <= maxN
 *
 * This is a browser file; the same file is require()-able from node for
 * testing (see the module.exports at the bottom).
 */
'use strict';

/* ===================== BigInt helpers ===================== */

function bigAbs(x) { return x < 0n ? -x : x; }

function bmod(x, m) {           // representative in [0, m)
  let r = x % m;
  if (r < 0n) r += m;
  return r;
}

function bgcd(a, b) {
  a = bigAbs(a); b = bigAbs(b);
  while (b) { const t = a % b; a = b; b = t; }
  return a;
}

function bmodinv(a, m) {        // inverse of a mod m, m > 0, gcd(a,m)=1
  let [old_r, r] = [bmod(a, m), m];
  let [old_s, s] = [1n, 0n];
  while (r !== 0n) {
    const q = old_r / r;
    [old_r, r] = [r, old_r - q * r];
    [old_s, s] = [s, old_s - q * s];
  }
  if (old_r !== 1n) throw new Error('not invertible');
  return bmod(old_s, m);
}

function bpowmod(b, e, m) {
  b = bmod(b, m);
  let r = 1n;
  while (e > 0n) {
    if (e & 1n) r = (r * b) % m;
    b = (b * b) % m;
    e >>= 1n;
  }
  return r;
}

/* ===================== integer factorisation ===================== */

const SMALL_PRIMES = (() => {
  const LIMIT = 100000;
  const sieve = new Uint8Array(LIMIT + 1);
  const out = [];
  for (let i = 2; i <= LIMIT; i++) {
    if (!sieve[i]) {
      out.push(BigInt(i));
      for (let j = i * i; j <= LIMIT; j += i) sieve[j] = 1;
    }
  }
  return out;
})();

const MR_BASES = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n];

function isProbablePrime(n) {
  if (n < 2n) return false;
  for (const p of MR_BASES) {
    if (n % p === 0n) return n === p;
  }
  let d = n - 1n, r = 0n;
  while (d % 2n === 0n) { d /= 2n; r += 1n; }
  for (const a of MR_BASES) {
    let x = bpowmod(a, d, n);
    if (x === 1n || x === n - 1n) continue;
    let ok = false;
    for (let i = 1n; i < r; i++) {
      x = (x * x) % n;
      if (x === n - 1n) { ok = true; break; }
    }
    if (!ok) return false;
  }
  return true;
}

// Brent's variant of Pollard's rho.  Throws if it does not split n in
// `maxTries` polynomial attempts, so the caller can report a clean error
// instead of hanging on an adversarial input.
function pollardRho(n, maxTries) {
  if (n % 2n === 0n) return 2n;
  if (n % 3n === 0n) return 3n;
  const tries = maxTries || 300;
  for (let c = 1n; c <= BigInt(tries); c++) {
    let y = 2n, m = 128n, g = 1n, r = 1n, q = 1n;
    let x = 0n, ys = 0n;
    while (g === 1n) {
      x = y;
      for (let i = 0n; i < r; i++) y = (y * y + c) % n;
      let k = 0n;
      while (k < r && g === 1n) {
        ys = y;
        const lim = (m < r - k) ? m : r - k;
        for (let i = 0n; i < lim; i++) {
          y = (y * y + c) % n;
          q = (q * bigAbs(x - y)) % n;
        }
        g = bgcd(q, n);
        k += lim;
      }
      r <<= 1n;
    }
    if (g === n) {
      g = 1n;
      y = ys;
      while (g === 1n) { y = (y * y + c) % n; g = bgcd(bigAbs(x - y), n); }
    }
    if (g !== n) return g;
  }
  throw new Error('factorisation failed on ' + n.toString() +
    ' — the coefficients are too large for this in-browser demo');
}

// factorize(n) -> Map<BigInt, Number>, for n != 0. Sign is ignored.
function factorize(n) {
  n = bigAbs(n);
  const fac = new Map();
  const add = (p, e) => fac.set(p, (fac.get(p) || 0) + e);
  for (const p of SMALL_PRIMES) {
    if (p * p > n) break;
    while (n % p === 0n) { add(p, 1); n /= p; }
  }
  const stack = [];
  if (n > 1n) stack.push(n);
  while (stack.length) {
    const m = stack.pop();
    if (m === 1n) continue;
    if (isProbablePrime(m)) { add(m, 1); continue; }
    const d = pollardRho(m);          // throws if m resists factorisation
    stack.push(d, m / d);
  }
  return fac;
}

function factorString(fac) {
  const parts = [];
  const keys = [...fac.keys()].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
  for (const p of keys) {
    const e = fac.get(p);
    parts.push(e === 1 ? `${p}` : `${p}^${e}`);
  }
  return parts.length ? parts.join(' * ') : '1';
}

/* ===================== Weierstrass invariants ===================== */

// a = [a1, a2, a3, a4, a6] as BigInt
function invariants(a) {
  const [a1, a2, a3, a4, a6] = a;
  const b2 = a1 * a1 + 4n * a2;
  const b4 = 2n * a4 + a1 * a3;
  const b6 = a3 * a3 + 4n * a6;
  const b8 = a1 * a1 * a6 + 4n * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4;
  const c4 = b2 * b2 - 24n * b4;
  const c6 = -b2 * b2 * b2 + 36n * b2 * b4 - 216n * b6;
  const Delta = -b2 * b2 * b8 - 8n * b4 * b4 * b4 - 27n * b6 * b6 + 9n * b2 * b4 * b6;
  return { b2, b4, b6, b8, c4, c6, Delta };
}

// x = u^2 x' + r, y = u^3 y' + s u^2 x' + t, with u = 1.
function rstTransform(a, r, s, t) {
  const [a1, a2, a3, a4, a6] = a;
  const na1 = a1 + 2n * s;
  const na2 = a2 - s * a1 + 3n * r - s * s;
  const na3 = a3 + r * a1 + 2n * t;
  const na4 = a4 - s * a3 + 2n * r * a2 - (t + r * s) * a1 + 3n * r * r - 2n * s * t;
  const na6 = a6 + r * a4 + r * r * a2 + r * r * r - t * a3 - t * t - r * t * a1;
  return [na1, na2, na3, na4, na6];
}

/* ===================== small modular arithmetic ===================== */

function powmodNum(b, e, m) {
  b = ((b % m) + m) % m;
  let r = 1;
  while (e > 0) {
    if (e & 1) r = (r * b) % m;
    b = (b * b) % m;
    e >>= 1;
  }
  return r;
}

function modinvNum(x, p) {
  x = ((x % p) + p) % p;
  if (x === 0) throw new Error('division by 0 mod ' + p);
  let [or, r] = [x, p], [os, s] = [1, 0];
  while (r !== 0) {
    const q = Math.floor(or / r);
    [or, r] = [r, or - q * r];
    [os, s] = [s, os - q * s];
  }
  return ((os % p) + p) % p;
}

function isSquareMod(a, p) {
  a = ((a % p) + p) % p;
  if (a === 0) return true;
  if (p === 2) return true;
  return powmodNum(a, (p - 1) / 2, p) === 1;
}

// Does a X^2 + b X + c have a root in F_p?
function pquadroots(a, b, c, p) {
  a = ((a % p) + p) % p; b = ((b % p) + p) % p; c = ((c % p) + p) % p;
  if (a === 0) return b !== 0 || c === 0;
  if (p === 2) {
    for (let x = 0; x < 2; x++) if ((a * x * x + b * x + c) % 2 === 0) return true;
    return false;
  }
  return isSquareMod(b * b - 4 * a * c, p);
}

function evalPolyNum(coeffs, x, p) {          // coeffs highest degree first
  let v = 0;
  for (const c of coeffs) v = (v * x + c) % p;
  return ((v % p) + p) % p;
}

function divLinearNum(coeffs, x, p) {         // divide by (X - x); drops remainder
  const n = coeffs.length - 1;
  if (n < 1) return [];
  const q = new Array(n);
  q[0] = coeffs[0];
  for (let i = 1; i < n; i++) q[i] = (coeffs[i] + q[i - 1] * x) % p;
  return q;
}

// number of roots in F_p of X^3 + b X^2 + c X + d, counted with multiplicity
function pcubicroots(b, c, d, p) {
  b = ((b % p) + p) % p; c = ((c % p) + p) % p; d = ((d % p) + p) % p;
  let count = 0;
  for (let x = 0; x < p; x++) {
    if (evalPolyNum([1, b, c, d], x, p) !== 0) continue;
    let m = 1;
    let q = divLinearNum([1, b, c, d], x, p);
    while (q.length > 0 && evalPolyNum(q, x, p) === 0) {
      m += 1;
      q = divLinearNum(q, x, p);
    }
    count += m;
  }
  return count;
}

/* ===================== Tate's algorithm at one prime ===================== */

// a: integral model [a1,a2,a3,a4,a6] (BigInt); p: Number (prime).
// Returns { model, valDisc, fp, kodaira, redType, split, cp }.
function tateLocal(aIn, p) {
  const P = BigInt(p);
  let a = aIn.slice();

  const pval = (x) => {
    if (x === 0n) return Infinity;
    let y = bigAbs(x), c = 0;
    while (y % P === 0n) { y /= P; c++; }
    return c;
  };
  const pdiv = (x) => x === 0n || pval(x) > 0;
  const red = (x) => Number(bmod(x, P));
  const proot = (x, e) => {
    const t = ((x % p) + p) % p;
    for (let v = 0; v < p; v++) if (powmodNum(v, e, p) === t) return v;
    return null;
  };
  const halfmodp = p === 2 ? 0 : modinvNum(2, p);
  const pinv = (x) => modinvNum(x, p);

  let guard = 0;
  while (true) {
    if (++guard > 100) throw new Error('Tate: no termination at p=' + p);
    const inv = invariants(a);
    const valDisc = pval(inv.Delta);
    const [a1, a2, a3, a4, a6] = a;
    const { b2, b4, b6, b8, c4, c6 } = inv;

    if (valDisc === 0) {
      return { model: a, valDisc: 0, fp: 0, kodaira: 'I0', redType: 'good', split: null, cp: 1 };
    }

    // (1) first transform: make p | a3, a4, a6
    let r, t;
    if (p === 2) {
      if (pdiv(b2)) {
        r = proot(red(a4), 2);
        t = proot(red(((BigInt(r) + a2) * BigInt(r) + a4) * BigInt(r) + a6), 2);
      } else {
        const temp = pinv(red(a1));
        r = (temp * red(a3)) % p;
        t = (temp * (red(a4) + r * r)) % p;
      }
    } else if (p === 3) {
      if (pdiv(b2)) r = proot(red(-b6), 3);
      else r = (((-pinv(red(b2)) * red(b4)) % p) + p) % p;
      t = (red(a1) * r + red(a3)) % p;
    } else {
      if (pdiv(c4)) r = (((-pinv(12) * red(b2)) % p) + p) % p;
      else r = (((-pinv((12 * red(c4)) % p) * ((red(c6) + red(b2) * red(c4)) % p)) % p) + p) % p;
      t = (((-halfmodp * ((red(a1) * r + red(a3)) % p)) % p) + p) % p;
    }
    a = rstTransform(a, BigInt(r), 0n, BigInt(t));

    const inv2 = invariants(a);
    if (!pdiv(inv2.c4)) {
      // multiplicative reduction, type I_n
      const split = pquadroots(1, red(a[0]), red(-a[1]), p);
      let cp;
      if (split) cp = valDisc;
      else if (valDisc % 2 === 0) cp = 2;
      else cp = 1;
      return { model: a, valDisc, fp: 1, kodaira: 'I' + valDisc, redType: 'multiplicative', split, cp };
    }
    if (pval(a[4]) < 2) {
      return { model: a, valDisc, fp: valDisc, kodaira: 'II', redType: 'additive', split: null, cp: 1 };
    }
    if (pval(inv2.b8) < 3) {
      return { model: a, valDisc, fp: valDisc - 1, kodaira: 'III', redType: 'additive', split: null, cp: 2 };
    }
    if (pval(inv2.b6) < 3) {
      const a3t = red(a[2] / P), a6t = red(a[4] / (P * P));
      const cp = pquadroots(1, a3t, -a6t, p) ? 3 : 1;
      return { model: a, valDisc, fp: valDisc - 2, kodaira: 'IV', redType: 'additive', split: null, cp };
    }

    // (2) second transform: p | a1,a2; p^2 | a3,a4; p^3 | a6.
    // NB: unlike the first transform, s and t are NOT reduced mod p here.
    let s2, t2;
    if (p === 2) {
      s2 = BigInt(proot(red(a[1]), 2));
      t2 = P * BigInt(proot(red(a[4] / (P * P)), 2));   // so t^2 = a6 (mod p^3)
    } else if (p === 3) {
      s2 = a[0];                                        // a1' = 2s + a1 = 3a1 = 0
      t2 = a[2];                                        // a3' = 2t + a3 = 3a3 = 0
    } else {
      s2 = -a[0] * BigInt(halfmodp);
      t2 = -a[2] * BigInt(halfmodp);
    }
    a = rstTransform(a, 0n, s2, t2);

    // cubic T^3 + b T^2 + c T + d
    const b = red(a[1] / P);
    const c = red(a[3] / (P * P));
    const d = red(a[4] / (P * P * P));
    const bb = (b * b) % p, cc = (c * c) % p, bc = (b * c) % p;
    const w = ((27 * d * d - bb * cc + 4 * b * bb * d - 18 * bc * d + 4 * c * cc) % p + p) % p;
    const x = ((3 * c - bb) % p + p) % p;
    const sw = w === 0 ? (x === 0 ? 3 : 2) : 1;

    if (sw === 1) {
      const cp = 1 + pcubicroots(b, c, d, p);
      return { model: a, valDisc, fp: valDisc - 4, kodaira: 'I0*', redType: 'additive', split: null, cp };
    }

    if (sw === 2) {
      // one double root: move it to T = 0
      let r2;
      if (p === 2) r2 = proot(c, 2);
      else if (p === 3) r2 = (c * pinv(b)) % p;
      else r2 = (((b * c - 9 * d) * pinv((2 * x) % p)) % p + p) % p;
      a = rstTransform(a, P * BigInt(r2), 0n, 0n);

      let ix = 3, iy = 3;
      let mx = P * P, my = mx;
      let cp;
      let innerGuard = 0;
      while (true) {
        if (++innerGuard > 200) {
          throw new Error('Tate I_n*: no termination at p=' + p);
        }
        const a2t = red(a[1] / P);
        const a3t = red(a[2] / my);
        const a4t = red(a[3] / (P * mx));
        const a6t = red(a[4] / (mx * my));
        if (((a3t * a3t + 4 * a6t) % p + p) % p === 0) {
          let t3;
          if (p === 2) t3 = my * BigInt(proot(a6t, 2));
          else t3 = my * BigInt(((-a3t * halfmodp) % p + p) % p);
          a = rstTransform(a, 0n, 0n, t3);
          my *= P; iy += 1;

          const a2t2 = red(a[1] / P);
          const a3t2 = red(a[2] / my);
          const a4t2 = red(a[3] / (P * mx));
          const a6t2 = red(a[4] / (mx * my));
          if (((a4t2 * a4t2 - 4 * a6t2 * a2t2) % p + p) % p === 0) {
            let r3;
            if (p === 2) {
              r3 = a2t2 === 0 ? 0 : mx * BigInt(proot((a6t2 * pinv(a2t2)) % p, 2));
            } else {
              r3 = a2t2 === 0 ? 0 : mx * BigInt(((-a4t2 * pinv((2 * a2t2) % p)) % p + p) % p);
            }
            a = rstTransform(a, r3, 0n, 0n);
            mx *= P; ix += 1;
          } else {
            cp = pquadroots(a2t2, a4t2, a6t2, p) ? 4 : 2;
            break;
          }
        } else {
          cp = pquadroots(1, a3t, -a6t, p) ? 4 : 2;
          break;
        }
      }
      return {
        model: a, valDisc, fp: valDisc - ix - iy + 1,
        kodaira: 'I' + (ix + iy - 5) + '*', redType: 'additive', split: null, cp
      };
    }

    // sw === 3: triple root
    let r4;
    if (p === 2) r4 = b;
    else if (p === 3) r4 = proot((-d % p + p) % p, 3);
    else r4 = (((-b * pinv(3)) % p) + p) % p;
    a = rstTransform(a, P * BigInt(r4), 0n, 0n);

    const a3t = red(a[2] / (P * P));
    const a6t = red(a[4] / (P * P * P * P));
    if (((a3t * a3t + 4 * a6t) % p + p) % p !== 0) {
      const cp = pquadroots(1, a3t, -a6t, p) ? 3 : 1;
      return { model: a, valDisc, fp: valDisc - 6, kodaira: 'IV*', redType: 'additive', split: null, cp };
    }

    let t5;
    if (p === 2) t5 = -P * P * BigInt(proot(a6t, 2));
    else t5 = P * P * BigInt(((-a3t * halfmodp) % p + p) % p);
    a = rstTransform(a, 0n, 0n, t5);

    if (pval(a[3]) < 4) {
      return { model: a, valDisc, fp: valDisc - 7, kodaira: 'III*', redType: 'additive', split: null, cp: 2 };
    }
    if (pval(a[4]) < 6) {
      return { model: a, valDisc, fp: valDisc - 8, kodaira: 'II*', redType: 'additive', split: null, cp: 1 };
    }
    // not minimal at p: divide out by u = p and go round again
    a = [a[0] / P, a[1] / (P * P), a[2] / (P * P * P), a[3] / (P * P * P * P), a[4] / (P ** 6n)];
  }
}

/* ===================== global minimal model ===================== */

function pvalBig(x, p) {
  if (x === 0n) return Infinity;
  const P = BigInt(p);
  let y = bigAbs(x), c = 0;
  while (y % P === 0n) { y /= P; c++; }
  return c;
}

function minimalModel(aIn, maxFactor) {
  const limit = maxFactor || 1000000;
  if (invariants(aIn).Delta === 0n) throw new Error('the discriminant is 0: this equation is singular, not an elliptic curve');
  // Stage 1: minimalise prime by prime.  Only replace the model when the
  // local minimal discriminant valuation actually drops, so an already
  // minimal input is returned untouched (the cosmetic u=1 transforms that
  // Tate's algorithm performs internally are discarded).
  let model = aIn.slice();
  const primes0 = [...factorize(invariants(model).Delta).keys()].map(Number)
    .filter((p) => p <= limit).sort((x, y) => x - y);
  for (const p of primes0) {
    const cur = pvalBig(invariants(model).Delta, p);
    const loc = tateLocal(model, p);
    if (loc.valDisc < cur) model = loc.model;
  }
  // Stage 2: read off the local data from the final, minimal model.
  const bad = factorize(invariants(model).Delta);
  const steps = [];
  for (const pBig of [...bad.keys()].map(Number).filter((p) => p <= limit).sort((x, y) => x - y)) {
    const loc = tateLocal(model, pBig);
    steps.push({
      p: pBig,
      valDisc: loc.valDisc,
      fp: loc.fp,
      kodaira: loc.kodaira,
      redType: loc.redType,
      split: loc.split,
      cp: loc.cp
    });
  }
  return { model, steps, badPrimes: [...bad.keys()] };
}

/* ===================== point counts and a_p ===================== */

function countPoints(a, p) {
  const A = a.map((x) => Number(bmod(x, BigInt(p))));
  const [a1, a2, a3, a4, a6] = A;
  let count = 0;
  for (let x = 0; x < p; x++) {
    const x3 = (((x * x) % p) * x) % p;
    const rhs = (x3 + a2 * x * x + a4 * x + a6) % p;
    for (let y = 0; y < p; y++) {
      const lhs = (y * y + a1 * x * y + a3 * y) % p;
      if (lhs === rhs) count++;
    }
  }
  return count + 1;                       // the point at infinity
}

function traceOfFrobenius(a, p) {
  return p + 1 - countPoints(a, p);
}

// local a_p of the weight-2 eigenform attached to a semistable E
function localAp(step) {
  if (step.redType === 'multiplicative') return step.split ? 1 : -1;
  if (step.redType === 'additive') return 0;
  return null;                            // good: use the point count
}

function isPrimeNum(n) {
  if (n < 2) return false;
  for (let d = 2; d * d <= n; d++) if (n % d === 0) return false;
  return true;
}

function primesUpTo(n) {
  const out = [];
  for (let p = 2; p <= n; p++) if (isPrimeNum(p)) out.push(p);
  return out;
}

// a_p for every prime p <= maxN: point count at good primes, local factor at bad
function apTable(model, steps, maxN) {
  const bad = new Map();
  for (const st of steps) if (st.redType !== 'good') bad.set(st.p, st);
  const table = new Map();
  for (const p of primesUpTo(maxN)) {
    if (bad.has(p)) table.set(p, localAp(bad.get(p)));
    else table.set(p, traceOfFrobenius(model, p));
  }
  return table;
}

/* ===================== Hecke recursion ===================== */

function factorNum(n) {                 // -> Map<number, number>
  const f = new Map();
  let m = n;
  for (let d = 2; d * d <= m; d++) {
    while (m % d === 0) { f.set(d, (f.get(d) || 0) + 1); m /= d; }
  }
  if (m > 1) f.set(m, (f.get(m) || 0) + 1);
  return f;
}

// Reconstruct a_1..a_maxN from the a_p table using the IsNormalizedEigenform
// clauses.  Returns { coeffs: Map<n, BigInt>, rules: Map<n, string> }.
function eigenCoeffs(aps, N, maxN) {
  const badSet = new Set([...aps.keys()].filter((p) => N % p === 0));
  const coeffs = new Map();
  const rules = new Map();
  coeffs.set(1, 1n);
  rules.set(1, 'normalisation: a_1 = 1');

  const apPow = new Map();               // p -> Map<e, BigInt>
  function primePower(p, e) {
    let byE = apPow.get(p);
    if (!byE) { byE = new Map(); apPow.set(p, byE); }
    if (byE.has(e)) return byE.get(e);
    const ap = BigInt(aps.get(p));
    if (e === 0) { byE.set(0, 1n); return 1n; }
    if (e === 1) { byE.set(1, ap); return ap; }
    const prev1 = primePower(p, e - 1);
    const prev2 = primePower(p, e - 2);
    let next;
    if (!badSet.has(p)) next = ap * prev1 - BigInt(p) * prev2;
    else next = ap * prev1;
    byE.set(e, next);
    return next;
  }

  for (let n = 2; n <= maxN; n++) {
    const f = factorNum(n);
    let value = 1n;
    const parts = [];
    for (const [p, e] of f) {
      const v = primePower(p, e);
      value *= v;
      parts.push(`a_{${p}^${e}}`);
    }
    coeffs.set(n, value);
    if (f.size === 1) {
      const [p, e] = [...f.entries()][0];
      if (e === 1) {
        rules.set(n, badSet.has(p)
          ? `a_${p} = ${aps.get(p)}  (local factor at the bad prime ${p})`
          : `a_${p} = ${p} + 1 - #E(F_${p})`);
      } else {
        const ap = aps.get(p);
        if (!badSet.has(p)) {
          rules.set(n,
            `a_{${p}^${e}} = a_${p} * a_{${p}^${e - 1}} - ${p} * a_{${p}^${e - 2}}` +
            `  = ${ap} * ${coeffs.get(p ** (e - 1))} - ${p} * ${coeffs.get(p ** (e - 2))}`);
        } else {
          rules.set(n,
            `a_{${p}^${e}} = a_${p} * a_{${p}^${e - 1}}` +
            `  = ${ap} * ${coeffs.get(p ** (e - 1))}`);
        }
      }
    } else {
      rules.set(n, `a_${n} = ${parts.join(' * ')}  (multiplicativity, coprime factors)`);
    }
  }
  return { coeffs, rules };
}

/* ===================== eta-product reference (level 11) ===================== */

// q * prod (1-q^n)^2 (1-q^{11n})^2  =  the level-11 newform 11.2.a.a,
// an independent q-expansion to check the point-count reconstruction against.
function eta11(maxN) {
  let P = [1];
  for (let n = 1; n <= maxN; n++) {
    const Q = P.slice();
    while (Q.length < P.length + n) Q.push(0);
    for (let i = 0; i < P.length; i++) Q[i + n] -= P[i];
    P = Q;
  }
  // multiply by (1 - q^11), then square
  const with11 = P.slice();
  while (with11.length < P.length + 11) with11.push(0);
  for (let i = 0; i < P.length; i++) with11[i + 11] -= P[i];
  const sq = new Array(2 * with11.length).fill(0);
  for (let i = 0; i < with11.length; i++)
    for (let j = 0; j < with11.length; j++) sq[i + j] += with11[i] * with11[j];
  const out = new Map();
  for (let n = 1; n <= maxN; n++) out.set(n, BigInt(sq[n - 1] || 0));
  return out;
}

/* ===================== rational j-invariant ===================== */

function gcdBig(a, b) { return bgcd(a, b); }

function jInvariant(inv) {
  const num = inv.c4 * inv.c4 * inv.c4;
  const den = inv.Delta;
  if (den === 0n) return null;
  const g = gcdBig(bigAbs(num), bigAbs(den));
  let n = num / g, d = den / g;
  if (d < 0n) { n = -n; d = -d; }
  return { n, d };
}

/* ===================== exports ===================== */

const EC = {
  bigAbs, bmod, bgcd, bmodinv, bpowmod,
  factorize, factorString, isProbablePrime,
  invariants, rstTransform,
  tateLocal, minimalModel,
  countPoints, traceOfFrobenius, apTable, localAp, primesUpTo,
  eigenCoeffs, factorNum, eta11, jInvariant
};

if (typeof module !== 'undefined' && module.exports) module.exports = EC;
if (typeof window !== 'undefined') window.EC = EC;
