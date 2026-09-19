"""Elliptic curves over a finite field, and Miller's Weil pairing.

sympy has no finite-field elliptic curve and no Weil pairing, so this is the one
layer ``pymath`` supplies itself.  It is deliberately thin: every field operation
comes from ``ffcurve.fields.FiniteField`` (sympy), and this module only has the
group law and Miller's algorithm.

Points are ``None`` (the identity) or ``(x, y)`` tuples of field elements.
Curves are short Weierstrass, ``y^2 = x^3 + a*x + b``.
"""

from ffcurve.fields import FiniteField


class EllipticCurve:
    def __init__(self, F, a, b):
        self.F = F
        self.a = F.from_int(a) if isinstance(a, int) else a
        self.b = F.from_int(b) if isinstance(b, int) else b
        disc = F.add(F.mul(F.from_int(4), F.pow(self.a, 3)),
                     F.mul(F.from_int(27), F.pow(self.b, 2)))
        assert not F.eq(disc, F.zero()), "singular curve (4a^3 + 27b^2 = 0)"

    def __repr__(self):
        F = self.F
        return f"y^2 = x^3 + ({F.format(self.a)})*x + ({F.format(self.b)}) over {F!r}"

    # -- group law ------------------------------------------------------

    def is_on(self, P):
        if P is None:
            return True
        x, y = P
        F = self.F
        return F.eq(F.mul(y, y),
                    F.add(F.add(F.pow(x, 3), F.mul(self.a, x)), self.b))

    def neg(self, P):
        if P is None:
            return None
        return (P[0], self.F.neg(P[1]))

    def add(self, P, Q):
        F = self.F
        if P is None:
            return Q
        if Q is None:
            return P
        x1, y1 = P
        x2, y2 = Q
        if F.eq(x1, x2):
            if F.eq(y1, F.neg(y2)):
                return None
            lam = F.div(F.add(F.mul(F.from_int(3), F.pow(x1, 2)), self.a),
                        F.mul(F.from_int(2), y1))
        else:
            lam = F.div(F.sub(y2, y1), F.sub(x2, x1))
        x3 = F.sub(F.sub(F.pow(lam, 2), x1), x2)
        y3 = F.sub(F.mul(lam, F.sub(x1, x3)), y1)
        return (x3, y3)

    def mul(self, n, P):
        if n < 0:
            return self.mul(-n, self.neg(P))
        R, Q = None, P
        while n:
            if n & 1:
                R = self.add(R, Q)
            Q = self.add(Q, Q)
            n >>= 1
        return R

    # -- finite group ---------------------------------------------------

    def points(self):
        """All F-rational points, identity included."""
        F = self.F
        pts = [None]
        for x in F.elements():
            rhs = F.add(F.add(F.pow(x, 3), F.mul(self.a, x)), self.b)
            for y in F.elements():
                if F.eq(F.mul(y, y), rhs):
                    pts.append((x, y))
        return pts

    def cardinality(self):
        return len(self.points())

    def order(self, P):
        """Order of P, by brute force (groups here are tiny)."""
        if P is None:
            return 1
        R, n = P, 1
        while R is not None:
            R = self.add(R, P)
            n += 1
            if n > 10 ** 6:
                raise RuntimeError("order too large for brute force")
        return n

    def torsion_basis(self, n):
        """A basis (P, Q) of E[n], or None if E[n] is not F-rational."""
        tors = [P for P in self.points() if self.mul(n, P) is None]
        if len(tors) != n * n:
            return None
        P = next((T for T in tors if T is not None and self.order(T) == n), None)
        if P is None:
            return None
        sub = {self.mul(k, P) for k in range(n)}
        Q = next((T for T in tors if T not in sub), None)
        if Q is None:
            return None
        return P, Q

    # -- Miller's algorithm and the Weil pairing ------------------------

    def _line(self, A, B, R):
        """Value at R of the line through A, B (tangent when A == B)."""
        F = self.F
        xR, yR = R
        if A is None or B is None:
            return F.one()
        xA, yA = A
        xB, yB = B
        if F.eq(xA, xB) and F.eq(yA, F.neg(yB)):
            return F.sub(xR, xA)  # vertical
        if A == B:
            lam = F.div(F.add(F.mul(F.from_int(3), F.pow(xA, 2)), self.a),
                        F.mul(F.from_int(2), yA))
        else:
            lam = F.div(F.sub(yB, yA), F.sub(xB, xA))
        return F.sub(F.sub(yR, yA), F.mul(lam, F.sub(xR, xA)))

    def _vertical(self, C, R):
        F = self.F
        if C is None:
            return F.one()
        return F.sub(R[0], C[0])

    def miller(self, P, Q, n):
        """f_{n,P}(Q) for div(f_{n,P}) = n[P] - n[O] (up to a scalar)."""
        F = self.F
        assert P is not None and Q is not None
        T, f = P, F.one()
        for bit in bin(n)[2:][1:]:
            f = F.mul(F.mul(f, f),
                      F.div(self._line(T, T, Q), self._vertical(self.add(T, T), Q)))
            T = self.add(T, T)
            if bit == "1":
                f = F.mul(f,
                          F.div(self._line(T, P, Q), self._vertical(self.add(T, P), Q)))
                T = self.add(T, P)
        return f

    def weil_pairing(self, P, Q, n):
        """e_n(P,Q) = (-1)^n f_{n,P}(Q) / f_{n,Q}(P).

        Miller's formula needs P, Q to generate a rank-2 subgroup.  If Q lies in
        <P> the pairing is 1, which is returned directly so that the alternating
        law e_n(R,R) = 1 holds for every R in E[n].
        """
        F = self.F
        if P is None or Q is None:
            return F.one()
        R = None
        for _ in range(n):
            if R == Q:
                return F.one()
            R = self.add(R, P)
        e = F.div(self.miller(P, Q, n), self.miller(Q, P, n))
        return F.neg(e) if n % 2 == 1 else e
