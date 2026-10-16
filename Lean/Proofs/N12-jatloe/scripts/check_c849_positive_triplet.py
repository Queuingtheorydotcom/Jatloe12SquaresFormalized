#!/usr/bin/env python3
"""Exact fixed witness audit, not search and not a Lean packing theorem.

Checks why the B/L/C premises alone cannot exclude cases849/851.  The
fourth, upper-left owner is deliberately absent.  No files are written.
"""
from fractions import Fraction as Q


def square(c, s, u, v):
    assert c*c+s*s == 1
    return c, s, u, v


a = Q(1001, 1000)
c, s = Q(209, 241), Q(120, 241)
lv = Q(29963, 24100)
lu = (s/c)*(lv+a)
L = square(c, s, lu, lv)
B = square(c, s, lu+a, Q(565, 482))
C = square(Q(1), Q(0), Q(417, 200), Q(2999, 1000))


def inside(q, point):
    c, s, u, v = q
    x, y = map(Q, point)
    return u < c*x+s*y < u+a and v < -s*x+c*y < v+a


def container(q):
    c, s, u, v = q
    vertices = [(c*U-s*V, s*U+c*V)
                for U in (u, u+a) for V in (v, v+a)]
    return all(0 <= x <= 4 and 0 <= y <= 4 for x, y in vertices)


owned = {
    "L": [("457/500", "2"), ("1", "113/50"), ("1", "12/5")],
    "B": [("33/20", "47/20"), ("8/5", "3"),
          ("87/50", "3"), ("2", "1543/500")],
    "C": [("113/50", "3"), ("213/100", "81/25"),
          ("72/25", "3"), ("3", "1543/500")],
}
missing = {
    "L": [("19/25", "187/100"), ("33/20", "33/20")],
    "B": [("2", "5/2"), ("1", "12/5"), ("1", "1543/500")],
    "C": [("1543/500", "3"), ("2", "1543/500")],
}
for name, q in (("L", L), ("B", B), ("C", C)):
    assert container(q), (name, "container")
    for p in owned[name]:
        assert inside(q, p), (name, "owned", p)
    for p in missing[name]:
        assert not inside(q, p), (name, "missing", p)

# L/B use the same frame and have disjoint open U intervals.
assert L[2]+a == B[2]
# C's least B-U projection exceeds B's greatest B-U projection.
gap = c*C[2]+s*C[3]-(B[2]+a)
assert gap == Q(546547, 50369000) and gap > 0
# L's rightmost x lies strictly left of C.
assert a*(c+s) < C[2]

# Extra reductions retained by the unfinished positive branch.
assert B[2]+a <= Q(113, 50)*c+3*s
assert B[3] == -2*s+Q(5, 2)*c
assert inside(B, ("7/5", "5/2"))
assert inside(L, ("1", "283/100"))
assert c+Q(283, 100)*s <= B[2]
print("Exact B/L/C witness satisfies all recorded local premises; B/C gap:", gap)

# A second fixed construction includes the entire upper-left corner E.
# It remains a local witness, deliberately omitting the actual A and R
# squares; replacing those squares by their known points loses information.
c, s = Q(903, 1145), Q(704, 1145)
L = square(Q(1), Q(0), Q(0), Q(187, 100))
E = square(Q(1), Q(0), Q(0), Q(4)-a)
B = square(c, s, c*a+s*(Q(187, 100)+a), -2*s+Q(5, 2)*c)
cv = 3*c-Q(1543, 500)*s
C = square(c, s, (4-c*(cv+a))/s-a, cv)
owned["E"] = [("457/500", "3"), ("1", "3"), ("1", "1543/500")]
missing["E"] = []
missing["B"] = [*missing["B"], ("1", "3")]
for name, q in (("L", L), ("B", B), ("C", C), ("E", E)):
    assert container(q), ("four", name, "container")
    for p in owned[name]:
        assert inside(q, p), ("four", name, "owned", p)
    for p in missing[name]:
        assert not inside(q, p), ("four", name, "missing", p)
assert B[2] == c*a+s*(L[3]+a)  # L/B longitudinal separation.
assert B[2]+a < C[2]  # B/C same-frame longitudinal separation.
assert B[3]+a < -s*a+c*E[3]  # B/E transverse separation.
assert L[3]+a < E[3]  # L/E vertical separation.
assert a < c*C[2]-s*(C[3]+a)  # Both L and E lie left of C.
assert C[3] == -Q(1543, 500)*s+3*c  # C's remaining lower-V sector.
print("Exact B/L/C/E local witness passed; full A/R geometry remains necessary.")
