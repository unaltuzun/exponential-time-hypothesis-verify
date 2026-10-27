#!/usr/bin/env python3
"""
Independent small-instance reproduction of the core mechanism of
"The Exponential Time Hypothesis is False" (OpenAI, Oct 25 2026), Sections 2 and 4.

This tests CORRECTNESS of the identities (not running time):
  Part A  (Sec 4.2, Lemmas swaps-matrix / swaps-support / swaps-forms):
          M0 = V0 f_I(W0) fixes ker C^B; support of M0 is confined to <= R-1 mismatches;
          rows P_u(T) have deg <= R-1, P_u(0) = delta_u, and separate at each t in [Q].
  Part B  (Sec 2, Lemma measurement-separation, Lemma boolean-differences, Hermite recovery):
          on a random 3-CNF with <= 3 occurrences per variable, the deformed count H(T)
          satisfies H(0) = #F; the Taylor coefficients at t=1..Q computed by the
          *separated* (measurement-fixing + inclusion-exclusion) routine equal the
          brute-force ones; Hermite interpolation recovers #F exactly.
All arithmetic is exact (fractions.Fraction). Usage: python3 -I mechanism_test.py [seed]
"""
import sys, itertools, random
from fractions import Fraction as Fr
from math import comb

# ---------------------------------------------------------------- polynomials
def padd(a, b):
    n = max(len(a), len(b)); return [ (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pscale(a, c): return [c*x for x in a]
def pmul(a, b, trunc=None):
    out = [Fr(0)]*(len(a)+len(b)-1 if a and b else 0)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b):
            if trunc is not None and i+j >= trunc: break
            out[i+j] += x*y
    if trunc is not None: out = out[:trunc]
    return out
def peval(a, t):
    s = Fr(0)
    for c in reversed(a): s = s*t + c
    return s
def pdeg(a):
    d = len(a)-1
    while d >= 0 and a[d] == 0: d -= 1
    return d
def pshift(a, t):
    """coefficients of a(t+z) as polynomial in z"""
    out = [Fr(0)]*len(a)
    for i, c in enumerate(a):
        for j in range(i+1):
            out[j] += c*comb(i, j)*Fr(t)**(i-j)
    return out

# ---------------------------------------------------------------- linear algebra over Q
def rank(rows):
    rows = [list(map(Fr, r)) for r in rows]; rk = 0
    if not rows: return 0
    ncol = len(rows[0])
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] != 0), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        pv = rows[rk][c]; rows[rk] = [x/pv for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] != 0:
                f = rows[i][c]; rows[i] = [x - f*y for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk
def in_rowspace(v, rows):
    return rank(rows + [v]) == rank(rows)
def solve(A, b):
    """solve square system A x = b over Q (Gauss-Jordan)."""
    n = len(A); M = [list(map(Fr, A[i])) + [Fr(b[i])] for i in range(n)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]; M[c] = [x/pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f*y for x, y in zip(M[i], M[c])]
    return [M[i][n] for i in range(n)]

# ================================================================ PART A: Section 4.2 construction
def build_auxiliary(r, Q, R):
    pairs = [(a, d) for a in range(r) for d in range(r)]
    B = list(itertools.product(pairs, repeat=Q))          # labels u = ((a1,d1),...,(aQ,dQ))
    idx = {u: i for i, u in enumerate(B)}
    D = len(B); assert D == r**(2*Q)
    def swap_s(u, s):
        u = list(u); a, d = u[s]; u[s] = (d, a); return tuple(u)
    # f_I interpolation polynomial: f(z) = (-1)^A0 sum_{j<R} (-2)^j binom(z-A0, j)
    p = Fr(r-1, 2*r); mu = Q*p
    A0 = int((mu - Fr(R-1, 2)) // 1)
    I = list(range(A0, A0+R))
    assert 0 <= A0 and A0+R-1 <= Q, "interval must lie in {0..Q}"
    def f(z):
        z = Fr(z); tot = Fr(0)
        for j in range(R):
            bn = Fr(1)
            for a in range(j): bn *= (z - A0 - a)
            bn /= Fr(1)*__import__('math').factorial(j)
            tot += Fr(-2)**j * bn
        return Fr(-1)**A0 * tot
    for j in I: assert f(j) == Fr(-1)**j
    # Product eigenbasis psi: at each position choose one of r(r+1)/2 (+1) or r(r-1)/2 (-1) vectors
    plus, minus = [], []
    for a in range(r): plus.append({(a, a): Fr(1)})
    for a in range(r):
        for d in range(a+1, r):
            plus.append({(a, d): Fr(1), (d, a): Fr(1)}); minus.append({(a, d): Fr(1), (d, a): Fr(-1)})
    choices = [(v, +1) for v in plus] + [(v, -1) for v in minus]
    basis = []  # (vector over B, j = number of -1 positions)
    for ch in itertools.product(choices, repeat=Q):
        j = sum(1 for _, e in ch if e == -1)
        vec = [Fr(1)]*D
        for i, u in enumerate(B):
            for s in range(Q):
                vec[i] *= ch[s][0].get(u[s], Fr(0))
        basis.append((vec, j))
    assert len(basis) == D
    # M0 via spectral formula: M0 psi = (-1)^j f(j) psi. Build M0 = sum_psi ((-1)^j f(j)) psi psi^T / <psi,psi>
    M0 = [[Fr(0)]*D for _ in range(D)]
    for vec, j in basis:
        lam = Fr(-1)**j * f(j); nrm = sum(x*x for x in vec)
        supp = [i for i, x in enumerate(vec) if x != 0]
        for i in supp:
            for k in supp:
                M0[i][k] += lam*vec[i]*vec[k]/nrm
    # cross-check spectral M0 against direct definition V0 f(W0) on a few basis vectors e_u
    def apply_W0(v):   # W0 = 1/2 sum_s (I - Pi_s), (Pi_s v)_u = v_{theta_s(u)}
        out = [Fr(0)]*D
        for s in range(Q):
            for i, u in enumerate(B): out[i] += (v[i] - v[idx[swap_s(u, s)]])/2
        return out
    def apply_V0(v):
        out = [Fr(0)]*D
        for i, u in enumerate(B):
            w = u
            for s in range(Q): w = swap_s(w, s)
            out[i] = v[idx[w]]
        return out
    def apply_fW0(v):
        # f(W0) v via explicit polynomial coefficients of f in monomial basis
        coeffs = solve([[Fr(z)**k for k in range(R)] for z in range(R)], [f(z) for z in range(R)])  # degree <= R-1
        acc = [Fr(0)]*D; pw = v[:]
        for k in range(R):
            acc = [a + coeffs[k]*x for a, x in zip(acc, pw)]
            pw = apply_W0(pw)
        return acc
    for i in random.sample(range(D), min(6, D)):
        e = [Fr(0)]*D; e[i] = Fr(1)
        direct = apply_V0(apply_fW0(e))
        col = [M0[k][i] for k in range(D)]
        assert direct == col, "spectral M0 != V0 f(W0)"
    C = [vec for vec, j in basis if j not in I]   # measurement rows
    # Lemma swaps-matrix: M0 fixes ker C  <=> (I-M0) psi = 0 for j in I; and rank(I-M0) <= |C|
    for vec, j in basis:
        img = [sum(M0[i][k]*vec[k] for k in range(D)) for i in range(D)]
        if j in I: assert img == vec
    IM = [[(Fr(1) if i == k else 0) - M0[i][k] for k in range(D)] for i in range(D)]
    assert rank(IM) == len(C)
    # Lemma swaps-support
    def mism(u, y): return sum(1 for s in range(Q) if y[s][0] != u[s][1])
    for i, u in enumerate(B):
        for k, y in enumerate(B):
            if M0[i][k] != 0: assert mism(u, y) <= R-1, "support lemma violated"
    # Rows P_u(T): P_u(T) = delta_u (I - M0) + sum_y M0[u,y] phi_{u,y}(T) delta_y, phi = prod_{s in E}(1 - T/s), s 1-based
    rows = []
    for i, u in enumerate(B):
        row = []
        for k, y in enumerate(B):
            poly = [IM[i][k]]  # constant from (I - M0)
            if M0[i][k] != 0:
                phi = [Fr(1)]
                for s in range(Q):
                    if y[s][0] != u[s][1]: phi = pmul(phi, [Fr(1), Fr(-1, s+1)])
                poly = padd(poly, pscale(phi, M0[i][k]))
            row.append(poly)
        rows.append(row)
    # Lemma swaps-forms checks
    for i, u in enumerate(B):
        for k in range(D):
            assert pdeg(rows[i][k]) <= R-1
            assert peval(rows[i][k], 0) == (1 if i == k else 0)
    # separation at each t: restriction of P_u(t) to S_{t,g}, g != d_u(t), lies in rowspace of C restricted to S_{t,g}
    for t in range(1, Q+1):
        for g in range(r):
            S = [k for k, y in enumerate(B) if y[t-1][0] == g]
            Cg = [[c[k] for k in S] for c in C]
            rk = rank(Cg)
            for i, u in enumerate(B):
                if u[t-1][1] == g: continue
                v = [peval(rows[i][k], t) for k in S]
                assert rank(Cg + [v]) == rk, "separation (Lemma swaps-forms) violated"
    return dict(B=B, idx=idx, D=D, M0=M0, C=C, rows=rows, I=I, A0=A0, f=f)

# ================================================================ PART B: end-to-end count on a 3-CNF
def end_to_end(aux, r, Q, R, n, clauses, seed):
    """clauses: list of lists of (var, sign) with sign True=positive; <=3 lits; each var in <=3 clauses."""
    rnd = random.Random(seed)
    B, idx, D, C, rows = aux['B'], aux['idx'], aux['D'], aux['C'], aux['rows']
    # dummy clauses for unused variables (scope {v}, Phi = 1)
    used = {v for cl in clauses for v, _ in cl}
    factors = [('clause', cl) for cl in clauses] + [('dummy', [(v, True)]) for v in range(n) if v not in used]
    scopes = [sorted({v for v, _ in cl}) for _, cl in factors]
    M = sum(len(s) for s in scopes)
    # schedules
    a = {v: tuple(rnd.randrange(r) for _ in range(Q)) for v in range(n)}
    d = {e: tuple(rnd.randrange(r) for _ in range(Q)) for e in range(len(factors))}
    label = {(e, v): tuple((a[v][s], d[e][s]) for s in range(Q)) for e, sc in enumerate(scopes) for v in sc}
    # copies
    copy, cnt = {}, {}
    for key, u in label.items():
        copy[key] = cnt.get(u, 0); cnt[u] = cnt.get(u, 0) + 1
    h = max(cnt.values())
    # transferred rows P_{e,v}(T) in Q[T]^n and measurement matrix Chat (h copies of C composed with iota)
    def P_ev(e, v):
        u = label[(e, v)]; c = copy[(e, v)]
        row = [[Fr(0)]*R for _ in range(n)]
        for (e2, v2), u2 in label.items():
            if copy[(e2, v2)] == c:
                row[v2] = padd(row[v2], rows[idx[u]][idx[u2]])
        return [ (x + [Fr(0)]*R)[:R] for x in row ]
    Prow = {key: P_ev(*key) for key in label}
    Chat = []
    for c in range(h):
        for crow in C:
            vec = [Fr(0)]*n
            for (e2, v2), u2 in label.items():
                if copy[(e2, v2)] == c: vec[v2] += crow[idx[u2]]
            Chat.append(vec)
    # group of variable v at t: a_v(t); clause assigned to d_e(t)
    def S_t(t, g): return [v for v in range(n) if a[v][t-1] == g]
    # Definition layout check (kernel condition) at each t
    for t in range(1, Q+1):
        for g in range(r):
            S = S_t(t, g); Cg = [[c[v] for v in S] for c in Chat]; rk = rank(Cg) if S else 0
            for e, sc in enumerate(scopes):
                if d[e][t-1] == g: continue
                for v in sc:
                    vec = [peval(Prow[(e, v)][w], t) for w in S]
                    if S: assert rank(Cg + [vec]) == rk, "Definition layout kernel condition failed"
    # clause polynomial Phi_e on (possibly non-Boolean) inputs: 1 - prod(1 - L); L = y (pos) or 1-y (neg)
    # WEIGHTED: each factor gets a random rational table phi_a : {0,1}^{S_a} -> Q, used via its
    # multilinear extension  phi(y) = sum_b phi_a(b) prod_v (y_v if b_v else 1-y_v)
    tables = {}
    for e, sc in enumerate(scopes):
        if factors[e][0] == 'dummy': continue
        tables[e] = {b: Fr(rnd.randrange(-5, 6), rnd.randrange(1, 4)) for b in itertools.product([0,1], repeat=len(sc))}
    def Phi(e, vals):
        kind, cl = factors[e]
        if kind == 'dummy': return [Fr(1)]
        sc = scopes[e]; out = [Fr(0)]
        for b, wgt in tables[e].items():
            term = [wgt]
            for v, bv in zip(sc, b):
                term = pmul(term, vals[v] if bv else padd([Fr(1)], pscale(vals[v], -1)))
            out = padd(out, term)
        return out
    # ---- brute force H(T): sum_x prod_e Phi_e(<P_{e,v}(T), x>)
    H = [Fr(0)]
    count_F = Fr(0)
    for x in itertools.product([0, 1], repeat=n):
        prod = [Fr(1)]
        for e, sc in enumerate(scopes):
            vals = {v: [sum(Prow[(e, v)][w][k]*x[w] for w in range(n)) for k in range(R)] for v in sc}  # poly in T
            prod = pmul(prod, Phi(e, vals))
        H = padd(H, prod)
        w = Fr(1)
        for e, sc in enumerate(scopes):
            if factors[e][0] != 'dummy': w *= tables[e][tuple(x[v] for v in sc)]
        count_F += w
    assert peval(H, 0) == count_F, "H(0) != Z"
    dH = pdeg(H); assert dH <= M*(R-1)
    # ---- Taylor data at t=1..Q via the SEPARATED routine
    d_H = M*(R-1); q = d_H // Q; J = q + 1
    assert Q*J > d_H
    taylor_sep = {}
    for t in range(1, Q+1):
        # per-group data
        groups = [S_t(t, g) for g in range(r)]
        Cg = [[[c[v] for v in S] for c in Chat] for S in groups]
        Pt = {key: [peval(Prow[key][w], t) for w in range(n)] for key in label}            # P(t)
        dP = {key: [pshift(Prow[key][w], t) for w in range(n)] for key in label}            # P(t+z) coefficients in z
        for key in dP:
            for w in range(n): dP[key][w][0] = Fr(0)                                          # Delta P = P(t+z)-P(t)
        acc = [Fr(0)]*J
        for size in range(0, min(q, n)+1):
            for E in itertools.combinations(range(n), size):
                for usz in range(size+1):
                    for U in itertools.combinations(E, usz):
                        sign = (-1)**(size - usz)
                        Uvec = [1 if w in U else 0 for w in range(n)]
                        # corrections independent of x: corr[e][v](z) = <Delta P, 1_U>
                        corr = {key: [sum((dP[key][w][k] if k < len(dP[key][w]) else Fr(0))*Uvec[w] for w in range(n)) for k in range(J)] for key in label}
                        # measurement-fixing enumeration (Lemma measurement-separation) with fixed bits E
                        # enumerate achievable measurement tuples per group
                        per_group = []
                        for g, S in enumerate(groups):
                            table = {}
                            for u in itertools.product([0, 1], repeat=len(S)):
                                y = tuple(sum(c[i]*u[i] for i in range(len(S))) for c in Cg[g])
                                table.setdefault(y, []).append(u)
                            per_group.append(table)
                        Z = [Fr(0)]*J
                        for ys in itertools.product(*[list(tb.keys()) for tb in per_group]):
                            reps = [per_group[g][ys[g]][0] for g in range(r)]
                            total = [Fr(1)]
                            for g, S in enumerate(groups):
                                s = [Fr(0)]*J
                                for u in per_group[g][ys[g]]:
                                    if any(u[i] != 1 for i, v in enumerate(S) if v in E): continue
                                    # full x: u on S_g, representatives elsewhere
                                    x = [0]*n
                                    for gg, SS in enumerate(groups):
                                        src = u if gg == g else reps[gg]
                                        for i, v in enumerate(SS): x[v] = src[i]
                                    A = [Fr(1)]
                                    for e, sc in enumerate(scopes):
                                        if d[e][t-1] != g: continue
                                        vals = {v: padd([sum(Pt[(e, v)][w]*x[w] for w in range(n))], corr[(e, v)]) for v in sc}
                                        A = pmul(A, Phi(e, vals), trunc=J)
                                    s = padd(s, A)
                                total = pmul(total, s, trunc=J)
                            Z = padd(Z, total)
                        acc = padd(acc, pscale(Z, sign))
        taylor_sep[t] = acc[:J]
        # compare with brute force Taylor coefficients of H at t
        bf = pshift(H, t)[:J] + [Fr(0)]*max(0, J - len(H))
        assert taylor_sep[t] == bf[:J], f"separated Taylor data != brute force at t={t}"
    # ---- Hermite interpolation: unknown coefficients c_0..c_{QJ-1} of H (deg <= d_H < QJ)
    N = Q*J
    A_mat, b_vec = [], []
    for t in range(1, Q+1):
        for j in range(J):
            A_mat.append([comb(i, j)*Fr(t)**(i-j) if i >= j else Fr(0) for i in range(N)])
            b_vec.append(taylor_sep[t][j])
    coeffs = solve(A_mat, b_vec)
    recovered = coeffs[0]
    assert recovered == count_F, f"Hermite recovery gave {recovered}, expected {count_F}"
    return dict(n=n, m=len(clauses), M=M, h=h, D=D, deg_H=dH, q=q, J=J, count=count_F, recovered=recovered, c_rows=len(C))

def random_bounded_cnf(n, rnd):
    """random 3-CNF with each variable in <= 3 clauses."""
    occ = [0]*n; clauses = []
    for _ in range(n):   # try to add up to n clauses
        avail = [v for v in range(n) if occ[v] < 3]
        if len(avail) < 3: break
        vs = rnd.sample(avail, 3)
        cl = [(v, rnd.random() < 0.5) for v in vs]
        for v in vs: occ[v] += 1
        clauses.append(cl)
    return clauses

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    random.seed(seed)
    results = []
    for (r, Q, R) in [(2, 2, 2)]:
        aux = build_auxiliary(r, Q, R)
        print(f"[A] r={r} Q={Q} R={R}: D={aux['D']} interval I={aux['I']} measurement rows c_B={len(aux['C'])} "
              f"(= D*Pr[Bin(Q,{Fr(r-1,2*r)}) notin I] = {aux['D']*sum(comb(Q,j)*Fr(r-1,2*r)**j*(1-Fr(r-1,2*r))**(Q-j) for j in range(Q+1) if j not in aux['I'])}) -- all Section 4.2 lemmas verified")
        results.append((r, Q, R, aux['D'], len(aux['C'])))
    # end-to-end on small formulas (R=2 keeps deg H small; Q=2 or 3)
    for (r, Q, R, n) in [(2, 2, 2, 5), (2, 3, 2, 6)]:
        aux = build_auxiliary(r, Q, R)
        rnd = random.Random(seed*100 + n)
        clauses = random_bounded_cnf(n, rnd)
        res = end_to_end(aux, r, Q, R, n, clauses, seed)
        print(f"[B] r={r} Q={Q} R={R} n={res['n']} m={res['m']} M={res['M']} copies h={res['h']} degH={res['deg_H']} q={res['q']} J={res['J']} "
              f"Z={res['count']} recovered={res['recovered']} -- design condition, separated Taylor data, Hermite recovery all verified")
    print("ALL CHECKS PASSED")
