#!/usr/bin/env python3
# quasi_eulerian_checks.py - exact checks of the computed facts in the paper
## version 1.20 - 2026-11-04 (paper v2.10: title year 1969; notation nu1, nu2; statement numbers unchanged)
## version 1.10 - 2026-10-24 (paper v1.30: check (I), the integer classes for n = 4, 5, 6)
## version 1.00 - 2026-10-24 (ancillary file of the paper; see README.txt)
# Ancillary file of "The Cerny (1969) conjecture holds for quasi-Eulerian automata of degree one".
# Author: Dave Goel
"""Checks, all in exact arithmetic (Python fractions), one thread, a few seconds:
 (G)  Lemma 5.8: binary witnesses of degree two. Of the 405 configurations (x1.a, x1.b, x2.a, x2.b; nu1, nu2) with targets in
      {x1, x2, s}, (nu1, nu2) != (0, 0) and nu1 + nu2 <= 2, exactly 179 have det(I - Z) != 0 and t1, t2 > 0; up to renaming
      x1 <-> x2 and a <-> b they form 49 configurations, and {t1, t2} takes 14 values. Each configuration is printed with
      the tag "block" if it satisfies the hypothesis of Proposition 5.6.
 (E1) Example 3.5: alpha = (1,1,1,1,2) is stationary at p = (1/2, 1/2); no witness of degree <= 2; the reset threshold.
 (E2) Example 3.6: no witness of degree <= 1; the irrational weights at x = 2 (checked in floating point).
 (C)  Theorem 4.1: the Cerny automata C_n, n = 3..8, have rt = (n-1)^2 and the witness E = {1..n-1}, s = 1, x = 0.
 (E3) Remark 4.3: the automaton a = (0,0,1,3), b = (3,1,3,2) has a degree-one witness with x = 3 and t = 2, and
      ext({0,1,2}) = 5; and ext({0,...,k-1}) = n in C_n for 2 <= k <= n-1, n = 4..8.
 (I)  Proposition 5.14 for n = 4, 5, 6: every strongly connected synchronizing binary automaton with a witness in the
      classes {2,2}, {2,3}, {2,4} has rt <= (n-1)^2. All members are listed: witness s = 0, X = {x1, x2} = {n-2, n-1},
      each state of E - {s} entered by exactly two edges (all from E), the two boundary edges as in the configuration.
Usage: python3 quasi_eulerian_checks.py   (exit status 0 if every check passes, 1 otherwise)
"""
import itertools
import sys
from fractions import Fraction as Fr

TARGETS = ("x1", "x2", "s")
BOUNDARY = ((1, 0), (0, 1), (2, 0), (1, 1), (0, 2))
INTEGER_CLASSES = ((Fr(2), Fr(2)), (Fr(2), Fr(3)), (Fr(2), Fr(4)))
CENSUS_SIZES = (4, 5, 6)


def solve_configuration(targets, boundary):
    """targets = (x1.a, x1.b, x2.a, x2.b); boundary = (nu1, nu2) (paper notation). Returns (t1, t2) or None."""
    zz = [[Fr(0), Fr(0)], [Fr(0), Fr(0)]]
    for ii, tgt in enumerate(targets):
        src = ii // 2
        if tgt in ("x1", "x2"):
            zz[src][0 if tgt == "x1" else 1] += Fr(1, 2)
    yy = [Fr(boundary[0], 2), Fr(boundary[1], 2)]
    m11, m12 = 1 - zz[0][0], -zz[0][1]
    m21, m22 = -zz[1][0], 1 - zz[1][1]
    det = m11 * m22 - m12 * m21
    if det == 0:
        return None
    t1 = (yy[0] * m22 - yy[1] * m21) / det
    t2 = (m11 * yy[1] - m12 * yy[0]) / det
    if t1 <= 0 or t2 <= 0:
        return None
    return (t1, t2)


def canonical(targets, boundary):
    """Canonical form under renaming x1 <-> x2 and a <-> b."""
    forms = []
    swap_x = {"x1": "x2", "x2": "x1", "s": "s"}
    for sx in (False, True):
        for sl in (False, True):
            tg = list(targets)
            bd = tuple(boundary)
            if sx:
                tg = [swap_x[tg[2]], swap_x[tg[3]], swap_x[tg[0]], swap_x[tg[1]]]
                bd = (bd[1], bd[0])
            if sl:
                tg = [tg[1], tg[0], tg[3], tg[2]]
            forms.append((tuple(tg), bd))
    return min(forms)


def is_block(targets):
    """Hypothesis of Proposition 5.6: for each letter, x1.c = x2.c or {x1.c, x2.c} = X."""
    for letter in (0, 1):
        u1, u2 = targets[letter], targets[2 + letter]
        if u1 != u2 and {u1, u2} != {"x1", "x2"}:
            return False
    return True


def check_configurations():
    classes = {}
    count = 0
    for targets in itertools.product(TARGETS, repeat=4):
        for boundary in BOUNDARY:
            sol = solve_configuration(targets, boundary)
            if sol is None:
                continue
            count += 1
            classes.setdefault(tuple(sorted(sol)), set()).add(canonical(targets, boundary))
    total = sum(len(shapes) for shapes in classes.values())
    print(f"(G) configurations with det(I-Z) != 0 and t > 0: {count}; up to renaming: {total}; classes: {len(classes)}")
    for key in sorted(classes):
        shapes = sorted(classes[key])
        print(f"  {{{key[0]}, {key[1]}}}: {len(shapes)} configuration(s)")
        for shape in shapes:
            tag = "block" if is_block(shape[0]) else "-"
            print(f"     x1.a, x1.b, x2.a, x2.b = {shape[0]}; boundary edges to (x1, x2) = {shape[1]}  [{tag}]")
    return count == 179 and total == 49 and len(classes) == 14


def reset_threshold(trans):
    """Breadth-first search on subsets; trans = list of letter images. Returns rt or None."""
    n = len(trans[0])
    full = (1 << n) - 1
    dist = {full: 0}
    frontier = [full]
    while frontier:
        nxt = []
        for sset in frontier:
            if sset & (sset - 1) == 0:
                return dist[sset]
            for img in trans:
                new = 0
                for qq in range(n):
                    if sset >> qq & 1:
                        new |= 1 << img[qq]
                if new not in dist:
                    dist[new] = dist[sset] + 1
                    nxt.append(new)
        frontier = nxt
    return None


def witness_feasible(trans, xset, sstate):
    """Binary automaton: is (E = Q - X, s) a witness for some p = (p_a, 1 - p_a), 0 < p_a < 1? Exact."""
    n = len(trans[0])
    for img in trans:
        for xx in xset:
            if img[xx] not in xset and img[xx] != sstate:
                return False
    eset = [qq for qq in range(n) if qq not in xset]
    if sstate not in eset:
        return False
    pa_fixed = None
    for rr in eset:
        if rr == sstate:
            continue
        ia = sum(1 for qq in range(n) if trans[0][qq] == rr)
        ib = sum(1 for qq in range(n) if trans[1][qq] == rr)
        if ia == ib:
            if ia != 1:
                return False
            continue
        val = Fr(1 - ib, ia - ib)
        if not 0 < val < 1:
            return False
        if pa_fixed is not None and pa_fixed != val:
            return False
        pa_fixed = val
    return True


def least_degree(trans, dmax):
    n = len(trans[0])
    for dd in range(dmax + 1):
        for xset in itertools.combinations(range(n), dd):
            for sstate in range(n):
                if sstate not in xset and witness_feasible(trans, set(xset), sstate):
                    return dd
    return None


def is_stationary(trans, pvec, alpha):
    n = len(trans[0])
    out = [Fr(0)] * n
    for img, pp in zip(trans, pvec):
        for qq in range(n):
            out[img[qq]] += pp * alpha[qq]
    return out == list(alpha)


def ext_length(trans, kset, max_len):
    """Least |w| with |K w^-1| > |K| (breadth-first search over preimages); None if none up to max_len."""
    start = frozenset(kset)
    seen = {start}
    frontier = [start]
    for length in range(1, max_len + 1):
        nxt = []
        for sset in frontier:
            for img in trans:
                pre = frozenset(qq for qq in range(len(img)) if img[qq] in sset)
                if len(pre) > len(start):
                    return length
                if pre not in seen:
                    seen.add(pre)
                    nxt.append(pre)
        frontier = nxt
    return None


def cerny(n):
    return [tuple(1 if qq == 0 else qq for qq in range(n)), tuple((qq + 1) % n for qq in range(n))]


def check_example_35():
    trans = [(2, 4, 3, 4, 0), (4, 2, 4, 3, 1)]
    stat = is_stationary(trans, [Fr(1, 2), Fr(1, 2)], [Fr(1)] * 4 + [Fr(2)])
    deg = least_degree(trans, 2)
    rt = reset_threshold(trans)
    print(f"(E1) Example 3.5: alpha = (1,1,1,1,2) stationary at p = 1/2: {stat}; witness of degree <= 2: {deg}; rt = {rt}")
    return stat and deg is None and rt == 5


def check_example_36():
    trans = [(0, 0, 0), (1, 2, 1)]
    deg = least_degree(trans, 1)
    pa = (3 - 5 ** 0.5) / 2
    tt = (5 ** 0.5 - 1) / 2
    res = [pa * (2 + tt) - 1, (1 - pa) * (1 + tt) - 1]
    print(f"(E2) Example 3.6: witness of degree <= 1: {deg}; residuals at x = 2: {res[0]:.1e}, {res[1]:.1e}")
    return deg is None and max(abs(rr) for rr in res) < 1e-12


def check_cerny():
    good = True
    for n in range(3, 9):
        trans = cerny(n)
        rt = reset_threshold(trans)
        wit = witness_feasible(trans, {0}, 1)
        print(f"(C) C_{n}: rt = {rt} = (n-1)^2: {rt == (n - 1) ** 2}; witness E = {{1..n-1}}, s = 1, x = 0: {wit}")
        good = good and rt == (n - 1) ** 2 and wit
    return good


def check_remark_43():
    trans = [(0, 0, 1, 3), (3, 1, 3, 2)]
    wit = witness_feasible(trans, {3}, 2)
    stat = is_stationary(trans, [Fr(1, 2), Fr(1, 2)], [Fr(1), Fr(1), Fr(1), Fr(2)])
    ext = ext_length(trans, {0, 1, 2}, 12)
    rt = reset_threshold(trans)
    print(f"(E3) Remark 4.3: witness E = {{0,1,2}}, s = 2, x = 3: {wit}; alpha = (1,1,1,2) stationary: {stat}; "
          f"ext({{0,1,2}}) = {ext}; rt = {rt}")
    good = wit and stat and ext == 5 and rt is not None
    for n in range(4, 9):
        exts = [ext_length(cerny(n), set(range(kk)), 3 * n) for kk in range(2, n)]
        print(f"(E3) C_{n}: ext({{0,...,k-1}}) for k = 2..{n - 1}: {exts}")
        good = good and all(ee == n for ee in exts)
    return good


def is_strongly_connected(trans):
    n = len(trans[0])
    for start in range(n):
        seen = {start}
        stack = [start]
        while stack:
            qq = stack.pop()
            for img in trans:
                if img[qq] not in seen:
                    seen.add(img[qq])
                    stack.append(img[qq])
        if len(seen) < n:
            return False
    return True


def class_members(targets, boundary, n):
    """All binary automata with witness s = 0, x1 = n-2, x2 = n-1 and this configuration, at p = (1/2, 1/2): the states
    1..n-3 of E - {s} are entered by exactly two edges each, all from E; boundary[i] boundary edges end at x_i and the
    others at s. Yields (images under a, images under b)."""
    code = {"s": 0, "x1": n - 2, "x2": n - 1}
    x_images = [code[tgt] for tgt in targets]
    ends = [rr for rr in range(1, n - 2) for _ in range(2)] + [n - 2] * boundary[0] + [n - 1] * boundary[1]
    ends += [0] * (2 - boundary[0] - boundary[1])
    for order in sorted(set(itertools.permutations(ends))):
        yield (tuple(order[0::2]) + (x_images[0], x_images[2]), tuple(order[1::2]) + (x_images[1], x_images[3]))


def census_configuration(targets, boundary, sol, n):
    """Strongly connected synchronizing members of one labeled configuration: (number, largest rt, checks pass)."""
    alpha = [Fr(1)] * (n - 2) + [sol[0], sol[1]]
    count, largest, good = 0, 0, True
    for trans in class_members(targets, boundary, n):
        if not is_strongly_connected(trans):
            continue
        rt = reset_threshold(trans)
        if rt is None:
            continue
        count += 1
        largest = max(largest, rt)
        good = good and is_stationary(trans, [Fr(1, 2), Fr(1, 2)], alpha) and rt <= (n - 1) ** 2
    return count, largest, good


def check_integer_classes():
    good = True
    for n in CENSUS_SIZES:
        members = dict.fromkeys(INTEGER_CLASSES, 0)
        max_rt = dict.fromkeys(INTEGER_CLASSES, 0)
        for targets in itertools.product(TARGETS, repeat=4):
            for boundary in BOUNDARY:
                sol = solve_configuration(targets, boundary)
                if sol is None or tuple(sorted(sol)) not in members:
                    continue
                count, largest, passed = census_configuration(targets, boundary, sol, n)
                members[tuple(sorted(sol))] += count
                max_rt[tuple(sorted(sol))] = max(max_rt[tuple(sorted(sol))], largest)
                good = good and passed
        good = good and all(count > 0 for count in members.values())
        print(f"(I) n = {n}: members (labeled) of {{2,2}}, {{2,3}}, {{2,4}}: {list(members.values())}; "
              f"largest rt: {list(max_rt.values())}; (n-1)^2 = {(n - 1) ** 2}")
    return good


def main():
    results = [check_configurations(), check_example_35(), check_example_36(), check_cerny(), check_remark_43(),
               check_integer_classes()]
    print("ALL PASS" if all(results) else f"FAILED: {results}")
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
