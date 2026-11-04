# The Černý (1969) conjecture holds for quasi-Eulerian automata of degree one: program and output

Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

The paper: https://doi.org/10.5281/zenodo.23956693

The proofs of Lemma 5.8 (with Table 1) and of Proposition 5.14 for 4 ≤ n ≤ 6 rest on the computation below; the other checks
confirm the examples. Numbering as in the paper.

## Directions to Reproduce

Install: Python 3 (made with Python 3.12.3); only the standard library is used. Run from this folder:

```
python3 quasi_eulerian_checks.py > out.txt && cmp out.txt quasi_eulerian_checks_output.txt
```

You see nothing from `cmp` (the new output equals the stored one), and the last line of `out.txt` is `ALL PASS`. It takes about
5 seconds on one thread; any failed check makes the program exit with status 1. All arithmetic is exact (Python fractions).

| Statement | What the program checks | Output |
|---|---|---|
| Lemma 5.8, Table 1 | the 405 configurations of a binary witness of degree two; the 179 with det(I − Z) ≠ 0 and t1, t2 > 0; the 49 configurations up to renaming x1 ↔ x2 and a ↔ b; the 14 classes {t1, t2}; each configuration printed, tagged "block" when it satisfies the hypothesis of Proposition 5.6 | part (G) |
| Proposition 5.14, 4 ≤ n ≤ 6 | every strongly connected synchronizing binary automaton with a witness in the classes {2, 2}, {2, 3}, {2, 4}: the stationary vector (1, …, 1, t1, t2) at p = (1/2, 1/2), exactly, and the reset threshold; largest values 8, 13, 19 for n = 4, 5, 6 | part (I) |
| Example 3.5 | the stationary vector (1, 1, 1, 1, 2) at p = (1/2, 1/2); no witness of degree at most two; reset threshold 5 | part (E1) |
| Example 3.6 | no witness of degree at most one; the irrational weights at x = 2 (floating-point residuals) | part (E2) |
| Theorem 4.1 (the Černý automata) | C_n for n = 3, …, 8: reset threshold (n − 1)^2 and the degree-one witness E = {1, …, n − 1}, s = 1, x = 0 | part (C) |
| Remark 4.3 | the automaton a = (0, 0, 1, 3), b = (3, 1, 3, 2) with x = 3, t = 2 and ext({0, 1, 2}) = 5; ext({0, …, k − 1}) = n in C_n for 2 ≤ k ≤ n − 1, n = 4, …, 8 | part (E3) |
