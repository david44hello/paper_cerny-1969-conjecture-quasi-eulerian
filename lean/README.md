# The Černý (1969) conjecture holds for quasi-Eulerian automata of degree one — Lean 4 proof

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_cerny-1969-conjecture-quasi-eulerian).

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/) and Python 3, then run:

```bash
git clone --branch v4.50 --single-branch https://github.com/david44hello/paper_cerny-1969-conjecture-quasi-eulerian.git
cd paper_cerny-1969-conjecture-quasi-eulerian/lean
./check.sh
```

The build needs about 8.6 GB of memory and about 31 minutes on one processor core; with more cores it is faster
but needs more memory.

Near the end it prints:

```
Totals: rows 167; PROVED 167; PROVED FROM CITED 0; CITED 0; not proved yet 0; FAIL 0.
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed rows; statuses match the list.
```

The proof takes no result of another paper and no computer check as given: the finite checks of Proposition 5.14 are
proved in Lean. [AUDIT.md](AUDIT.md) gives the status of every claim, and [AUDIT_NOTES.md](AUDIT_NOTES.md) explains
the formalization.

Copyright (C) Dave Goel 2026--now. All rights reserved.
