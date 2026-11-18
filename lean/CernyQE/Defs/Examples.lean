/-
CernyQE/Defs/Examples.lean — the explicit automata of the paper: the 4-state automaton of Remark 4.4, Example 3.5,
Example 3.6 and the 4-state automaton of Remark 4.3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.31 - 20261118 — source references use the paper metadata recorded in the audit notes and claim map.
## version 0.01 - 20261105 — first.
Paper = the paper's frozen text; a pointer "tex:N" is line N of its main source file (AUDIT_NOTES.md names the version and its SHA-256).
Letters: `a = 0`, `b = 1` in `Fin 2`. A list `(i₀, i₁, …)` gives the images of the states `0, 1, …`.
-/
import CernyQE.Defs.Automaton

namespace CernyQE

/-- The automaton from two image lists (letter `a = 0` and letter `b = 1`). -/
def ofLists {n : ℕ} (la lb : Fin n → Fin n) : Automaton (Fin n) (Fin 2) where
  step q c := if c = 0 then la q else lb q

/-- The automaton of Remark 4.4 (tex:561): `a = (0,2,1,0)`, `b = (1,3,2,0)`. -/
def exIntro4 : Automaton (Fin 4) (Fin 2) := ofLists ![0, 2, 1, 0] ![1, 3, 2, 0]

/-- Example 3.5 (tex:478): `a = (2,4,3,4,0)`, `b = (4,2,4,3,1)`. -/
def ex35 : Automaton (Fin 5) (Fin 2) := ofLists ![2, 4, 3, 4, 0] ![4, 2, 4, 3, 1]

/-- Example 3.6 (tex:492): `a` maps every state to `0`; `b = (1,2,1)`. -/
def ex36 : Automaton (Fin 3) (Fin 2) := ofLists ![0, 0, 0] ![1, 2, 1]

/-- The automaton of Remark 4.3 (tex:557): `a = (0,0,1,3)`, `b = (3,1,3,2)`. -/
def ex43 : Automaton (Fin 4) (Fin 2) := ofLists ![0, 0, 1, 3] ![3, 1, 3, 2]

end CernyQE
