/-
CernyQE/Defs/Binary.lean — binary automata of degree two (Section 5.4): configurations and their renamings, the
matrix Z, the vector y and the class t of a configuration (Lemmas 5.7-5.8, Table 1), the configuration of a witness,
patterns, good and aligned patterns.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.31 - 20261118 — source references use the paper metadata recorded in the audit notes and claim map.
## version 0.01 - 20261105 — first.
Paper = the paper's frozen text; a pointer "tex:N" is line N of its main source file (AUDIT_NOTES.md names the version and its SHA-256).
A configuration lives on codes: a target `x_i.c ∈ {x₁, x₂, s}` is coded `0 = x₁`, `1 = x₂`, `2 = s`; letters are coded
`0 = a`, `1 = b`; exceptional states `0 = x₁`, `1 = x₂`. Its numbers are rationals, so finite facts are kernel-checked.
-/
import CernyQE.Defs.Witness

namespace CernyQE

/-- A configuration `(x₁.a, x₁.b, x₂.a, x₂.b; ν₁, ν₂)` (tex:690-691). -/
structure Config where
  x1a : Fin 3
  x1b : Fin 3
  x2a : Fin 3
  x2b : Fin 3
  nu1 : ℕ
  nu2 : ℕ
  deriving DecidableEq, Repr

namespace Config

/-- The target code of `x_i.c` (exceptional state `i`, letter `c`). -/
def tgt (cf : Config) : Fin 2 → Fin 2 → Fin 3 :=
  ![![cf.x1a, cf.x1b], ![cf.x2a, cf.x2b]]

/-- `ν_i`, the number of boundary edges that end at `x_i`. -/
def nu (cf : Config) : Fin 2 → ℕ := ![cf.nu1, cf.nu2]

/-- `Z_{ij} = ½ |{c : x_i.c = x_j}|` (tex:691). -/
def Z (cf : Config) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => (1 / 2 : ℚ) * ((Finset.univ.filter (fun c : Fin 2 => cf.tgt i c = Fin.castSucc j)).card : ℚ)

/-- `y_i = ν_i / 2` (tex:691). -/
def y (cf : Config) : Fin 2 → ℚ := fun i => (cf.nu i : ℚ) / 2

/-- `det (I - Z)` (tex:717). -/
def det (cf : Config) : ℚ := (1 - cf.Z 0 0) * (1 - cf.Z 1 1) - cf.Z 0 1 * cf.Z 1 0

/-- The row vector `t = y (I - Z)⁻¹` by Cramer's rule (meaningful when `det ≠ 0`; tex:641, tex:691). -/
def t (cf : Config) : Fin 2 → ℚ :=
  ![(cf.y 0 * (1 - cf.Z 1 1) + cf.y 1 * cf.Z 1 0) / cf.det,
    (cf.y 1 * (1 - cf.Z 0 0) + cf.y 0 * cf.Z 0 1) / cf.det]

/-- A configuration counted in Lemma 5.8: `det (I - Z) ≠ 0` and `t₁, t₂ > 0` (tex:717). -/
def Valid (cf : Config) : Prop := cf.det ≠ 0 ∧ 0 < cf.t 0 ∧ 0 < cf.t 1

instance (cf : Config) : Decidable cf.Valid := by unfold Valid; infer_instance

/-- The class `{t₁, t₂}`, written as the sorted pair (tex:95). -/
def cls (cf : Config) : ℚ × ℚ := (min (cf.t 0) (cf.t 1), max (cf.t 0) (cf.t 1))

/-- Swap the codes of `x₁` and `x₂`. -/
def swapCode (k : Fin 3) : Fin 3 := if k = 0 then 1 else if k = 1 then 0 else k

/-- Renaming `x₁ ↔ x₂` (tex:714). -/
def swapX (cf : Config) : Config :=
  ⟨swapCode cf.x2a, swapCode cf.x2b, swapCode cf.x1a, swapCode cf.x1b, cf.nu2, cf.nu1⟩

/-- Renaming `a ↔ b` (tex:714). -/
def swapL (cf : Config) : Config :=
  ⟨cf.x1b, cf.x1a, cf.x2b, cf.x2a, cf.nu1, cf.nu2⟩

/-- The configurations obtained by renaming `x₁ ↔ x₂` and `a ↔ b` (tex:714). -/
def renamings (cf : Config) : Finset Config :=
  {cf, cf.swapX, cf.swapL, cf.swapX.swapL}

/-- A block configuration (Table 1 caption, tex:729-730; Proposition 5.6): every letter maps `x₁, x₂` to one state
or to the pair `{x₁, x₂}`. -/
def IsBlock (cf : Config) : Prop :=
  (cf.x1a = cf.x2a ∨ ({cf.x1a, cf.x2a} : Finset (Fin 3)) = {0, 1}) ∧
  (cf.x1b = cf.x2b ∨ ({cf.x1b, cf.x2b} : Finset (Fin 3)) = {0, 1})

instance (cf : Config) : Decidable cf.IsBlock := by unfold IsBlock; infer_instance

end Config

/-- The `3^4 · 5 = 405` choices (tex:712-714): all targets, `ν₁ + ν₂ ≤ 2`, `(ν₁, ν₂) ≠ (0, 0)`. -/
def choices : Finset Config :=
  ((Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3)).filter
      (fun v => v.2.2.2.2.1.val + v.2.2.2.2.2.val ≤ 2 ∧ ¬ (v.2.2.2.2.1 = 0 ∧ v.2.2.2.2.2 = 0))).image
    (fun v => (⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1.val, v.2.2.2.2.2.val⟩ : Config))

/-- The 14 classes of Table 1 (tex:735-742), as sorted pairs. -/
def tableClasses : Finset (ℚ × ℚ) :=
  {(1, 1), (1/2, 1), (1, 2), (1/4, 1/2), (1/2, 3/4), (1/3, 2/3), (2/3, 4/3), (1/2, 2), (3/2, 2), (2, 2), (2, 3),
    (2, 4), (1/2, 1/2), (1/2, 3/2)}

/-- The three configurations excluded by Theorem 5.9 (tex:749-751): `(s,x₁,x₁,s;0,1)`, `(s,s,x₁,x₁;0,1)`,
`(s,x₁,x₁,s;1,1)`. -/
def openConfigs : Finset Config :=
  {⟨2, 0, 0, 2, 0, 1⟩, ⟨2, 2, 0, 0, 0, 1⟩, ⟨2, 0, 0, 2, 1, 1⟩}

variable {Q S : Type*} [Fintype Q] [DecidableEq Q]

/-- The code of a state in `{x₁, x₂, s}`: `0 = x₁`, `1 = x₂`, `2` otherwise (a target of an edge from `X` is `s`
there, by Definition 1.1(a)). -/
def stateCode (x₁ x₂ : Q) (q : Q) : Fin 3 := if q = x₁ then 0 else if q = x₂ then 1 else 2

namespace Automaton

variable (A : Automaton Q S)

/-- The number `ν` of edges from `E` (letters `a`, `b`) that end at `x` (tex:691). -/
def nuOf (a b : S) (E : Finset Q) (x : Q) : ℕ :=
  (E.filter (fun q => A.step q a = x)).card + (E.filter (fun q => A.step q b = x)).card

/-- The configuration `(x₁.a, x₁.b, x₂.a, x₂.b; ν₁, ν₂)` of a binary witness with exceptional states `x₁, x₂`
(tex:690-691). -/
def configOf (a b : S) (E : Finset Q) (x₁ x₂ : Q) : Config :=
  ⟨stateCode x₁ x₂ (A.step x₁ a), stateCode x₁ x₂ (A.step x₁ b), stateCode x₁ x₂ (A.step x₂ a),
    stateCode x₁ x₂ (A.step x₂ b),
    A.nuOf a b E x₁, A.nuOf a b E x₂⟩

end Automaton

/-- The pattern `P(K) = (e₁(K), e₂(K), e_s(K))` of a set (tex:771). -/
def pattern (x₁ x₂ s : Q) (K : Finset Q) : Bool × Bool × Bool :=
  (decide (x₁ ∈ K), decide (x₂ ∈ K), decide (s ∈ K))

/-- `[x ∈ K]` as a real number. -/
noncomputable def ein (x : Q) (K : Finset Q) : ℝ := if x ∈ K then 1 else 0

/-- A pattern `P` is good (tex:784-785) for the numbers `g₁, g₂`: for some letter `c` and some set `K` with pattern
`P`, the number `g₁ (e₁(K c⁻¹) - e₁(K)) + g₂ (e₂(K c⁻¹) - e₂(K))` is not an integer. -/
def Good (A : Automaton Q S) (x₁ x₂ s : Q) (g₁ g₂ : ℝ) (P : Bool × Bool × Bool) : Prop :=
  ∃ (c : S) (K : Finset Q), pattern x₁ x₂ s K = P ∧
    ¬ ∃ z : ℤ, g₁ * (ein x₁ (A.pre K [c]) - ein x₁ K) + g₂ * (ein x₂ (A.pre K [c]) - ein x₂ K) = z

/-- The aligned patterns `(1,1,1)` and `(0,0,0)` (tex:786). -/
def Aligned (P : Bool × Bool × Bool) : Prop := P = (true, true, true) ∨ P = (false, false, false)

end CernyQE
