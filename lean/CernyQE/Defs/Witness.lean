/-
CernyQE/Defs/Witness.lean — quantities of a witness: z and y of Section 4, the matrix Z, the vector y and the
stationary vector of Lemma 5.5, and the quotient automaton of Proposition 5.6.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.31 - 20261118 — source references use the paper metadata recorded in the audit notes and claim map.
## version 0.01 - 20261105 — first.
Paper = the paper's frozen text; a pointer "tex:N" is line N of its main source file (AUDIT_NOTES.md names the version and its SHA-256).
The objects are defined from raw data (a set `E` and weights `p`), so that they can be used with the weights
`(1/2, 1/2)` of Lemma 5.7 as well as with the weights of a witness.
-/
import CernyQE.Defs.Automaton

namespace CernyQE

variable {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S]

namespace Automaton

variable (A : Automaton Q S)

/-- `z = ∑_{b : x.b = x} p_b`, the weight of the loops at `x` (tex:508). -/
noncomputable def zLoop (p : S → ℝ) (x : Q) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b => A.step x b = x), p b

/-- `y = ∑_b p_b |{q ∈ E : q.b = x}|`, the weight of the edges from `E` into `x` (tex:508, tex:640). -/
noncomputable def yIn (E : Finset Q) (p : S → ℝ) (x : Q) : ℝ :=
  ∑ b, p b * ((E.filter (fun q => A.step q b = x)).card : ℝ)

/-- The vector of Lemma 4.2 (tex:513): `1` off `x` and `t = y/(1-z)` at `x`. -/
noncomputable def alphaDeg1 (E : Finset Q) (p : S → ℝ) (x : Q) : Q → ℝ :=
  fun q => if q = x then A.yIn E p x / (1 - A.zLoop p x) else 1

/-- The `X × X` matrix `Z` of Lemma 5.5 (tex:639-640), `X = Q \ E`: `Z_{x x'} = ∑_{b : x.b = x'} p_b`. -/
noncomputable def Zmat (E : Finset Q) (p : S → ℝ) : Matrix (Finset.univ \ E : Finset Q) (Finset.univ \ E : Finset Q) ℝ :=
  fun x x' => ∑ b ∈ Finset.univ.filter (fun b => A.step x.1 b = x'.1), p b

/-- The row vector `y ∈ ℝ^X` of Lemma 5.5 (tex:640): `y_x = ∑_b p_b |{q ∈ E : q.b = x}|`. -/
noncomputable def yvec (E : Finset Q) (p : S → ℝ) : (Finset.univ \ E : Finset Q) → ℝ :=
  fun x => A.yIn E p x.1

/-- The row vector `t = y (I - Z)⁻¹` of Lemma 5.5 (tex:641). -/
noncomputable def tvec (E : Finset Q) (p : S → ℝ) : (Finset.univ \ E : Finset Q) → ℝ :=
  Matrix.vecMul (A.yvec E p) (1 - A.Zmat E p)⁻¹

/-- The vector `α` of Lemma 5.5 (tex:641): `1` on `E` and `t` on `X = Q \ E`. -/
noncomputable def alphaStat (E : Finset Q) (p : S → ℝ) : Q → ℝ :=
  fun q => if h : q ∈ Finset.univ \ E then A.tvec E p ⟨q, h⟩ else 1

/-- `Z_{x x'} = ∑_{b : x.b = x'} p_b` for two states (the entries of `Zmat`; tex:640, tex:691). -/
noncomputable def zPair (p : S → ℝ) (x x' : Q) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b => A.step x b = x'), p b

/-- A set `C` is a minimal nonempty closed set (tex:576). -/
def IsMinClosed (C : Finset Q) : Prop :=
  C.Nonempty ∧ A.IsClosed C ∧ ∀ C' : Finset Q, C'.Nonempty → A.IsClosed C' → C' ⊆ C → C' = C

/-- An extension process for a vector `α` (tex:441-443, tex:776-781): sets `K 0, …, K J` and words `w 0, …, w (J-1)`
with `K (j+1) = K j (w j)⁻¹`, where `w j` raises `α` for the proper set `K j` and has length `m(K j)`, and
`K J = Q`. -/
def IsProcess (α : Q → ℝ) (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ) : Prop :=
  (∀ j < J, K j ≠ Finset.univ ∧ K (j + 1) = A.pre (K j) (w j) ∧ ((w j).length : ℕ∞) = A.cost α (K j) ∧
    A.Raises α (K j) (w j)) ∧ K J = Finset.univ

/-- The quotient automaton of Proposition 5.6 (tex:667-668) for the partition of `Q` into `{x₁, x₂}` and singletons,
written on the states other than `x₂`: the block `{x₁, x₂}` is represented by `x₁`. -/
def blockQuot (x₁ x₂ : Q) (h : x₁ ≠ x₂) : Automaton {q : Q // q ≠ x₂} S where
  step q b := if h' : A.step q.1 b = x₂ then ⟨x₁, h⟩ else ⟨A.step q.1 b, h'⟩

end Automaton

/-- The vector of Section 3 after scaling (tex:386): `1` on `Q \ {x}` and `t` at `x`. -/
noncomputable def alphaOff (x : Q) (t : ℝ) : Q → ℝ := fun q => if q = x then t else 1

/-- An expensive set (tex:408), for `0 < t < 2`, `t ≠ 1`: `x ∉ K` when `t > 1`, `x ∈ K` when `t < 1`; the other sets
are cheap. -/
def Expensive (x : Q) (t : ℝ) (K : Finset Q) : Prop := (1 < t ∧ x ∉ K) ∨ (t < 1 ∧ x ∈ K)

end CernyQE
