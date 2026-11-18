/-
CernyQE/Defs/Tier.lean — the row vectors and subspaces of the proof of the tier lemma (Lemma 2.4) and of Remark 2.5.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.31 - 20261118 — source references use the paper metadata recorded in the audit notes and claim map.
## version 0.01 - 20261105 — first.
Paper = the paper's frozen text; a pointer "tex:N" is line N of its main source file (AUDIT_NOTES.md names the version and its SHA-256).
Row vectors are functions `Q → ℝ`; `αᵀ M` is `Matrix.vecMul α M`.
-/
import CernyQE.Defs.Automaton

namespace CernyQE

variable {Q S : Type*} [Fintype Q] [DecidableEq Q]

namespace Automaton

variable (A : Automaton Q S)

/-- `δ_c = αᵀ M_c - αᵀ`, a row vector (tex:334). -/
noncomputable def delta (α : Q → ℝ) (c : S) : Q → ℝ := Matrix.vecMul α (A.Mw [c]) - α

/-- `D_k = span{δ_c M_v : c ∈ Σ, |v| ≤ k - 1}`, so `D_0 = 0` (tex:335). -/
noncomputable def Dk (α : Q → ℝ) (k : ℕ) : Submodule ℝ (Q → ℝ) :=
  Submodule.span ℝ {lam | ∃ (c : S) (v : List S), v.length + 1 ≤ k ∧ lam = Matrix.vecMul (A.delta α c) (A.Mw v)}

/-- `U_k = span{αᵀ M_u : |u| ≤ k - 1}`, so that `U_{k+1} = span{αᵀ M_u : |u| ≤ k}` is Berlinkov's chain (tex:366-367). -/
noncomputable def Uk (α : Q → ℝ) (k : ℕ) : Submodule ℝ (Q → ℝ) :=
  Submodule.span ℝ {lam | ∃ u : List S, u.length + 1 ≤ k ∧ lam = Matrix.vecMul α (A.Mw u)}

end Automaton

end CernyQE
