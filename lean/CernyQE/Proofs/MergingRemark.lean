/-
Proofs/MergingRemark.lean — Proposition 5.11's remark: a merging letter alone would not do (an automaton with
`{s} a⁻¹ = X` and `α(X) = 3/4 < 1`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.01 - 20261105 — first.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary
import CernyQE.Defs.Examples
import CernyQE.Proofs.BinaryBase

namespace CernyQE

open Classical Automaton Matrix

namespace MergingRemark

theorem half_weights : IsLetterWeights (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
  refine ⟨fun _ => by norm_num, ?_⟩
  rw [Fin.sum_univ_two]
  norm_num

/-- With the weights `(1/2, 1/2)`, a state entered by exactly two edges has in-weight one. -/
theorem inW_half {n : ℕ} (A : Automaton (Fin n) (Fin 2)) (r : Fin n) (h : ∑ b, (A.pre {r} [b]).card = 2) :
    A.inW (fun _ => 1 / 2) r = 1 := by
  have h' : (∑ b, ((A.pre {r} [b]).card : ℝ)) = 2 := by exact_mod_cast h
  rw [inW, ← Finset.mul_sum, h']
  norm_num

/-- The automaton of the remark: `a = (0,0,1,1)`, `b = (1,3,1,2)`. -/
abbrev B : Automaton (Fin 4) (Fin 2) := ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]

/-- Its witness: `E = {0, 1}`, `s = 1`, weights `(1/2, 1/2)`. -/
noncomputable def W : QEWitness B 2 :=
  ⟨{0, 1}, 1, fun _ => 1 / 2, by rfl, by decide +kernel, half_weights, by decide +kernel, by
    intro r hr hrs
    apply inW_half
    revert r
    decide +kernel⟩

theorem sc : B.StronglyConnected := by
  unfold StronglyConnected Automaton.IsClosed
  decide +kernel

theorem cfg : B.configOf 0 1 {0, 1} 2 3 = ⟨2, 2, 2, 0, 0, 1⟩ := by decide +kernel

theorem t_vals : (Config.t ⟨2, 2, 2, 0, 0, 1⟩ 0 : ℚ) = 1 / 4 ∧ (Config.t ⟨2, 2, 2, 0, 0, 1⟩ 1 : ℚ) = 1 / 2 := by
  decide +kernel

theorem X_eq : W.X = {2, 3} := by
  unfold QEWitness.X
  decide +kernel

end MergingRemark

open MergingRemark

theorem prop_5_11_merging_remark_proved :
    ∃ W : QEWitness (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]) 2, W.E = {0, 1} ∧ W.s = 1 ∧
      (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).Synchronizing ∧ (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).StronglyConnected ∧
      (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).configOf 0 1 {0, 1} 2 3 = ⟨2, 2, 2, 0, 0, 1⟩ ∧
      (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).pre {1} [0] = {2, 3} ∧ W.X = {2, 3} ∧
      wt ((ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).alphaStat {0, 1} (fun _ => 1 / 2)) {2, 3} = 3 / 4 := by
  refine ⟨W, rfl, rfl, ⟨[0, 0], by unfold IsReset; decide +kernel⟩, sc, cfg, by decide +kernel, X_eq, ?_⟩
  have hb := (lem_5_7_b_proved B 0 1 (by decide) (fun c => by fin_cases c <;> simp) W 2 3 X_eq
    (by decide)).2.2.2.2 sc
  have h0 := hb 0
  have h1 := hb 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  change B.alphaStat {0, 1} (fun _ => 1 / 2) 2 = ((B.configOf 0 1 {0, 1} 2 3).t 0 : ℝ) at h0
  change B.alphaStat {0, 1} (fun _ => 1 / 2) 3 = ((B.configOf 0 1 {0, 1} 2 3).t 1 : ℝ) at h1
  rw [cfg, t_vals.1] at h0
  rw [cfg, t_vals.2] at h1
  rw [wt, Finset.sum_pair (by decide), h0, h1]
  push_cast
  norm_num

end CernyQE
