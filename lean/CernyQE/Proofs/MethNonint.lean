/-
Proofs/MethNonint.lean — the Method's two step facts for the case t > 2 not an integer (tex:199-200).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.11 - 20261105 — + the chained form (the set does not shrink before the move back).
## version 0.01 - 20261105 — first.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary
import CernyQE.Proofs.Sec3Levels

namespace CernyQE

open Classical Automaton Matrix

universe u v

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

omit [Fintype S] in
/-- Every step of a process raises the value. -/
private theorem process_rises {α : Q → ℝ} {K : ℕ → Finset Q} {w : ℕ → List S} {J : ℕ}
    (hP : A.IsProcess α K w J) {j : ℕ} (hj : j < J) : wt α (K j) < wt α (K (j + 1)) := by
  obtain ⟨-, hK, -, hR⟩ := hP.1 j hj
  rw [hK]
  exact hR

omit [Fintype S] in
theorem meth_nonint_steps_proved (x : Q) (t : ℝ) (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ)
    (hP : A.IsProcess (alphaOff x t) K w J) :
    (∀ j < J, x ∈ K j → x ∉ K (j + 1) → t - 1 < ((K (j + 1)).card : ℝ) - (K j).card) ∧
      (∀ j < J, x ∉ K j → x ∉ K (j + 1) → (K j).card < (K (j + 1)).card) ∧
      (∀ j j', j' < J → (∀ i, j < i → i ≤ j' → x ∉ K i) → ∀ i, j < i → i ≤ j' →
        (K (j + 1)).card ≤ (K i).card) := by
  have hlose : ∀ j < J, x ∈ K j → x ∉ K (j + 1) → t - 1 < ((K (j + 1)).card : ℝ) - (K j).card := by
    intro j hj hx hx'
    have hlev := lem_3_2_a_proved x t (K j) (K (j + 1))
    have hup := process_rises A hP hj
    simp only [ein, hx, hx', ↓reduceIte] at hlev
    linarith
  have hfree : ∀ j < J, x ∉ K j → x ∉ K (j + 1) → (K j).card < (K (j + 1)).card := by
    intro j hj hx hx'
    have hlev := lem_3_2_a_proved x t (K j) (K (j + 1))
    have hup := process_rises A hP hj
    simp only [ein, hx, hx', ↓reduceIte] at hlev
    have hreal : ((K j).card : ℝ) < (K (j + 1)).card := by linarith
    exact_mod_cast hreal
  refine ⟨hlose, hfree, ?_⟩
  intro j j' hj'J hout i hi hij'
  have hi' : j + 1 ≤ i := hi
  induction i, hi' using Nat.le_induction with
  | base => exact le_rfl
  | succ i hji ih =>
    have hstep := hfree i (by omega) (hout i (by omega) (by omega)) (hout (i + 1) (by omega) hij')
    exact (ih (by omega) (by omega)).trans hstep.le

end General

end CernyQE
