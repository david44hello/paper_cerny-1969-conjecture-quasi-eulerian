/-
CernyQE/Proofs/Rows5x.lean — Theorem 5.1, Remark 5.4 (d ≤ 2) and Proposition 5.6, with Theorem 4.1 supplied.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Proofs.Sec5x
import CernyQE.Proofs.Rows4

namespace CernyQE

open Classical Automaton Matrix

universe u v

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

theorem thm_5_1_proved (hA : A.Synchronizing) (hn : 3 ≤ Fintype.card Q) (d : ℕ) (hd : d ≤ 2)
    (hqe : QuasiEulerian A d) (hsc : ¬ A.StronglyConnected) : A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_5_1_of (fun _Q' _ _ B hB hn' hqe' => thm_4_1_proved B hB hn' hqe') A hA hn d hd hqe hsc

theorem prop_5_6_proved (hA : A.Synchronizing) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (hblock : A.IsBlockPair x₁ x₂) : A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  prop_5_6_of (fun _Q' _ _ B hB hn' hqe' => thm_4_1_proved B hB hn' hqe') A hA W x₁ x₂ hX h12 hblock

end General

theorem rem_5_4_d2_proved (S : Type v) [Fintype S] (d : ℕ) (hd : d ≤ 2) :
    (∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), B.Synchronizing →
      B.StronglyConnected → (∃ d', 1 ≤ d' ∧ d' ≤ d - 1 ∧ QuasiEulerian B d') →
      B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞)) ∧
    (∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), Fintype.card Q' ≤ d →
      B.Synchronizing → B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞)) :=
  rem_5_4_d2_of S (fun _Q' _ _ B hB hn' hqe' => thm_4_1_proved B hB hn' hqe') d hd

end CernyQE
