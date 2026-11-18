/-
CernyQE/Proofs/Rows4.lean — the rows of Section 4 (degree one), with the exact binders and types of
Paper/Statements.lean, each proved from Proofs/Sec4.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Proofs.Sec4

namespace CernyQE

open Classical Automaton Matrix

universe u v

theorem thm_4_1_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (hqe : QuasiEulerian A 1) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_4_1_core A hA hn hqe

theorem thm_4_1_case_sc_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) :
    (A.zLoop W.p x < 1 → 0 < A.yIn W.E W.p x → A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞)) ∧
      (A.StronglyConnected ↔ A.zLoop W.p x < 1 ∧ 0 < A.yIn W.E W.p x) :=
  thm_4_1_case_sc_core A hA hn W x hx

theorem thm_4_1_case_z1_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) (hz : A.zLoop W.p x = 1) :
    0 < A.yIn W.E W.p x ∧ A.inW W.p x = 1 + A.yIn W.E W.p x ∧ A.inW W.p W.s = 1 - A.yIn W.E W.p x ∧
      (∀ T : Finset Q, x ∈ T → ∑ b, W.p b * ((A.pre T [b]).card : ℝ) = T.card + A.yIn W.E W.p x * (1 - ein W.s T) ∧
        (T.card : ℝ) ≤ ∑ b, W.p b * ((A.pre T [b]).card : ℝ)) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) :=
  thm_4_1_case_z1_core A hA hn W x hx hz

theorem thm_4_1_case_y0_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) (hz : A.zLoop W.p x < 1) (hy : A.yIn W.E W.p x = 0) :
    ∃ hE : A.IsClosed W.E, (∀ r, (A.restrict W.E hE).inW W.p r = 1) ∧
      (3 ≤ Fintype.card Q →
        (A.restrict W.E hE).rt ≤ ((1 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞)) ∧
      (3 ≤ Fintype.card Q → A.rt ≤ ((2 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞)) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) :=
  thm_4_1_case_y0_core A hA hn W x hx hz hy

theorem intro_deg1_nonsc_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) (hsc : ¬ A.StronglyConnected) :
    ((∀ b, A.step x b = x) ∨ A.IsClosed W.E) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) :=
  intro_deg1_nonsc_core A hA hn W x hx hsc

theorem intro_deg1_in_thm31_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hsc : A.StronglyConnected) (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) :
    A.zLoop W.p x < 1 ∧ A.IsStationary W.p (A.alphaDeg1 W.E W.p x) ∧ (∀ q, 0 < A.alphaDeg1 W.E W.p x q) ∧
      ∀ q ∈ W.E, A.alphaDeg1 W.E W.p x q = 1 :=
  intro_deg1_in_thm31_core A hA hsc W x hx

theorem thm_4_1_cn_witness_proved (n : ℕ) [NeZero n] (hn : 2 ≤ n) (p : Fin 2 → ℝ) (hp : IsLetterWeights p) :
    ∃ W : QEWitness (cerny n) 1, W.E = Finset.univ.erase 0 ∧ W.s = 1 ∧ W.p = p :=
  thm_4_1_cn_witness_core n hn p hp

theorem thm_4_1_attained_proved (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (cerny n).Synchronizing ∧ QuasiEulerian (cerny n) 1 ∧ (cerny n).rt = (((n - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_4_1_attained_core n hn

theorem intro_rt_cerny_proved (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (cerny n).rt = (((n - 1) ^ 2 : ℕ) : ℕ∞) :=
  intro_rt_cerny_core n hn

theorem rem_4_3_cn_zyt_proved (n : ℕ) [NeZero n] (hn : 2 ≤ n) (p : Fin 2 → ℝ) (hp : IsLetterWeights p) :
    (cerny n).zLoop p 0 = 0 ∧ (cerny n).yIn (Finset.univ.erase 0) p 0 = p 1 ∧
      (cerny n).yIn (Finset.univ.erase 0) p 0 / (1 - (cerny n).zLoop p 0) = p 1 ∧ 0 < p 1 ∧ p 1 < 1 :=
  rem_4_3_cn_zyt_core n hn p hp

theorem rem_4_3_attained_proved (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (cerny n).rt = ((1 + (n - 2) * n : ℕ) : ℕ∞) :=
  rem_4_3_attained_core n hn

theorem rem_4_3_chain_proved (n : ℕ) [NeZero n] (hn : 2 ≤ n) (K : ℕ → Finset (Fin n)) (w : ℕ → List (Fin 2)) (J : ℕ) (hK0 : K 0 = {0, 1}) (hstep : ∀ j < J, K j ≠ Finset.univ ∧ K (j + 1) = (cerny n).pre (K j) (w j) ∧
      ((w j).length : ℕ∞) = (cerny n).ext (K j) ∧ (K j).card < (K (j + 1)).card) (hJ : K J = Finset.univ) :
    (cerny n).IsReset ((((List.range J).reverse.map w).flatten) ++ [0]) ∧ J = n - 2 ∧
      ∀ j < J, (w j).length = n ∧ (K (j + 1)).card = (K j).card + 1 :=
  rem_4_3_chain_core n hn K w J hK0 hstep hJ

end CernyQE
