/-
CernyQE/Proofs/Examples1.lean — the claims on Example 3.5, the 4-state automaton of Remark 4.4 and a supplementary circular example.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary
import CernyQE.Defs.Examples

namespace CernyQE

open Classical Automaton Matrix

universe u v

/-! ### Small helpers: least lengths, words over `Fin 2`, weights `(1/2, 1/2)` -/

/-- `minLen P = k` when some word of length `k` has `P` and no shorter word has it. -/
private theorem minLen_eq_of {S : Type*} {P : List S → Prop} (k : ℕ) (w₀ : List S) (h₀ : P w₀)
    (hk : w₀.length = k) (hlt : ∀ w : List S, w.length < k → ¬ P w) : minLen P = k := by
  unfold minLen
  apply le_antisymm
  · exact (iInf₂_le w₀ h₀).trans_eq (by rw [hk])
  · refine le_iInf₂ fun w hw => ?_
    by_contra h
    exact hlt w (by exact_mod_cast not_le.mp h) hw

/-- All words of length `m` over `Fin 2`. -/
private def words2 : ℕ → List (List (Fin 2))
  | 0 => [[]]
  | m + 1 => (words2 m).flatMap fun w => [0 :: w, 1 :: w]

private theorem mem_words2 (w : List (Fin 2)) : w ∈ words2 w.length := by
  induction w with
  | nil => simp [words2]
  | cons b w ih =>
    simp only [List.length_cons, words2, List.mem_flatMap]
    refine ⟨w, ih, ?_⟩
    fin_cases b <;> simp

/-- A property of words that fails on the finite lists `words2 m`, `m < k`, fails on every word shorter than `k`. -/
private theorem short_of_words2 {P : List (Fin 2) → Prop} {k : ℕ} (h : ∀ m < k, ∀ w ∈ words2 m, ¬ P w) :
    ∀ w : List (Fin 2), w.length < k → ¬ P w :=
  fun w hw => h w.length hw w (mem_words2 w)

/-- The `r`-th entry of `αᵀ M`: the weighted sum of `α` over the edges that end at `r`. -/
private theorem vecMul_M_apply {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]
    (A : Automaton Q S) (p : S → ℝ) (α : Q → ℝ) (r : Q) :
    vecMul α (A.M p) r = ∑ b, p b * ∑ q, if A.step q b = r then α q else 0 := by
  simp only [vecMul, dotProduct, M, Mw, Matrix.sum_apply, Matrix.smul_apply, act, List.foldl_cons,
    List.foldl_nil, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : A.step q b = r <;> simp [hq, mul_comm]

/-- With the weights `(1/2, 1/2)`, a vector of natural numbers `u` is stationary when, at every state `r`, the sum of
`u` over the edges that end at `r` is `2 u(r)`. -/
private theorem stat_half_nat {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]
    (A : Automaton Q S) (α : Q → ℝ) (u : Q → ℕ) (hαu : ∀ q, α q = u q) (hu : ∃ q, u q ≠ 0)
    (h : ∀ r, ∑ b, ∑ q, (if A.step q b = r then u q else 0) = 2 * u r) :
    A.IsStationary (fun _ => 1 / 2) α := by
  refine ⟨fun h0 => ?_, funext fun r => ?_⟩
  · obtain ⟨q, hq⟩ := hu
    have := congrFun h0 q
    rw [hαu, Pi.zero_apply] at this
    exact hq (by exact_mod_cast this)
  · have hr : ((∑ b, ∑ q, (if A.step q b = r then u q else 0) : ℕ) : ℝ) = 2 * (u r : ℝ) := by
      exact_mod_cast h r
    push_cast at hr
    rw [vecMul_M_apply, ← Finset.mul_sum, hαu]
    simp_rw [hαu]
    rw [hr]
    ring

/-- `(1/2, 1/2)` are letter weights. -/
private theorem half_weights : IsLetterWeights (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
  refine ⟨fun _ => by norm_num, ?_⟩
  rw [Fin.sum_univ_two]
  norm_num

/-- With the weights `(1/2, 1/2)`, a state entered by exactly two edges has in-weight one. -/
private theorem inW_half {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]
    (A : Automaton Q S) (r : Q) (h : ∑ b, (A.pre {r} [b]).card = 2) : A.inW (fun _ => 1 / 2) r = 1 := by
  have h' : (∑ b, ((A.pre {r} [b]).card : ℝ)) = 2 := by exact_mod_cast h
  rw [inW, ← Finset.mul_sum, h']
  norm_num

/-! ### Example 3.5 -/

private theorem ex35_reset : ex35.IsReset [0, 1, 0, 0, 1] := by
  unfold IsReset
  decide +kernel

theorem ex_3_5_rt_proved : ex35.rt = 5 ∧ ex35.img Finset.univ [0, 1, 0, 0, 1] = {4} := by
  refine ⟨?_, by decide +kernel⟩
  have h := minLen_eq_of (P := ex35.IsReset) 5 [0, 1, 0, 0, 1] ex35_reset rfl
    (short_of_words2 (by unfold IsReset; decide +kernel))
  rw [rt, h]
  rfl

/-- The vector `(1,1,1,1,2)` (that is, `1` off `4` and `2` at `4`) is stationary for `(1/2, 1/2)`. -/
private theorem ex35_stat (α : Fin 5 → ℝ) (hα : ∀ q, α q = ((if q = 4 then 2 else 1 : ℕ) : ℝ)) :
    ex35.IsStationary (fun _ => 1 / 2) α :=
  stat_half_nat ex35 α (fun q => if q = 4 then 2 else 1) hα ⟨0, by decide⟩ (by decide +kernel)

theorem ex_3_5_stationary_proved :
    ex35.IsStationary (fun _ => 1 / 2) ![1, 1, 1, 1, 2] ∧
      ex35.pre {0} [0] = {4} ∧ ex35.pre {0} [1] = ∅ ∧ ex35.pre {1} [0] = ∅ ∧ ex35.pre {1} [1] = {4} ∧
      (∀ r : Fin 5, r = 2 ∨ r = 3 →
        (ex35.pre {r} [0]).card + (ex35.pre {r} [1]).card = 2 ∧ ex35.pre {r} [0] ∪ ex35.pre {r} [1] ⊆ {0, 1, 2, 3}) ∧
      (ex35.pre {4} [0]).card + (ex35.pre {4} [1]).card = 4 ∧ ex35.pre {4} [0] ∪ ex35.pre {4} [1] ⊆ {0, 1, 2, 3} := by
  refine ⟨ex35_stat _ fun q => ?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  fin_cases q <;> simp

theorem ex_3_5_in_thm31_proved :
    ex35.Synchronizing ∧ IsLetterWeights (fun _ : Fin 2 => (1 / 2 : ℝ)) ∧
      ex35.IsStationary (fun _ => 1 / 2) (alphaOff 4 2) := by
  refine ⟨⟨_, ex35_reset⟩, half_weights, ex35_stat _ fun q => ?_⟩
  by_cases hq : q = 4 <;> simp [alphaOff, hq]

theorem ex_3_5_inedges_proved (p : Fin 2 → ℝ) (hp : IsLetterWeights p) :
    ex35.inW p 0 ≠ 1 ∧ ex35.inW p 1 ≠ 1 ∧ ex35.inW p 4 ≠ 1 := by
  obtain ⟨hpos, hsum⟩ := hp
  rw [Fin.sum_univ_two] at hsum
  have h00 : (ex35.pre {0} [0]).card = 1 := by decide +kernel
  have h01 : (ex35.pre {0} [1]).card = 0 := by decide +kernel
  have h10 : (ex35.pre {1} [0]).card = 0 := by decide +kernel
  have h11 : (ex35.pre {1} [1]).card = 1 := by decide +kernel
  have h40 : (ex35.pre {4} [0]).card = 2 := by decide +kernel
  have h41 : (ex35.pre {4} [1]).card = 2 := by decide +kernel
  have hp0 := hpos 0
  have hp1 := hpos 1
  simp only [inW, Fin.sum_univ_two, h00, h01, h10, h11, h40, h41]
  push_cast
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith

/-- The finite part of "not quasi-Eulerian of degree one or two": if `E \ {s} ⊆ {2, 3}` and every edge from `Q \ E`
ends in `(Q \ E) ∪ {s}`, then `|E|` is neither `4` nor `3`. -/
private theorem ex35_finite :
    ∀ (E : Finset (Fin 5)) (s : Fin 5), s ∈ E → (∀ r ∈ E, r ≠ s → r = 2 ∨ r = 3) →
      (∀ q, q ∉ E → ∀ b, ex35.step q b ∉ E ∨ ex35.step q b = s) → E.card ≠ 4 ∧ E.card ≠ 3 := by
  decide +kernel

private theorem ex35_witness_card {d : ℕ} (W : QEWitness ex35 d) : W.E.card ≠ 4 ∧ W.E.card ≠ 3 := by
  refine ex35_finite W.E W.s W.s_mem (fun r hr hrs => ?_) W.edge_X
  have h1 := W.inW_one r hr hrs
  obtain ⟨h0, h1', h4⟩ := ex_3_5_inedges_proved W.p W.weights
  fin_cases r
  · exact absurd h1 h0
  · exact absurd h1 h1'
  · simp
  · simp
  · exact absurd h1 h4

theorem ex_3_5_not_qe12_proved : ¬ QuasiEulerian ex35 1 ∧ ¬ QuasiEulerian ex35 2 := by
  refine ⟨fun ⟨W⟩ => (ex35_witness_card W).1 ?_, fun ⟨W⟩ => (ex35_witness_card W).2 ?_⟩
  · rw [W.card_E]; rfl
  · rw [W.card_E]; rfl

theorem ex_3_5_one_cluster_proved : cycles (fun q => ex35.step q 0) = {{0, 2, 3, 4}} ∧ OneCluster ex35 := by
  have h : cycles (fun q => ex35.step q 0) = {{0, 2, 3, 4}} := by decide +kernel
  exact ⟨h, ⟨0, by rw [h]; rfl⟩⟩

/-! ### The 4-state automaton of Remark 4.4 -/

theorem intro_ex4_reset_proved : exIntro4.IsReset [0, 1, 1, 0, 1, 1, 0] := by
  unfold IsReset
  decide +kernel

theorem intro_ex4_cycles_proved :
    cycles (fun q => exIntro4.step q 0) = {{0}, {1, 2}} ∧ cycles (fun q => exIntro4.step q 1) = {{0, 1, 3}, {2}} :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem intro_ex4_qe1_proved :
    exIntro4.Synchronizing ∧ (∀ c, exIntro4.step 3 c = 0) ∧
      (∀ r : Fin 4, r = 1 ∨ r = 2 → ∀ c, (exIntro4.pre {r} [c]).card = 1) ∧
      ∃ W : QEWitness exIntro4 1, W.E = {0, 1, 2} ∧ W.s = 0 := by
  refine ⟨⟨_, intro_ex4_reset_proved⟩, by decide +kernel, by decide +kernel, ?_⟩
  refine ⟨⟨{0, 1, 2}, 0, fun _ => 1 / 2, by rfl, by decide +kernel, half_weights, by decide +kernel, ?_⟩, rfl, rfl⟩
  intro r hr hrs
  apply inW_half
  revert r
  decide +kernel

theorem intro_incomparable_proved :
    (ex35.Synchronizing ∧ OneCluster ex35 ∧ ¬ QuasiEulerian ex35 1) ∧
      (exIntro4.Synchronizing ∧ QuasiEulerian exIntro4 1 ∧ ¬ OneCluster exIntro4) := by
  obtain ⟨hsync, -, -, W, -, -⟩ := intro_ex4_qe1_proved
  refine ⟨⟨⟨_, ex35_reset⟩, ex_3_5_one_cluster_proved.2, ex_3_5_not_qe12_proved.1⟩, hsync, ⟨W⟩, ?_⟩
  rintro ⟨b, hb⟩
  obtain ⟨h0, h1⟩ := intro_ex4_cycles_proved
  fin_cases b
  · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, h0] at hb
    exact absurd hb (by decide)
  · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, h1] at hb
    exact absurd hb (by decide)

/-! ### Supplement: a circular automaton with an excluded configuration -/

theorem sec6_some_circular_proved :
    ∃ W : QEWitness (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]) 2, W.E = {1, 2} ∧ W.s = 1 ∧
      (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).Synchronizing ∧ (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).StronglyConnected ∧
      (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).configOf 0 1 {1, 2} 0 3 ∈ openConfigs ∧
      Function.Bijective (fun q => (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).step q 0) ∧
      cycles (fun q => (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).step q 0) = {Finset.univ} := by
  refine ⟨⟨{1, 2}, 1, fun _ => 1 / 2, by rfl, by decide +kernel, half_weights, by decide +kernel, ?_⟩, rfl, rfl,
    ⟨[1, 1, 0, 1, 1], by unfold IsReset; decide +kernel⟩, by unfold StronglyConnected Automaton.IsClosed; decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro r hr hrs
  apply inW_half
  revert r
  decide +kernel

end CernyQE
