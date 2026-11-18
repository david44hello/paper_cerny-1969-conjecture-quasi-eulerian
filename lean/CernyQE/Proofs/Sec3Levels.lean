/-
CernyQE/Proofs/Sec3Levels.lean — the levels of a vector constant off one state: Lemma 3.2 and its consequences.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary

namespace CernyQE

open Classical Automaton Matrix

universe u v

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-! ### Small facts on least lengths -/

omit [Fintype S] in
private theorem minLen_le_length' {P : List S → Prop} {w : List S} (h : P w) : minLen P ≤ w.length :=
  iInf₂_le w h

omit [Fintype S] in
private theorem minLen_mono' {P P' : List S → Prop} (h : ∀ w, P w → P' w) : minLen P' ≤ minLen P :=
  le_iInf₂ fun w hw => minLen_le_length' (h w hw)

/-! ### Moving a state across a set -/

omit [Fintype S] in
/-- `w` moves `x` across `K` iff `x` lies in exactly one of the sets `K w⁻¹` and `K`. -/
private theorem movesAcross_iff' (x : Q) (K : Finset Q) (w : List S) :
    A.MovesAcross x K w ↔ ¬ (x ∈ A.pre K w ↔ x ∈ K) := by
  simp only [Automaton.MovesAcross, Automaton.pre, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
    decide_eq_decide]

/-! ### The weight of a set for a vector constant off one state -/

omit [Fintype Q] in
/-- If `α = c` off `x`, then `α(K) = c |K| + (α_x - c) [x ∈ K]`. -/
private theorem wt_const_off (α : Q → ℝ) (x : Q) (c : ℝ) (hα : ∀ q, q ≠ x → α q = c) (K : Finset Q) :
    wt α K = c * K.card + (α x - c) * ein x K := by
  have h : ∀ q, α q = c + (α x - c) * (if q = x then 1 else 0) := by
    intro q
    by_cases hq : q = x
    · subst hq
      simp
    · simp [hq, hα q hq]
  unfold wt ein
  rw [Finset.sum_congr rfl (fun q _ => h q), Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_ite_eq']
  split_ifs <;> ring

omit [Fintype Q] in
private theorem wt_alphaOff (x : Q) (t : ℝ) (K : Finset Q) :
    wt (alphaOff x t) K = K.card + (t - 1) * ein x K := by
  have hx : alphaOff x t x = t := by simp [alphaOff]
  rw [wt_const_off (alphaOff x t) x 1 (fun q hq => by simp [alphaOff, hq]) K, hx]
  ring

/-- If `t - 1` is not an integer, two sets have the same `α` iff they have the same size and the same side of `x`. -/
private theorem wt_alphaOff_eq_iff (x : Q) (t : ℝ) (hg : ¬ ∃ z : ℤ, t - 1 = z) (K K' : Finset Q) :
    wt (alphaOff x t) K' = wt (alphaOff x t) K ↔ K'.card = K.card ∧ (x ∈ K' ↔ x ∈ K) := by
  rw [wt_alphaOff, wt_alphaOff]
  constructor
  · intro h
    by_cases hx' : x ∈ K' <;> by_cases hx : x ∈ K <;>
      simp only [ein, hx, hx', ↓reduceIte, mul_one, mul_zero, add_zero] at h
    · exact ⟨by exact_mod_cast (by linarith : (K'.card : ℝ) = K.card), iff_of_true hx' hx⟩
    · exact (hg ⟨(K.card : ℤ) - K'.card, by push_cast; linarith⟩).elim
    · exact (hg ⟨(K'.card : ℤ) - K.card, by push_cast; linarith⟩).elim
    · exact ⟨by exact_mod_cast (by linarith : (K'.card : ℝ) = K.card), iff_of_false hx' hx⟩
  · rintro ⟨hc, hm⟩
    have he : ein x K' = ein x K := by simp only [ein, hm]
    rw [hc, he]

/-! ### The rows -/

/-- tex:386-387: `α(K) = |K| + g [x ∈ K]` and `α(Q) = n - 1 + t`, `g = t - 1`. -/
theorem sec3_alpha_formula_proved (x : Q) (t : ℝ) :
    (∀ K : Finset Q, wt (alphaOff x t) K = K.card + (t - 1) * ein x K) ∧
      wt (alphaOff x t) Finset.univ = Fintype.card Q - 1 + t := by
  refine ⟨wt_alphaOff x t, ?_⟩
  rw [wt_alphaOff, Finset.card_univ]
  simp only [ein, Finset.mem_univ, ↓reduceIte]
  ring

/-- Lemma 3.2(a) (levels), tex:394. -/
theorem lem_3_2_a_proved (x : Q) (t : ℝ) (K K' : Finset Q) :
    wt (alphaOff x t) K' - wt (alphaOff x t) K = ((K'.card : ℝ) - K.card) + (t - 1) * (ein x K' - ein x K) := by
  rw [wt_alphaOff, wt_alphaOff]
  ring

/-- tex:195: if `t - 1` is not an integer, every word that moves `x` across a set changes `α`. -/
theorem meth_move_changes_proved (x : Q) (t : ℝ) (ht : ¬ ∃ z : ℤ, t - 1 = z) (K : Finset Q) (w : List S)
    (hw : A.MovesAcross x K w) : wt (alphaOff x t) (A.pre K w) ≠ wt (alphaOff x t) K := by
  intro h
  exact (movesAcross_iff' A x K w).mp hw ((wt_alphaOff_eq_iff x t ht K (A.pre K w)).mp h).2

/-- Lemma 3.2(b), tex:395-397. -/
theorem lem_3_2_b_proved (x : Q) (t : ℝ) (hg : ¬ ∃ z : ℤ, t - 1 = z) :
    (∀ K K' : Finset Q, wt (alphaOff x t) K' = wt (alphaOff x t) K ↔ K'.card = K.card ∧ (x ∈ K' ↔ x ∈ K)) ∧
      ∀ K : Finset Q,
        A.cost (alphaOff x t) K = minLen (fun w => (A.pre K w).card ≠ K.card ∨ A.MovesAcross x K w) ∧
          A.cost (alphaOff x t) K ≤ A.esc x K ∧
          ∀ w : List S, (w.length : ℕ∞) = A.cost (alphaOff x t) K → A.Raises (alphaOff x t) K w →
            A.MovesAcross x K w → A.cost (alphaOff x t) K = A.esc x K := by
  have hle : ∀ K : Finset Q, A.cost (alphaOff x t) K ≤ A.esc x K := fun K =>
    minLen_mono' (fun w hw => meth_move_changes_proved A x t hg K w hw)
  refine ⟨wt_alphaOff_eq_iff x t hg, fun K => ⟨?_, hle K, ?_⟩⟩
  · unfold Automaton.cost
    refine congrArg minLen (funext fun w => propext ?_)
    rw [ne_eq, wt_alphaOff_eq_iff x t hg K (A.pre K w), movesAcross_iff', not_and_or, ne_eq]
  · intro w hlen _ hmove
    have hesc : A.esc x K ≤ w.length := minLen_le_length' hmove
    exact le_antisymm (hle K) (hesc.trans_eq hlen)

/-- Lemma 3.2(c), tex:398-400. -/
theorem lem_3_2_c_proved (x : Q) (t : ℝ) (h0 : 0 < t) (h2 : t < 2) (_h1 : t ≠ 1) (K K' : Finset Q)
    (hlt : wt (alphaOff x t) K < wt (alphaOff x t) K') :
    K.card ≤ K'.card ∧ (K'.card = K.card → (1 < t → x ∉ K ∧ x ∈ K') ∧ (t < 1 → x ∈ K ∧ x ∉ K')) := by
  rw [wt_alphaOff, wt_alphaOff] at hlt
  refine ⟨?_, fun hc => ?_⟩
  · have hgt : (K.card : ℝ) < K'.card + 1 := by
      by_cases hx' : x ∈ K' <;> by_cases hx : x ∈ K <;>
        simp only [ein, hx, hx', ↓reduceIte, mul_one, mul_zero, add_zero] at hlt <;> linarith
    have hnat : K.card < K'.card + 1 := by exact_mod_cast hgt
    omega
  · rw [hc] at hlt
    by_cases hx' : x ∈ K' <;> by_cases hx : x ∈ K <;>
      simp only [ein, hx, hx', ↓reduceIte, mul_one, mul_zero, add_zero] at hlt
    all_goals first
      | exact absurd hlt (lt_irrefl _)
      | exact ⟨fun _ => ⟨hx, hx'⟩, fun ht => (by linarith : False).elim⟩
      | exact ⟨fun ht => (by linarith : False).elim, fun _ => ⟨hx, hx'⟩⟩

/-- tex:408-410: a raising word that keeps the size of an expensive set moves `x` across it and makes it cheap; a
raising word always enlarges a cheap set. -/
theorem sec3_expensive_cheap_proved (x : Q) (t : ℝ) (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) (K : Finset Q)
    (w : List S) (hw : A.Raises (alphaOff x t) K w) :
    ((A.pre K w).card = K.card → Expensive x t K → A.MovesAcross x K w ∧ ¬ Expensive x t (A.pre K w)) ∧
      (¬ Expensive x t K → K.card < (A.pre K w).card) := by
  obtain ⟨hle, hside⟩ := lem_3_2_c_proved x t h0 h2 h1 K (A.pre K w) hw
  refine ⟨fun hc _ => ?_, fun hcheap => ?_⟩
  · rw [movesAcross_iff']
    obtain ⟨hgt, hlt⟩ := hside hc
    rcases lt_or_gt_of_ne h1 with ht | ht
    · obtain ⟨hxK, hxK'⟩ := hlt ht
      refine ⟨fun h => hxK' (h.mpr hxK), fun hE => ?_⟩
      unfold Expensive at hE
      rcases hE with ⟨ht', _⟩ | ⟨_, hx⟩
      · linarith
      · exact hxK' hx
    · obtain ⟨hxK, hxK'⟩ := hgt ht
      refine ⟨fun h => hxK (h.mp hxK'), fun hE => ?_⟩
      unfold Expensive at hE
      rcases hE with ⟨_, hx⟩ | ⟨ht', _⟩
      · exact hx hxK'
      · linarith
  · refine lt_of_le_of_ne hle (fun hc => hcheap ?_)
    obtain ⟨hgt, hlt⟩ := hside hc.symm
    show (1 < t ∧ x ∉ K) ∨ (t < 1 ∧ x ∈ K)
    rcases lt_or_gt_of_ne h1 with ht | ht
    · exact Or.inr ⟨ht, (hlt ht).1⟩
    · exact Or.inl ⟨ht, (hgt ht).1⟩

/-- tex:191-192: when `α` is constant (`c > 0`) off one state `x`, a raising word either enlarges the set or moves `x`
across it. -/
theorem meth_raise_enlarge_or_move_proved (α : Q → ℝ) (x : Q) (c : ℝ) (hc : 0 < c) (hα : ∀ q, q ≠ x → α q = c)
    (K : Finset Q) (w : List S) (hw : A.Raises α K w) :
    K.card < (A.pre K w).card ∨ A.MovesAcross x K w := by
  by_contra hcon
  obtain ⟨hnlt, hmove⟩ := not_or.mp hcon
  rw [movesAcross_iff', not_not] at hmove
  have he : ein x (A.pre K w) = ein x K := by simp only [ein, hmove]
  have hraise : wt α K < wt α (A.pre K w) := hw
  rw [wt_const_off α x c hα, wt_const_off α x c hα, he] at hraise
  have hcard : ((A.pre K w).card : ℝ) ≤ K.card := by exact_mod_cast not_lt.mp hnlt
  have hmul := mul_le_mul_of_nonneg_left hcard hc.le
  linarith

end General

end CernyQE
