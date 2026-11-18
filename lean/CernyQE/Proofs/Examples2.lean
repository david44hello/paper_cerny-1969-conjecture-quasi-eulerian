/-
CernyQE/Proofs/Examples2.lean — the claims on Example 3.6, the Cerny automaton's set K_0 and the 4-state example of Remark 4.3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Examples

namespace CernyQE

open Classical Automaton Matrix

universe u v

/-! ### Small helpers: least lengths, words over `Fin 2`, weights `(1/2, 1/2)`, irrational numbers -/

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

/-- If `x = a + b y` with rational `a, b` and `x` is irrational, then `y` is irrational. -/
private theorem irr_of_affine {x y : ℝ} (hx : Irrational x) (a b : ℚ) (h : x = a + b * y) : Irrational y := by
  rintro ⟨z, rfl⟩
  exact hx ⟨a + b * z, by rw [h]; push_cast; ring⟩

/-! ### Example 3.6: `a = (0,0,0)`, `b = (1,2,1)` -/

/-- The three equations of `αᵀ M = αᵀ` for Example 3.6. -/
private theorem ex36_stat_iff (p : Fin 2 → ℝ) (α : Fin 3 → ℝ) :
    ex36.IsStationary p α ↔
      α ≠ 0 ∧ p 0 * (α 0 + α 1 + α 2) = α 0 ∧ p 1 * (α 0 + α 2) = α 1 ∧ p 1 * α 1 = α 2 := by
  have h0 : vecMul α (ex36.M p) 0 = p 0 * (α 0 + α 1 + α 2) := by
    rw [vecMul_M_apply]
    simp [Fin.sum_univ_two, Fin.sum_univ_three, ex36, ofLists]
  have h1 : vecMul α (ex36.M p) 1 = p 1 * (α 0 + α 2) := by
    rw [vecMul_M_apply]
    simp [Fin.sum_univ_two, Fin.sum_univ_three, ex36, ofLists]
  have h2 : vecMul α (ex36.M p) 2 = p 1 * α 1 := by
    rw [vecMul_M_apply]
    simp [Fin.sum_univ_two, Fin.sum_univ_three, ex36, ofLists]
  unfold Automaton.IsStationary
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, h0 ▸ congrFun h 0, h1 ▸ congrFun h 1, h2 ▸ congrFun h 2⟩
  · rintro ⟨hne, e0, e1, e2⟩
    refine ⟨hne, funext fun r => ?_⟩
    fin_cases r
    · exact h0.trans e0
    · exact h1.trans e1
    · exact h2.trans e2

/-- The same equations for a vector written `![a₀, a₁, a₂]`. -/
private theorem ex36_stat_vec (p : Fin 2 → ℝ) (a₀ a₁ a₂ : ℝ) :
    ex36.IsStationary p ![a₀, a₁, a₂] ↔
      (a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ a₂ ≠ 0) ∧ p 0 * (a₀ + a₁ + a₂) = a₀ ∧ p 1 * (a₀ + a₂) = a₁ ∧ p 1 * a₁ = a₂ := by
  rw [ex36_stat_iff]
  have hne : (![a₀, a₁, a₂] : Fin 3 → ℝ) ≠ 0 ↔ (a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ a₂ ≠ 0) := by
    constructor
    · intro h
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply h
      funext i
      fin_cases i <;> simp [hc.1, hc.2.1, hc.2.2]
    · rintro h h0
      have e0 := congrFun h0 0
      have e1 := congrFun h0 1
      have e2 := congrFun h0 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Pi.zero_apply] at e0 e1 e2
      tauto
  rw [hne]
  exact Iff.rfl

private theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private theorem inv_sqrt2 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  have hpos : 0 < Real.sqrt 2 := by positivity
  rw [div_eq_div_iff hpos.ne' two_ne_zero]
  linear_combination -sqrt2_sq

/-- `x = 2`: the equations force `t = p_b` and `t² + t - 1 = 0`. -/
private theorem ex36_x2_solve (p : Fin 2 → ℝ) (hp : IsLetterWeights p) (t : ℝ)
    (e0 : p 0 * (2 + t) = 1) (e1 : p 1 * (1 + t) = 1) :
    t = p 1 ∧ t ^ 2 + t - 1 = 0 ∧ t = (Real.sqrt 5 - 1) / 2 ∧ p 0 = (3 - Real.sqrt 5) / 2 := by
  obtain ⟨hpos, hsum⟩ := hp
  rw [Fin.sum_univ_two] at hsum
  have ht : t = p 1 := by linear_combination e0 + e1 - (2 + t) * hsum
  have hq : t ^ 2 + t - 1 = 0 := by linear_combination e1 + (1 + t) * ht
  have htpos : 0 < t := ht ▸ hpos 1
  have hprod : (t - (Real.sqrt 5 - 1) / 2) * (t + (Real.sqrt 5 + 1) / 2) = 0 := by
    linear_combination hq - (1 / 4 : ℝ) * sqrt5_sq
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have ht' : t = (Real.sqrt 5 - 1) / 2 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  exact ⟨ht, hq, ht', by linarith⟩

theorem ex_3_6_x2_proved :
    (∀ (p : Fin 2 → ℝ), IsLetterWeights p → ∀ t : ℝ,
      (ex36.IsStationary p ![1, 1, t] ↔ p 0 * (2 + t) = 1 ∧ p 1 * (1 + t) = 1) ∧
      (p 0 * (2 + t) = 1 ∧ p 1 * (1 + t) = 1 →
        t ^ 2 + t - 1 = 0 ∧ t = (Real.sqrt 5 - 1) / 2 ∧ p 0 = (3 - Real.sqrt 5) / 2)) ∧
    IsLetterWeights ![(3 - Real.sqrt 5) / 2, (Real.sqrt 5 - 1) / 2] ∧
      ex36.IsStationary ![(3 - Real.sqrt 5) / 2, (Real.sqrt 5 - 1) / 2] ![1, 1, (Real.sqrt 5 - 1) / 2] := by
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hlt : Real.sqrt 5 < 3 := by nlinarith [sqrt5_sq]
  have hgt : 1 < Real.sqrt 5 := by nlinarith [sqrt5_sq]
  refine ⟨fun p hp t => ⟨?_, fun ⟨e0, e1⟩ => (ex36_x2_solve p hp t e0 e1).2⟩, ?_, ?_⟩
  · rw [ex36_stat_vec]
    constructor
    · rintro ⟨-, e0, e1, -⟩
      exact ⟨by linear_combination e0, by linear_combination e1⟩
    · rintro ⟨e0, e1⟩
      have ht := (ex36_x2_solve p hp t e0 e1).1
      exact ⟨Or.inl one_ne_zero, by linear_combination e0, by linear_combination e1, by linear_combination -ht⟩
  · refine ⟨fun b => ?_, ?_⟩
    · fin_cases b
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        linarith
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        linarith
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
  · rw [ex36_stat_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨Or.inl one_ne_zero, ?_, ?_, ?_⟩
    · linear_combination (-1 / 4 : ℝ) * sqrt5_sq
    · linear_combination (1 / 4 : ℝ) * sqrt5_sq
    · ring

/-- `x = 1`: the equations force `2 p_b = t` and `p_b t = 1`, so `p_b = √2/2` and `t = √2`. -/
private theorem ex36_x1_solve (p : Fin 2 → ℝ) (hp : IsLetterWeights p) (t : ℝ)
    (hα : ex36.IsStationary p ![1, t, 1]) : t = Real.sqrt 2 ∧ p 1 = Real.sqrt 2 / 2 := by
  obtain ⟨hpos, -⟩ := hp
  obtain ⟨-, -, e1, e2⟩ := (ex36_stat_vec p 1 t 1).mp hα
  have hq : 2 * p 1 ^ 2 = 1 := by linear_combination p 1 * e1 + e2
  have hprod : (p 1 - Real.sqrt 2 / 2) * (p 1 + Real.sqrt 2 / 2) = 0 := by
    linear_combination (1 / 2 : ℝ) * hq - (1 / 4 : ℝ) * sqrt2_sq
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hp1 := hpos 1
  have hp1' : p 1 = Real.sqrt 2 / 2 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  exact ⟨by linear_combination -e1 + 2 * hp1', hp1'⟩

theorem ex_3_6_x1_proved :
    (∀ (p : Fin 2 → ℝ), IsLetterWeights p → ∀ t : ℝ, ex36.IsStationary p ![1, t, 1] →
      t = Real.sqrt 2 ∧ p 1 = 1 / Real.sqrt 2) ∧
    IsLetterWeights ![1 - 1 / Real.sqrt 2, 1 / Real.sqrt 2] ∧
      ex36.IsStationary ![1 - 1 / Real.sqrt 2, 1 / Real.sqrt 2] ![1, Real.sqrt 2, 1] := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlt : Real.sqrt 2 < 2 := by nlinarith [sqrt2_sq]
  have hgt : 0 < Real.sqrt 2 := by positivity
  refine ⟨fun p hp t hα => ?_, ⟨fun b => ?_, ?_⟩, ?_⟩
  · obtain ⟨ht, hp1⟩ := ex36_x1_solve p hp t hα
    exact ⟨ht, by rw [hp1, inv_sqrt2]⟩
  · fin_cases b
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, inv_sqrt2]
      linarith
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, inv_sqrt2]
      linarith
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · rw [ex36_stat_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, inv_sqrt2]
    refine ⟨Or.inl one_ne_zero, ?_, ?_, ?_⟩
    · linear_combination (-1 / 2 : ℝ) * sqrt2_sq
    · ring
    · linear_combination (1 / 2 : ℝ) * sqrt2_sq

theorem ex_3_6_x0_proved (p : Fin 2 → ℝ) (hp : IsLetterWeights p) (t : ℝ) : ¬ ex36.IsStationary p ![t, 1, 1] := by
  intro hα
  obtain ⟨hpos, hsum⟩ := hp
  rw [Fin.sum_univ_two] at hsum
  obtain ⟨-, -, -, e2⟩ := (ex36_stat_vec p t 1 1).mp hα
  have := hpos 0
  linarith

theorem ex_3_6_irrational_proved (x : Fin 3) (p : Fin 2 → ℝ) (hp : IsLetterWeights p) (t : ℝ)
    (hα : ex36.IsStationary p (alphaOff x t)) : Irrational (p 0) ∧ Irrational (p 1) := by
  have hsum := hp.2
  rw [Fin.sum_univ_two] at hsum
  fin_cases x
  · have h : alphaOff (0 : Fin 3) t = ![t, 1, 1] := by
      funext i
      fin_cases i <;> simp [alphaOff]
    exact absurd (h ▸ hα) (ex_3_6_x0_proved p hp t)
  · have h : alphaOff (1 : Fin 3) t = ![1, t, 1] := by
      funext i
      fin_cases i <;> simp [alphaOff]
    have hp1 := (ex36_x1_solve p hp t (h ▸ hα)).2
    exact ⟨irr_of_affine irrational_sqrt_two 2 (-2) (by push_cast; linarith),
      irr_of_affine irrational_sqrt_two 0 2 (by push_cast; linarith)⟩
  · have h : alphaOff (2 : Fin 3) t = ![1, 1, t] := by
      funext i
      fin_cases i <;> simp [alphaOff]
    obtain ⟨-, e0, e1, -⟩ := (ex36_stat_vec p 1 1 t).mp (h ▸ hα)
    have hp0 := (ex36_x2_solve p hp t (by linear_combination e0) (by linear_combination e1)).2.2.2
    have h5 : Irrational (Real.sqrt 5) := Nat.prime_five.irrational_sqrt
    exact ⟨irr_of_affine h5 3 (-2) (by push_cast; linarith), irr_of_affine h5 1 2 (by push_cast; linarith)⟩

theorem ex_3_6_sync_proved : ex36.IsReset [0] ∧ ex36.rt = 1 := by
  have hr : ex36.IsReset [0] := by
    unfold IsReset
    decide +kernel
  refine ⟨hr, ?_⟩
  have h := minLen_eq_of (P := ex36.IsReset) 1 [0] hr rfl (short_of_words2 (by unfold IsReset; decide +kernel))
  rw [rt, h]
  rfl

/-! ### Remark 4.3 -/

theorem rem_4_3_K0_proved (n : ℕ) [NeZero n] (_hn : 2 ≤ n) : (cerny n).pre {1} [0] = {0, 1} := by
  ext q
  simp only [pre, act, List.foldl_cons, List.foldl_nil, cerny, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_insert]
  by_cases hq : q = 0 <;> simp [hq]

/-- Remark 4.3, tex:559. Every word of length at most four has one of these six images, all containing state 3. -/
theorem rem_4_3_images_proved (w : List (Fin 2)) (hw : w.length ≤ 4) :
    ex43.img Finset.univ w ∈
      ({Finset.univ, {0, 1, 3}, {1, 2, 3}, {0, 3}, {2, 3}, {1, 3}} : Finset (Finset (Fin 4))) ∧
      3 ∈ ex43.img Finset.univ w := by
  have h : ∀ m < 5, ∀ v ∈ words2 m,
      ex43.img Finset.univ v ∈
        ({Finset.univ, {0, 1, 3}, {1, 2, 3}, {0, 3}, {2, 3}, {1, 3}} : Finset (Finset (Fin 4))) ∧
        3 ∈ ex43.img Finset.univ v := by decide +kernel
  exact h w.length (by omega) w (mem_words2 w)

/-- Remark 4.3, tex:558. A word enlarges the three-state set exactly when it maps Q into that set. -/
theorem rem_4_3_enlarges_iff_proved (w : List (Fin 2)) :
    ({0, 1, 2} : Finset (Fin 4)).card < (ex43.pre {0, 1, 2} w).card ↔
      ex43.img Finset.univ w ⊆ {0, 1, 2} := by
  have hcard : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
  rw [hcard, Automaton.img, Finset.image_subset_iff]
  have hle := (ex43.pre {0, 1, 2} w).card_le_univ
  simp only [Fintype.card_fin] at hle
  constructor
  · intro h q _
    have he := (Finset.card_eq_iff_eq_univ _).mp
      (show (ex43.pre {0, 1, 2} w).card = Fintype.card (Fin 4) by simp; omega)
    have hq : q ∈ ex43.pre {0, 1, 2} w := he ▸ Finset.mem_univ q
    exact (Finset.mem_filter.mp hq).2
  · intro h
    have he : ex43.pre {0, 1, 2} w = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro q
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, h q (Finset.mem_univ q)⟩
    simp [he]

private theorem ex43_reset : ex43.IsReset [0, 0, 1, 0, 1, 0, 0] := by
  unfold IsReset
  decide +kernel

private theorem ex43_ext : ex43.ext {0, 1, 2} = 5 := by
  have h := minLen_eq_of (P := fun w => ({0, 1, 2} : Finset (Fin 4)).card < (ex43.pre {0, 1, 2} w).card) 5
    [0, 0, 1, 0, 1] (by decide +kernel) rfl (short_of_words2 (by decide +kernel))
  rw [Automaton.ext, h]
  rfl

private theorem ex43_rt : ex43.rt = 7 := by
  have h := minLen_eq_of (P := ex43.IsReset) 7 [0, 0, 1, 0, 1, 0, 0] ex43_reset rfl
    (short_of_words2 (by unfold IsReset; decide +kernel))
  rw [rt, h]
  rfl

theorem rem_4_3_t2_example_proved :
    (∃ W : QEWitness ex43 1, W.E = {0, 1, 2} ∧ W.s = 2 ∧ W.p = fun _ => 1 / 2) ∧
      ex43.zLoop (fun _ => 1 / 2) 3 = 1 / 2 ∧ ex43.yIn {0, 1, 2} (fun _ => 1 / 2) 3 = 1 ∧
      ex43.yIn {0, 1, 2} (fun _ => 1 / 2) 3 / (1 - ex43.zLoop (fun _ => 1 / 2) 3) = 2 ∧
      ex43.ext {0, 1, 2} = 5 ∧ ex43.img Finset.univ [0, 0, 1, 0, 1] = {1, 2} ∧
      ex43.Synchronizing ∧ ex43.rt = 7 ∧ ex43.img Finset.univ [0, 0, 1, 0, 1, 0, 0] = {0} := by
  have hz : ex43.zLoop (fun _ => 1 / 2) 3 = 1 / 2 := by
    unfold zLoop
    rw [show (Finset.univ.filter fun b => ex43.step 3 b = 3) = {0} by decide +kernel]
    simp
  have hy : ex43.yIn {0, 1, 2} (fun _ => 1 / 2) 3 = 1 := by
    unfold yIn
    rw [Fin.sum_univ_two,
      show (({0, 1, 2} : Finset (Fin 4)).filter fun q => ex43.step q 0 = 3).card = 0 by decide +kernel,
      show (({0, 1, 2} : Finset (Fin 4)).filter fun q => ex43.step q 1 = 3).card = 2 by decide +kernel]
    norm_num
  refine ⟨⟨⟨{0, 1, 2}, 2, fun _ => 1 / 2, by rfl, by decide +kernel, half_weights, by decide +kernel, ?_⟩,
    rfl, rfl, rfl⟩, hz, hy, by rw [hz, hy]; norm_num, ex43_ext, by decide +kernel, ⟨_, ex43_reset⟩, ex43_rt,
    by decide +kernel⟩
  intro r hr hrs
  apply inW_half
  revert r
  decide +kernel

theorem rem_4_3_not_extend_proved :
    ex43.IsStationary (fun _ => 1 / 2) (alphaOff 3 2) ∧ (4 : ℕ∞) < ex43.ext {0, 1, 2} := by
  refine ⟨stat_half_nat ex43 _ (fun q => if q = 3 then 2 else 1) (fun q => ?_) ⟨0, by decide⟩ (by decide +kernel),
    ?_⟩
  · by_cases hq : q = 3 <;> simp [alphaOff, hq]
  · rw [ex43_ext]
    decide

end CernyQE
