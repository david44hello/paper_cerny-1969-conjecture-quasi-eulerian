/-
CernyQE/Proofs/Basic.lean — the least-length API and the in-text claims of Section 2 (words, preimages, the matrices
M_w and M, stationary vectors, in-weights).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Automaton

open Matrix

namespace CernyQE

/-! ### The least length of a word with a property -/

section MinLen

variable {S : Type*} {P P' : List S → Prop}

theorem minLen_le_length {w : List S} (h : P w) : minLen P ≤ w.length :=
  iInf₂_le w h

theorem le_minLen_iff {k : ℕ∞} : k ≤ minLen P ↔ ∀ w, P w → k ≤ w.length := by
  simp [minLen, le_iInf_iff]

theorem minLen_eq_top_iff : minLen P = ⊤ ↔ ∀ w, ¬ P w := by
  simp [minLen, iInf_eq_top]

theorem not_of_lt_minLen {w : List S} (h : (w.length : ℕ∞) < minLen P) : ¬ P w :=
  fun hw => absurd (minLen_le_length hw) (not_le.mpr h)

theorem exists_of_minLen_ne_top (h : minLen P ≠ ⊤) : ∃ w, P w ∧ (w.length : ℕ∞) = minLen P := by
  classical
  have hex : ∃ w, P w := by
    by_contra hne
    exact h (minLen_eq_top_iff.mpr fun w hw => hne ⟨w, hw⟩)
  have hn : ∃ n, ∃ w, P w ∧ w.length = n := by
    obtain ⟨w, hw⟩ := hex
    exact ⟨_, w, hw, rfl⟩
  obtain ⟨w, hw, hwn⟩ := Nat.find_spec hn
  refine ⟨w, hw, le_antisymm ?_ (minLen_le_length hw)⟩
  rw [le_minLen_iff]
  intro w' hw'
  rw [hwn]
  exact_mod_cast Nat.find_min' hn ⟨w', hw', rfl⟩

theorem minLen_le_iff {k : ℕ} : minLen P ≤ k ↔ ∃ w, P w ∧ w.length ≤ k := by
  constructor
  · intro h
    obtain ⟨w, hw, hwl⟩ := exists_of_minLen_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top k) h)
    exact ⟨w, hw, by rw [← hwl] at h; exact_mod_cast h⟩
  · rintro ⟨w, hw, hwk⟩
    exact (minLen_le_length hw).trans (by exact_mod_cast hwk)

theorem minLen_mono (h : ∀ w, P w → P' w) : minLen P' ≤ minLen P :=
  le_minLen_iff.mpr fun _ hw => minLen_le_length (h _ hw)

/-- If the least length is `m`, some word of length exactly `m` has the property and no shorter word has it. -/
theorem minLen_eq_coe {m : ℕ} (h : minLen P = m) :
    (∃ w, P w ∧ w.length = m) ∧ ∀ w : List S, w.length < m → ¬ P w := by
  obtain ⟨w, hw, hwl⟩ := exists_of_minLen_ne_top (h ▸ ENat.natCast_ne_top m)
  refine ⟨⟨w, hw, by rw [h] at hwl; exact_mod_cast hwl⟩, fun w' hw' => not_of_lt_minLen ?_⟩
  rw [h]
  exact_mod_cast hw'

end MinLen

/-! ### Words, preimages, indicator vectors and weights -/

namespace Automaton

variable {Q S : Type*} (A : Automaton Q S)

@[simp] theorem act_nil (q : Q) : A.act q [] = q := rfl

@[simp] theorem act_cons (q : Q) (b : S) (w : List S) : A.act q (b :: w) = A.act (A.step q b) w := rfl

theorem act_append (q : Q) (u v : List S) : A.act q (u ++ v) = A.act (A.act q u) v := by
  simp [act, List.foldl_append]

@[simp] theorem act_singleton (q : Q) (b : S) : A.act q [b] = A.step q b := rfl

theorem act_concat (q : Q) (w : List S) (b : S) : A.act q (w ++ [b]) = A.step (A.act q w) b := by
  rw [act_append, act_singleton]

variable [Fintype Q] [DecidableEq Q]

@[simp] theorem mem_pre (x : Q) (K : Finset Q) (w : List S) : x ∈ A.pre K w ↔ A.act x w ∈ K := by
  simp [pre]

@[simp] theorem pre_nil (K : Finset Q) : A.pre K [] = K := by
  ext q; simp

theorem pre_append (K : Finset Q) (u v : List S) : A.pre K (u ++ v) = A.pre (A.pre K v) u := by
  ext q; simp [act_append]

@[simp] theorem pre_univ (w : List S) : A.pre Finset.univ w = Finset.univ := by
  ext q; simp

@[simp] theorem pre_empty (w : List S) : A.pre ∅ w = ∅ := by
  ext q; simp

end Automaton

section Weights

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

omit [Fintype Q] in
theorem ind_apply (K : Finset Q) (q : Q) : ind K q = if q ∈ K then 1 else 0 := rfl

theorem ind_univ : ind (Finset.univ : Finset Q) = fun _ => 1 := by
  funext q; simp [ind]

omit [Fintype Q] in
theorem ind_empty : ind (∅ : Finset Q) = 0 := by
  funext q; simp [ind]

theorem dot_ind (β : Q → ℝ) (K : Finset Q) : β ⬝ᵥ ind K = wt β K := by
  simp [dotProduct, ind, wt, Finset.sum_ite_mem]

theorem wt_univ (β : Q → ℝ) : wt β Finset.univ = β ⬝ᵥ (fun _ => 1) := by
  rw [← ind_univ, dot_ind]

omit [Fintype Q] [DecidableEq Q] in
theorem wt_empty (β : Q → ℝ) : wt β ∅ = 0 := by
  simp [wt]

end Weights

namespace Automaton

variable {Q S : Type*} [Fintype Q] [DecidableEq Q] (A : Automaton Q S)

omit [Fintype Q] in
theorem Mw_apply (w : List S) (q q' : Q) : A.Mw w q q' = if A.act q w = q' then 1 else 0 := rfl

omit [Fintype Q] in
@[simp] theorem Mw_nil : A.Mw ([] : List S) = 1 := by
  ext q q'
  by_cases h : q = q' <;> simp [Mw_apply, Matrix.one_apply, h]

theorem Mw_append (u v : List S) : A.Mw (u ++ v) = A.Mw u * A.Mw v := by
  ext q q'
  rw [Matrix.mul_apply, Mw_apply, act_append, Finset.sum_eq_single (A.act q u)]
  · simp [Mw_apply]
  · intro r _ hr
    simp [Mw_apply, Ne.symm hr]
  · simp

/-- `M_w v` at `q` is `v (q.w)`. -/
theorem Mw_mulVec (w : List S) (v : Q → ℝ) (q : Q) : (A.Mw w *ᵥ v) q = v (A.act q w) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (A.act q w)]
  · simp [Mw_apply]
  · intro r _ hr
    simp [Mw_apply, Ne.symm hr]
  · simp

theorem Mw_mulVec_one (w : List S) : A.Mw w *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext q; rw [Mw_mulVec]

theorem Mw_mulVec_ind (w : List S) (K : Finset Q) : A.Mw w *ᵥ ind K = ind (A.pre K w) := by
  funext q; rw [Mw_mulVec]; simp [ind]

theorem wt_pre_eq_dot (β : Q → ℝ) (w : List S) (K : Finset Q) :
    β ⬝ᵥ (A.Mw w *ᵥ ind K) = wt β (A.pre K w) := by
  rw [Mw_mulVec_ind, dot_ind]

/-- `αᵀ M_w` at `q'` is the `α`-weight of the states that `w` maps to `q'`. -/
theorem vecMul_Mw (α : Q → ℝ) (w : List S) (q' : Q) :
    Matrix.vecMul α (A.Mw w) q' = ∑ q, α q * (if A.act q w = q' then 1 else 0) := rfl

variable [Fintype S]

omit [Fintype Q] in
theorem M_apply (p : S → ℝ) (q q' : Q) : A.M p q q' = ∑ b, p b * (if A.step q b = q' then 1 else 0) := by
  simp only [M, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rfl

/-- `(M v)_q = ∑_b p_b v(q.b)`. -/
theorem M_mulVec (p : S → ℝ) (v : Q → ℝ) (q : Q) : (A.M p *ᵥ v) q = ∑ b, p b * v (A.step q b) := by
  simp only [Matrix.mulVec, dotProduct, M_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (A.step q b)]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

/-- `(αᵀ M)_{q'} = ∑_b p_b α(q' b⁻¹)`. -/
theorem vecMul_M (p : S → ℝ) (α : Q → ℝ) (q' : Q) :
    Matrix.vecMul α (A.M p) q' = ∑ b, p b * wt α (A.pre {q'} [b]) := by
  simp only [Matrix.vecMul, dotProduct, M_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [wt, Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun q => A.step q b = q')]
  have h1 : (Finset.univ.filter fun q => A.step q b = q') = A.pre {q'} [b] := by
    ext q; simp
  rw [h1]
  have h2 : ∑ x ∈ Finset.univ.filter (fun q => ¬ A.step q b = q'),
      α x * (p b * if A.step x b = q' then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    simp only [Finset.mem_filter] at hx
    simp [hx.2]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : A.step x b = q' := by simpa using hx
  simp [hx']
  ring_nf

end Automaton

/-! ### The rows of Section 2 that are not numbered results -/

open Automaton

theorem sec2_act_append_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (q : Q) (u v : List S), A.act q (u ++ v) = A.act (A.act q u) v :=
  A.act_append

theorem sec2_pre_append_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (K : Finset Q) (u v : List S), A.pre K (u ++ v) = A.pre (A.pre K v) u :=
  A.pre_append

theorem sec2_mem_pre_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (x : Q) (K : Finset Q) (w : List S), x ∈ A.pre K w ↔ A.act x w ∈ K :=
  A.mem_pre

/-- The word of the extension method, `w_{J-1} ⋯ w_1 w_0`. -/
theorem ext_method_word_succ {S : Type*} (w : ℕ → List S) (j : ℕ) :
    (((List.range (j + 1)).reverse).map w).flatten = w j ++ (((List.range j).reverse).map w).flatten := by
  simp [List.range_succ]

theorem sec2_ext_method_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ),
    (∀ j < J, K (j + 1) = A.pre (K j) (w j)) → K J = Finset.univ →
    let word := (((List.range J).reverse).map w).flatten
    K J = A.pre (K 0) word ∧ (∀ q, A.act q word ∈ K 0) ∧ ((∃ r, K 0 = {r}) → A.IsReset word) ∧
    (∀ (r : Q) (c : S), K 0 = A.pre {r} [c] → A.IsReset (word ++ [c])) := by
  intro K w J hstep hJ word
  have hK : ∀ j ≤ J, K j = A.pre (K 0) (((List.range j).reverse).map w).flatten := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      rw [hstep j (by omega), ih (by omega), ext_method_word_succ, A.pre_append]
  have h1 : K J = A.pre (K 0) word := hK J le_rfl
  have h2 : ∀ q, A.act q word ∈ K 0 := by
    intro q
    rw [← A.mem_pre, ← h1, hJ]
    exact Finset.mem_univ q
  refine ⟨h1, h2, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, fun q => by simpa [hr] using h2 q⟩
  · intro r c hc
    refine ⟨r, fun q => ?_⟩
    have hq := h2 q
    rw [hc, A.mem_pre] at hq
    simpa [A.act_append] using hq

theorem sec2_Mw_mul_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ u v : List S, A.Mw (u ++ v) = A.Mw u * A.Mw v :=
  A.Mw_append

theorem sec2_Mw_one_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ w : List S, A.Mw w *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 :=
  A.Mw_mulVec_one

theorem sec2_Mw_ind_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (w : List S) (K : Finset Q), A.Mw w *ᵥ ind K = ind (A.pre K w) :=
  A.Mw_mulVec_ind

theorem sec2_wt_Mw_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (β : Q → ℝ) (w : List S) (K : Finset Q), β ⬝ᵥ (A.Mw w *ᵥ ind K) = wt β (A.pre K w) :=
  A.wt_pre_eq_dot

theorem sec2_outweight_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ p : S → ℝ, IsLetterWeights p → ∀ q, ∑ q', A.M p q q' = 1 := by
  intro p hp q
  simp only [M_apply]
  rw [Finset.sum_comm]
  have hb : ∀ b, ∑ q', p b * (if A.step q b = q' then (1 : ℝ) else 0) = p b := by
    intro b
    rw [← Finset.mul_sum]
    simp
  simp only [hb]
  exact hp.2

theorem sec2_M_stochastic_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ p : S → ℝ, IsLetterWeights p → (∀ q q', 0 ≤ A.M p q q') ∧ ∀ q, ∑ q', A.M p q q' = 1 := by
  intro p hp
  refine ⟨fun q q' => ?_, sec2_outweight_core A p hp⟩
  rw [M_apply]
  exact Finset.sum_nonneg fun b _ => mul_nonneg (hp.1 b).le (by split_ifs <;> norm_num)

/-- `α ⬝ (M 𝟙_T) = ∑_b p_b α(T b⁻¹)`, for any vector `α` and weights `p`. -/
theorem dot_M_ind {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)
    (p : S → ℝ) (α : Q → ℝ) (T : Finset Q) :
    α ⬝ᵥ (A.M p *ᵥ ind T) = ∑ b, p b * wt α (A.pre T [b]) := by
  simp only [dotProduct, M_mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← dot_ind, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [ind]
  ring_nf

theorem eq_2_1_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (p : S → ℝ) (α : Q → ℝ), A.IsStationary p α → ∀ T : Finset Q,
    ∑ b, p b * wt α (A.pre T [b]) = α ⬝ᵥ (A.M p *ᵥ ind T) ∧ α ⬝ᵥ (A.M p *ᵥ ind T) = wt α T := by
  intro p α hα T
  refine ⟨(dot_M_ind A p α T).symm, ?_⟩
  rw [Matrix.dotProduct_mulVec, hα.2, dot_ind]

theorem sec2_inW_sum_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ p : S → ℝ, IsLetterWeights p → ∑ q, A.inW p q = (Fintype.card Q : ℝ) := by
  intro p hp
  simp only [inW]
  rw [Finset.sum_comm]
  have hfib : ∀ b : S, ∑ q : Q, ((A.pre {q} [b]).card : ℝ) = Fintype.card Q := by
    intro b
    have h := (Finset.card_eq_sum_card_fiberwise (f := fun q => A.step q b) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _))
    rw [Finset.card_univ] at h
    rw [h]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 2
    ext x; simp
  simp only [← Finset.mul_sum, hfib, ← Finset.sum_mul, hp.2, one_mul]

theorem sec2_one_stationary_iff_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    [Nonempty Q] → ∀ p : S → ℝ, IsLetterWeights p →
    (A.IsStationary p (fun _ => 1) ↔ ∀ q, A.inW p q = 1) := by
  intro hQ p _
  have hv : ∀ q, Matrix.vecMul (fun _ => (1 : ℝ)) (A.M p) q = A.inW p q := by
    intro q
    rw [vecMul_M, inW]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [wt]
  have hne : (fun _ : Q => (1 : ℝ)) ≠ 0 := by
    obtain ⟨q⟩ := hQ
    intro h
    exact one_ne_zero (congrFun h q)
  constructor
  · rintro ⟨-, h⟩ q
    rw [← hv q, h]
  · intro h
    refine ⟨hne, funext fun q => ?_⟩
    rw [hv q, h q]

end CernyQE
