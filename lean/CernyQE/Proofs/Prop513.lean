/-
CernyQE/Proofs/Prop513.lean — Proposition 5.13 (the classes {1/2, 2} and {3/2, 2}): the proof steps and the bounds.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary
import CernyQE.Proofs.Basic
import CernyQE.Proofs.Sec2
import CernyQE.Proofs.Rows2
import CernyQE.Proofs.Stationary
import CernyQE.Proofs.BinaryBase
import CernyQE.Proofs.Census

namespace CernyQE

open Classical Automaton Matrix

universe u v

namespace Prop513

/-! ### Least lengths and sums -/

/-- If no empty word has `P` and `c :: w` has `P` iff `w` has `P'`, then `minLen P = 1 + minLen P'`. -/
theorem minLen_cons {S : Type*} [Nonempty S] {P P' : List S → Prop} (h0 : ¬ P [])
    (hc : ∀ c w, P (c :: w) ↔ P' w) : minLen P = 1 + minLen P' := by
  apply le_antisymm
  · by_cases htop : minLen P' = ⊤
    · rw [htop]
      simp
    · obtain ⟨w, hw, hwl⟩ := exists_of_minLen_ne_top htop
      obtain ⟨c⟩ := ‹Nonempty S›
      refine (minLen_le_length ((hc c w).mpr hw)).trans ?_
      rw [← hwl, List.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
  · rw [le_minLen_iff]
    intro w hw
    cases w with
    | nil => exact absurd hw h0
    | cons c w =>
      have h := minLen_le_length ((hc c w).mp hw)
      rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
      gcongr

/-- Summing over the pairs of consecutive values `2N + 1`, `2N + 2`. -/
theorem sum_pairs (f : ℕ → ℕ) (a k : ℕ) (hak : a ≤ k) :
    ∑ M ∈ Finset.Ico (2 * a + 1) (2 * k + 1), f M =
      ∑ N ∈ Finset.Ico a k, (f (2 * N + 1) + f (2 * N + 1 + 1)) := by
  induction k, hak using Nat.le_induction with
  | base => simp
  | succ k hak ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring,
      Finset.sum_Ico_succ_top (by omega : 2 * a + 1 ≤ 2 * k + 1 + 1),
      Finset.sum_Ico_succ_top (by omega : 2 * a + 1 ≤ 2 * k + 1), ih, Finset.sum_Ico_succ_top hak]
    ring

/-! ### The cost bounds of the values (doubled values `M = 2 α(K)`) -/

/-- The bound for an integer value `N` (both classes). -/
def ce (n N : ℕ) : ℕ := if N + 3 ≤ n then n - N else if N + 2 ≤ n then 2 else if N ≤ n then 1 else 0

/-- The class `{1/2, 2}`: the bound for the doubled value `M`. -/
def cHalf (n M : ℕ) : ℕ := if M % 2 = 0 then ce n (M / 2) else if M / 2 ≤ 2 then 2 else M / 2

/-- The class `{3/2, 2}`: the bound for a value `N + 1/2`. -/
def coHi (N : ℕ) : ℕ := if N ≤ 2 then 1 else if N ≤ 3 then 2 else N - 1

/-- The class `{3/2, 2}`: the bound for the doubled value `M`. -/
def cHi (n M : ℕ) : ℕ := if M % 2 = 0 then ce n (M / 2) else coHi (M / 2)

/-- The count in the class `{1/2, 2}` (tex:890-898). -/
theorem sum_half (n : ℕ) (hn : 4 ≤ n) :
    1 + ∑ M ∈ Finset.Ico (4 + 1) (2 * n + 1), cHalf n M ≤ n ^ 2 + 4 - 3 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show 4 + 1 = 2 * 2 + 1 from rfl, sum_pairs _ 2 (m + 4) (by omega),
    Finset.sum_Ico_succ_top (by omega : 2 ≤ m + 3)]
  have hpt : ∀ N ∈ Finset.Ico 2 (m + 3),
      cHalf (m + 4) (2 * N + 1) + cHalf (m + 4) (2 * N + 1 + 1) ≤ m + 3 := by
    intro N hN
    rw [Finset.mem_Ico] at hN
    unfold cHalf ce
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hsum
  have hlast : cHalf (m + 4) (2 * (m + 3) + 1) + cHalf (m + 4) (2 * (m + 3) + 1 + 1) ≤ m + 4 := by
    unfold cHalf ce
    split_ifs <;> omega
  have h1 : (m + 3 - 2) * (m + 3) = m * m + 4 * m + 3 := by
    rw [show m + 3 - 2 = m + 1 by omega]
    ring
  have h2 : (m + 4) ^ 2 = m * m + 8 * m + 16 := by ring
  omega

/-- The count in the class `{3/2, 2}` (tex:900-909). -/
theorem sum_hi (n : ℕ) (hn : 4 ≤ n) :
    1 + ∑ M ∈ Finset.Ico (4 + 1) (2 * (n + 1) + 1), cHi n M ≤ n ^ 2 + 5 - 3 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show 4 + 1 = 2 * 2 + 1 from rfl, sum_pairs _ 2 (m + 4 + 1) (by omega),
    Finset.sum_Ico_succ_top (by omega : 2 ≤ m + 4), Finset.sum_Ico_succ_top (by omega : 2 ≤ m + 3)]
  have hpt : ∀ N ∈ Finset.Ico 2 (m + 3),
      cHi (m + 4) (2 * N + 1) + cHi (m + 4) (2 * N + 1 + 1) ≤ m + 2 := by
    intro N hN
    rw [Finset.mem_Ico] at hN
    unfold cHi coHi ce
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hsum
  have hl1 : cHi (m + 4) (2 * (m + 3) + 1) + cHi (m + 4) (2 * (m + 3) + 1 + 1) ≤ m + 3 := by
    unfold cHi coHi ce
    split_ifs <;> omega
  have hl2 : cHi (m + 4) (2 * (m + 4) + 1) + cHi (m + 4) (2 * (m + 4) + 1 + 1) ≤ m + 3 := by
    unfold cHi coHi ce
    split_ifs <;> omega
  have h1 : (m + 3 - 2) * (m + 2) = m * m + 3 * m + 2 := by
    rw [show m + 3 - 2 = m + 1 by omega]
    ring
  have h2 : (m + 4) ^ 2 = m * m + 8 * m + 16 := by ring
  omega

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-! ### Weights of sets and the extension process -/

omit [Fintype Q] [DecidableEq Q] in
theorem wt_pos {α : Q → ℝ} (hpos : ∀ q, 0 < α q) {K : Finset Q} (hK : K.Nonempty) : 0 < wt α K :=
  Finset.sum_pos (fun q _ => hpos q) hK

omit [Fintype Q] [DecidableEq Q] in
theorem nonempty_of_wt_pos {α : Q → ℝ} {K : Finset Q} (h : 0 < wt α K) : K.Nonempty := by
  rcases K.eq_empty_or_nonempty with hK | hK
  · rw [hK, wt_empty] at h
    exact absurd h (lt_irrefl 0)
  · exact hK

theorem wt_lt_univ {α : Q → ℝ} (hpos : ∀ q, 0 < α q) {K : Finset Q} (hK : K ≠ Finset.univ) :
    wt α K < wt α Finset.univ := by
  have hne : (Finset.univ \ K).Nonempty := by
    obtain ⟨q, hq⟩ : ∃ q, q ∉ K := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hK (Finset.eq_univ_of_forall h)
    exact ⟨q, by simp [hq]⟩
  have h := Finset.sum_sdiff (Finset.subset_univ K) (f := α)
  have hp : 0 < ∑ q ∈ Finset.univ \ K, α q := Finset.sum_pos (fun q _ => hpos q) hne
  unfold wt
  linarith

omit [Fintype S] in
theorem rt_le_of_pre_singleton {r : Q} {w : List S} (h : A.pre {r} w = Finset.univ) :
    A.rt ≤ (w.length : ℕ∞) := by
  have hres : A.IsReset w := ⟨r, fun q => by
    have hq : q ∈ A.pre {r} w := h ▸ Finset.mem_univ q
    simpa using hq⟩
  exact minLen_le_length hres

omit [Fintype S] in
/-- Strong induction along a strictly rising value, with a budget `B` that pays for every step. -/
theorem reach_univ (val : Finset Q → ℝ) (C : Finset Q → Prop) (B : Finset Q → ℕ)
    (hstep : ∀ K, C K → K ≠ Finset.univ →
      ∃ w : List S, val K < val (A.pre K w) ∧ C (A.pre K w) ∧ w.length + B (A.pre K w) ≤ B K) :
    ∀ K, C K → ∃ w : List S, A.pre K w = Finset.univ ∧ w.length ≤ B K := by
  suffices H : ∀ N : ℕ, ∀ K, (Finset.univ.filter (fun T : Finset Q => val K < val T)).card = N → C K →
      ∃ w : List S, A.pre K w = Finset.univ ∧ w.length ≤ B K from
    fun K hK => H _ K rfl hK
  intro N
  induction' N using Nat.strong_induction_on with N ih
  intro K hN hK
  by_cases hKu : K = Finset.univ
  · exact ⟨[], by simp [hKu], by simp⟩
  obtain ⟨w, hlt, hC, hB⟩ := hstep K hK hKu
  have hsub : Finset.univ.filter (fun T : Finset Q => val (A.pre K w) < val T) ⊂
      Finset.univ.filter (fun T : Finset Q => val K < val T) := by
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨A.pre K w, ?_, ?_⟩
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact hlt.trans hT
    · simp [hlt]
    · simp
  have hlt' := Finset.card_lt_card hsub
  rw [hN] at hlt'
  obtain ⟨u', hu', hul⟩ := ih _ hlt' (A.pre K w) rfl hC
  refine ⟨u' ++ w, ?_, ?_⟩
  · rw [A.pre_append, hu']
  · rw [List.length_append]
    omega

/-- The count along an extension process from a singleton `{r}` of cost one: with natural values `V K = 2 α(K)` and a
bound `c (V K)` for the cost of every proper set above `V {r}`, `rt ≤ 1 + ∑ c` over the values above `V {r}`. -/
theorem rt_count (hA : A.Synchronizing) (p : S → ℝ) (hp : IsLetterWeights p) (α : Q → ℝ)
    (hst : A.IsStationary p α) (hpos : ∀ q, 0 < α q) (V : Finset Q → ℕ) (hV : ∀ K, (V K : ℝ) = 2 * wt α K)
    (c : ℕ → ℕ) (M₀ : ℕ)
    (hc : ∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → M₀ < V K → A.cost α K ≤ (c (V K) : ℕ∞))
    (r : Q) (hr : V {r} = M₀) (hr0 : ({r} : Finset Q) ≠ Finset.univ) (hr1 : A.cost α {r} = 1) :
    A.rt ≤ ((1 + ∑ M ∈ Finset.Ico (M₀ + 1) (V Finset.univ), c M : ℕ) : ℕ∞) := by
  have hVlt : ∀ K K' : Finset Q, wt α K < wt α K' → V K < V K' := by
    intro K K' h
    have h' : (V K : ℝ) < V K' := by
      rw [hV, hV]
      linarith
    exact_mod_cast h'
  -- the first step, from `{r}`
  obtain ⟨-, hw⟩ := sec2_cost_bounds_core A hA α hpos {r} (Finset.singleton_nonempty r) hr0
  obtain ⟨w₀, hw₀l, hw₀⟩ := hw p hp hst
  have hw₀1 : w₀.length = 1 := by
    rw [hr1] at hw₀l
    exact_mod_cast hw₀l
  have hlt₁ : wt α {r} < wt α (A.pre {r} w₀) := hw₀
  have hK₁ne : (A.pre {r} w₀).Nonempty :=
    nonempty_of_wt_pos ((wt_pos hpos (Finset.singleton_nonempty r)).trans hlt₁)
  have hM₁ : M₀ < V (A.pre {r} w₀) := by
    rw [← hr]
    exact hVlt _ _ hlt₁
  -- the budget: the sum of the bounds of the values from `V K` on
  have hstep : ∀ K : Finset Q, (K.Nonempty ∧ M₀ < V K) → K ≠ Finset.univ → ∃ w : List S,
      wt α K < wt α (A.pre K w) ∧ ((A.pre K w).Nonempty ∧ M₀ < V (A.pre K w)) ∧
        w.length + ∑ M ∈ Finset.Ico (V (A.pre K w)) (V Finset.univ), c M ≤
          ∑ M ∈ Finset.Ico (V K) (V Finset.univ), c M := by
    rintro K ⟨hKne, hKM⟩ hKu
    obtain ⟨-, hwK⟩ := sec2_cost_bounds_core A hA α hpos K hKne hKu
    obtain ⟨w, hwl, hwr⟩ := hwK p hp hst
    have hlt : wt α K < wt α (A.pre K w) := hwr
    have hcK := hc K hKne hKu hKM
    rw [← hwl] at hcK
    have hwc : w.length ≤ c (V K) := by exact_mod_cast hcK
    have hVK := hVlt _ _ hlt
    have hVu : V K < V Finset.univ := hVlt _ _ (wt_lt_univ hpos hKu)
    refine ⟨w, hlt, ⟨nonempty_of_wt_pos ((wt_pos hpos hKne).trans hlt), by omega⟩, ?_⟩
    have h1 := Finset.sum_eq_sum_Ico_succ_bot hVu c
    have h2 : ∑ M ∈ Finset.Ico (V (A.pre K w)) (V Finset.univ), c M ≤
        ∑ M ∈ Finset.Ico (V K + 1) (V Finset.univ), c M :=
      Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left (Nat.succ_le_of_lt hVK))
    omega
  obtain ⟨u₁, hu₁, hu₁l⟩ := reach_univ A (wt α) (fun K => K.Nonempty ∧ M₀ < V K)
    (fun K => ∑ M ∈ Finset.Ico (V K) (V Finset.univ), c M) hstep (A.pre {r} w₀) ⟨hK₁ne, hM₁⟩
  have hB : ∑ M ∈ Finset.Ico (V (A.pre {r} w₀)) (V Finset.univ), c M ≤
      ∑ M ∈ Finset.Ico (M₀ + 1) (V Finset.univ), c M :=
    Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left (Nat.succ_le_of_lt hM₁))
  have hres : A.pre {r} (u₁ ++ w₀) = Finset.univ := by
    rw [A.pre_append]
    exact hu₁
  refine (rt_le_of_pre_singleton A hres).trans (Nat.cast_le.mpr ?_)
  rw [List.length_append, hw₀1]
  have hu₁l' : u₁.length ≤ ∑ M ∈ Finset.Ico (V (A.pre {r} w₀)) (V Finset.univ), c M := hu₁l
  omega

/-! ### Sets and memberships -/

omit [Fintype Q] in
theorem ein_mem {x : Q} {K : Finset Q} (h : x ∈ K) : ein x K = 1 := by
  simp [ein, h]

omit [Fintype Q] in
theorem ein_not_mem {x : Q} {K : Finset Q} (h : x ∉ K) : ein x K = 0 := by
  simp [ein, h]

omit [Fintype Q] in
theorem ein_int (x : Q) (K : Finset Q) : ∃ z : ℤ, ein x K = z := by
  by_cases h : x ∈ K
  · exact ⟨1, by rw [ein_mem h]; norm_num⟩
  · exact ⟨0, by rw [ein_not_mem h]; norm_num⟩

theorem card_add_le (K T : Finset Q) (h : ∀ x ∈ T, x ∉ K) : K.card + T.card ≤ Fintype.card Q := by
  have hd : Disjoint K T := Finset.disjoint_left.mpr fun x hxK hxT => h x hxT hxK
  rw [← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_univ _

omit [Fintype Q] in
theorem card_three {x y z : Q} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : ({x, y, z} : Finset Q).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]

omit [Fintype S] in
theorem exists_pattern {x₁ x₂ s : Q} (h12 : x₁ ≠ x₂) (h1s : x₁ ≠ s) (h2s : x₂ ≠ s)
    (P : Bool × Bool × Bool) : ∃ K : Finset Q, pattern x₁ x₂ s K = P := by
  obtain ⟨b₁, b₂, b₃⟩ := P
  refine ⟨Finset.univ.filter (fun q => (q = x₁ ∧ b₁ = true) ∨ (q = x₂ ∧ b₂ = true) ∨ (q = s ∧ b₃ = true)), ?_⟩
  simp [pattern, h12, h12.symm, h1s, h2s, h1s.symm, h2s.symm]

/-! ### The witness -/

theorem not_mem_E {d : ℕ} (W : QEWitness A d) {u v : Q} (hX : W.X = {u, v}) {x : Q} (hx : x = u ∨ x = v) :
    x ∉ W.E := by
  have h : x ∈ W.X := by
    rw [hX]
    rcases hx with rfl | rfl <;> simp
  exact (Finset.mem_sdiff.mp h).2

theorem ne_s {d : ℕ} (W : QEWitness A d) {u v : Q} (hX : W.X = {u, v}) : u ≠ W.s ∧ v ≠ W.s := by
  refine ⟨fun h => not_mem_E A W hX (Or.inl rfl) (h ▸ W.s_mem), fun h => not_mem_E A W hX (Or.inr rfl) (h ▸ W.s_mem)⟩

/-- Every edge from `X = {u, v}` ends in `{s, u, v}`. -/
theorem step_mem {d : ℕ} (W : QEWitness A d) {u v : Q} (hX : W.X = {u, v}) {x : Q} (hx : x = u ∨ x = v)
    (c : S) : A.step x c = W.s ∨ A.step x c = u ∨ A.step x c = v := by
  rcases W.edge_X x (not_mem_E A W hX hx) c with h | h
  · right
    have h' : A.step x c ∈ W.X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩
    rw [hX] at h'
    simpa using h'
  · exact Or.inl h

omit [Fintype Q] in
theorem stateCode_one {u v q : Q} (h : stateCode u v q = 1) : q = v := by
  unfold stateCode at h
  split_ifs at h with h1 h2
  · exact absurd h (by decide)
  · exact h2
  · exact absurd h (by decide)

omit [Fintype Q] in
theorem stateCode_two {u v q : Q} (h : stateCode u v q = 2) : q ≠ u ∧ q ≠ v := by
  unfold stateCode at h
  split_ifs at h with h1 h2
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact ⟨h1, h2⟩

/-- A valid configuration with `t = (k, 2)`, `k < 2`, in a class with one configuration `cf₀` up to renaming, is `cf₀`
or `cf₀` with the letters renamed. -/
theorem config_of_class (cf cf₀ : Config) (k : ℚ) (hk : k < 2) (h0 : cf.t 0 = k) (h1 : cf.t 1 = 2)
    (hch : cf ∈ choices) (hval : cf.Valid)
    (hcl : (choices.filter (fun c => c.Valid ∧ c.cls = (k, 2))).image Config.renamings = {cf₀.renamings})
    (ht₀ : cf₀.t 1 = 2) : cf = cf₀ ∨ cf = cf₀.swapL := by
  have hcls : cf.cls = (k, 2) := by
    rw [Config.cls, h0, h1, min_eq_left hk.le, max_eq_right hk.le]
  have hmem : cf.renamings ∈ (choices.filter (fun c => c.Valid ∧ c.cls = (k, 2))).image Config.renamings :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hch, hval, hcls⟩)
  rw [hcl, Finset.mem_singleton] at hmem
  have hself : cf ∈ cf.renamings := by simp [Config.renamings]
  rw [hmem] at hself
  simp only [Config.renamings, Finset.mem_insert, Finset.mem_singleton] at hself
  rcases hself with e | e | e | e
  · exact Or.inl e
  · rw [e, Census.t_swapX_zero, ht₀] at h0
    exact absurd h0 hk.ne'
  · exact Or.inr e
  · rw [e, Census.t_swapL, Census.t_swapX_zero, ht₀] at h0
    exact absurd h0 hk.ne'

/-- The configuration (tex:871-875): both letters map `u` to `v`, and some letter maps `v` to `s`. -/
theorem config_facts (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2 ∨ A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) :
    (∀ c, A.step u c = v) ∧ ∃ c, A.step v c = W.s := by
  obtain ⟨-, -, -, -, ht⟩ := lem_5_7_b_proved A a b hab hS W u v hX huv
  have ht0 : A.alphaStat W.E (fun _ => 1 / 2) u = ((A.configOf a b W.E u v).t 0 : ℝ) := ht hsc 0
  have ht1 : A.alphaStat W.E (fun _ => 1 / 2) v = ((A.configOf a b W.E u v).t 1 : ℝ) := ht hsc 1
  obtain ⟨hch, hval⟩ := sec54_config_valid_proved A a b hab hS hsc W u v hX huv
  obtain ⟨hc1, hc2, ht1', ht2'⟩ := prop_5_13_config_proved
  have h1q : (A.configOf a b W.E u v).t 1 = 2 := by
    have h := ht1.symm.trans hv
    exact_mod_cast h
  have hshape : (A.configOf a b W.E u v).x1a = 1 ∧ (A.configOf a b W.E u v).x1b = 1 ∧
      ((A.configOf a b W.E u v).x2a = 2 ∨ (A.configOf a b W.E u v).x2b = 2) := by
    rcases hu with h | h
    · have h0q : (A.configOf a b W.E u v).t 0 = 1/2 := by
        have h' : (((A.configOf a b W.E u v).t 0 : ℚ) : ℝ) = ((1/2 : ℚ) : ℝ) := by
          rw [← ht0, h]
          norm_num
        exact Rat.cast_injective h'
      have h12 : (⟨1, 1, 2, 1, 1, 1⟩ : Config).t 1 = 2 := by rw [ht1']; rfl
      rcases config_of_class _ _ _ (by norm_num) h0q h1q hch hval hc1 h12 with e | e <;> rw [e] <;> decide
    · have h0q : (A.configOf a b W.E u v).t 0 = 3/2 := by
        have h' : (((A.configOf a b W.E u v).t 0 : ℚ) : ℝ) = ((3/2 : ℚ) : ℝ) := by
          rw [← ht0, h]
          norm_num
        exact Rat.cast_injective h'
      have h12 : (⟨1, 1, 2, 0, 1, 1⟩ : Config).t 1 = 2 := by rw [ht2']; rfl
      rcases config_of_class _ _ _ (by norm_num) h0q h1q hch hval hc2 h12 with e | e <;> rw [e] <;> decide
  obtain ⟨ha, hb, hvs⟩ := hshape
  have hua : A.step u a = v := stateCode_one ha
  have hub : A.step u b = v := stateCode_one hb
  refine ⟨fun c => by rcases hS c with rfl | rfl <;> assumption, ?_⟩
  have hto_s : ∀ c, stateCode u v (A.step v c) = 2 → A.step v c = W.s := by
    intro c hc
    obtain ⟨h1, h2⟩ := stateCode_two hc
    rcases step_mem A W hX (Or.inr rfl) c with h | h | h
    · exact h
    · exact absurd h h1
    · exact absurd h h2
  rcases hvs with h | h
  · exact ⟨a, hto_s a h⟩
  · exact ⟨b, hto_s b h⟩

/-! ### Steps (i)-(iii) -/

/-- `t_u - 1 = ∓ 1/2` is not an integer. -/
theorem g_not_int (x : ℝ) (h : x = 1/2 ∨ x = 3/2) (z : ℤ) : x - 1 ≠ z := by
  intro hz
  rcases h with rfl | rfl
  · have h2 : ((2 * z : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * z = -1 := by exact_mod_cast h2
    omega
  · have h2 : ((2 * z : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * z = 1 := by exact_mod_cast h2
    omega

/-- Step (i): `m(K) ≤ esc_u(K)`. -/
theorem step_i (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2 ∨ A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) (K : Finset Q) :
    A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ A.esc u K := by
  refine minLen_mono (fun w hw => ?_)
  rw [A.movesAcross_iff] at hw
  intro heq
  rw [sec54_alpha_formula_proved A W u v hX huv, sec54_alpha_formula_proved A W u v hX huv, hv] at heq
  obtain ⟨z, hz⟩ := ein_int v (A.pre K w)
  obtain ⟨z', hz'⟩ := ein_int v K
  rw [hz, hz'] at heq
  by_cases hU : u ∈ K
  · have hU' : u ∉ A.pre K w := by
      rw [A.mem_pre]
      tauto
    rw [ein_mem hU, ein_not_mem hU'] at heq
    exact g_not_int _ hu (((A.pre K w).card : ℤ) - K.card + z - z') (by push_cast; linarith)
  · have hU' : u ∈ A.pre K w := by
      rw [A.mem_pre]
      tauto
    rw [ein_not_mem hU, ein_mem hU'] at heq
    exact g_not_int _ hu ((K.card : ℤ) - (A.pre K w).card + z' - z) (by push_cast; linarith)

/-- Step (ii): a pattern is good iff `e_u ≠ e_v`. -/
theorem step_ii (W : QEWitness A 2) (u v : Q) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2 ∨ A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) (hstep : ∀ c, A.step u c = v) (hus : u ≠ W.s)
    (hvs : v ≠ W.s) (a : S) (P : Bool × Bool × Bool) :
    Good A u v W.s (A.alphaStat W.E (fun _ => 1 / 2) u - 1) (A.alphaStat W.E (fun _ => 1 / 2) v - 1) P ↔
      P.1 ≠ P.2.1 := by
  have e1 : ∀ (c : S) (K : Finset Q), ein u (A.pre K [c]) = ein v K := by
    intro c K
    simp only [ein, A.mem_pre, act_singleton, hstep c]
  rw [hv]
  constructor
  · rintro ⟨c, K, hK, hnot⟩ hP
    apply hnot
    have hUV : (u ∈ K ↔ v ∈ K) := by
      rw [← hK] at hP
      simpa [pattern] using hP
    have e2 : ein u K = ein v K := by
      by_cases h : u ∈ K
      · rw [ein_mem h, ein_mem (hUV.mp h)]
      · rw [ein_not_mem h, ein_not_mem (fun h' => h (hUV.mpr h'))]
    obtain ⟨z, hz⟩ := ein_int v (A.pre K [c])
    obtain ⟨z', hz'⟩ := ein_int v K
    exact ⟨z - z', by rw [e1, e2, hz, hz']; push_cast; ring⟩
  · intro hP
    obtain ⟨K, hK⟩ := exists_pattern huv hus hvs P
    refine ⟨a, K, hK, ?_⟩
    rintro ⟨z, hz⟩
    have hUV : ¬ (u ∈ K ↔ v ∈ K) := by
      rw [← hK] at hP
      simpa [pattern] using hP
    obtain ⟨z', hz'⟩ := ein_int v (A.pre K [a])
    rw [e1, hz'] at hz
    by_cases hU : u ∈ K
    · have hV : v ∉ K := fun h => hUV ⟨fun _ => h, fun _ => hU⟩
      rw [ein_mem hU, ein_not_mem hV] at hz
      exact g_not_int _ hu (z' - z) (by push_cast; linarith)
    · have hV : v ∈ K := by
        by_contra h
        exact hUV ⟨fun h' => absurd h' hU, fun h' => absurd h' h⟩
      rw [ein_not_mem hU, ein_mem hV] at hz
      exact g_not_int _ hu (z - z' + 1) (by push_cast; linarith)

omit [Fintype Q] [Fintype S] in
/-- Step (iii), first part: `esc_u(K) = 1 + esc_v(K)` when `e_u(K) = e_v(K)`. -/
theorem esc_u_eq (u v : Q) (a : S) (hstep : ∀ c, A.step u c = v) (K : Finset Q) (h : u ∈ K ↔ v ∈ K) :
    A.esc u K = 1 + A.esc v K := by
  have : Nonempty S := ⟨a⟩
  unfold Automaton.esc
  apply minLen_cons
  · intro h0
    rw [A.movesAcross_iff] at h0
    exact h0 (by simp)
  · intro c w
    rw [A.movesAcross_iff, A.movesAcross_iff, act_cons, hstep c]
    tauto

omit [Fintype Q] [Fintype S] in
/-- Step (iii), second part: `esc_v(K) = 1` when `e_s(K) ≠ e_v(K)`. -/
theorem esc_v_one (v s : Q) (cs : S) (hcs : A.step v cs = s) (K : Finset Q) (h : s ∈ K ↔ v ∉ K) :
    A.esc v K = 1 := by
  apply le_antisymm
  · have hm : A.MovesAcross v K [cs] := by
      rw [A.movesAcross_iff, act_singleton, hcs]
      tauto
    exact (minLen_le_length hm).trans (by simp)
  · refine le_minLen_iff.mpr (fun w hw => ?_)
    cases w with
    | nil =>
      rw [A.movesAcross_iff] at hw
      exact absurd (by simp) hw
    | cons c w => exact_mod_cast (show 1 ≤ (c :: w).length by simp)

/-- For an aligned set, the states `u`, `v` stay on the side of `s` for `|w| ≤ esc_s(K)` (the joint orbit). -/
theorem stay (W : QEWitness A 2) {u v : Q} (hX : W.X = {u, v}) (K : Finset Q)
    (hu : u ∈ K ↔ W.s ∈ K) (hv : v ∈ K ↔ W.s ∈ K) :
    ∀ (w : List S) (x : Q), (x = u ∨ x = v) → (w.length : ℕ∞) ≤ A.esc W.s K →
      (A.act x w ∈ K ↔ W.s ∈ K) := by
  intro w
  induction w with
  | nil =>
    intro x hx _
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  | cons c w ih =>
    intro x hx hlen
    rw [act_cons]
    have hlt : (w.length : ℕ∞) < ((c :: w).length : ℕ∞) := by
      exact_mod_cast (show w.length < (c :: w).length by simp)
    rcases step_mem A W hX hx c with h | h | h
    · rw [h]
      have hnm := not_of_lt_minLen (P := A.MovesAcross W.s K) (lt_of_lt_of_le hlt hlen)
      rw [A.movesAcross_iff, not_not] at hnm
      exact hnm
    · exact ih _ (Or.inl h) (hlt.le.trans hlen)
    · exact ih _ (Or.inr h) (hlt.le.trans hlen)

/-- Step (iii), third part: `esc_v(K) = 1 + esc_s(K)` for an aligned set. -/
theorem esc_v_aligned (hsc : A.StronglyConnected) (W : QEWitness A 2) {u v : Q} (hX : W.X = {u, v})
    (cs : S) (hcs : A.step v cs = W.s) (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ)
    (hu : u ∈ K ↔ W.s ∈ K) (hv : v ∈ K ↔ W.s ∈ K) : A.esc v K = 1 + A.esc W.s K := by
  have hfin : A.esc W.s K ≠ ⊤ := lem_2_3_fin_core A hsc W.s K hne hprop
  obtain ⟨f, hf⟩ := ENat.ne_top_iff_exists.mp hfin
  have hstay := stay A W hX K hu hv
  apply le_antisymm
  · obtain ⟨ws, hws, hwsl⟩ := exists_of_minLen_ne_top (P := A.MovesAcross W.s K) hfin
    have hmv : A.MovesAcross v K (cs :: ws) := by
      rw [A.movesAcross_iff] at hws ⊢
      rw [act_cons, hcs]
      tauto
    have hwsf : ws.length = f := by
      have h' : (ws.length : ℕ∞) = f := hwsl.trans hf.symm
      exact_mod_cast h'
    calc A.esc v K ≤ ((cs :: ws).length : ℕ∞) := minLen_le_length hmv
      _ = 1 + A.esc W.s K := by
        rw [← hf, List.length_cons, hwsf]
        push_cast
        ring
  · rw [← hf]
    refine le_minLen_iff.mpr (fun w hw => ?_)
    have h1f : 1 + f ≤ w.length := by
      by_contra hlt
      have hle : (w.length : ℕ∞) ≤ A.esc W.s K := by
        rw [← hf]
        exact_mod_cast (by omega : w.length ≤ f)
      have h1 := hstay w v (Or.inr rfl) hle
      rw [A.movesAcross_iff] at hw
      exact hw (h1.trans hv.symm)
    exact_mod_cast h1f

end General

end Prop513

open Prop513

section Binary

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- Proposition 5.13, proof steps (i)-(iii), tex:878-886 and tab_costs_float.tex:12-20, with Lean u = printed x₂ and v = printed x₁, `t_u ∈ {1/2, 3/2}`,
`t_v = 2`. -/
theorem prop_5_13_steps_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (_hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2 ∨ A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) :
    (∀ K : Finset Q, A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ A.esc u K) ∧
      (∀ P : Bool × Bool × Bool, Good A u v W.s (A.alphaStat W.E (fun _ => 1 / 2) u - 1)
          (A.alphaStat W.E (fun _ => 1 / 2) v - 1) P ↔ P.1 ≠ P.2.1) ∧
      ∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → (u ∈ K ↔ v ∈ K) →
        A.esc u K = 1 + A.esc v K ∧
        ((W.s ∈ K ↔ v ∉ K) → A.esc v K = 1 ∧ A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ 2) ∧
        (Aligned (pattern u v W.s K) → A.esc v K = 1 + A.esc W.s K ∧
          A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ 2 + A.esc W.s K ∧
          (pattern u v W.s K = (true, true, true) → 2 + A.esc W.s K ≤ K.card) ∧
          (pattern u v W.s K = (false, false, false) → 2 + A.esc W.s K ≤
            ((Fintype.card Q - K.card : ℕ) : ℕ∞))) := by
  obtain ⟨hstep, cs, hcs⟩ := config_facts A a b hab hS hsc W u v hX huv hu hv
  obtain ⟨hus, hvs⟩ := ne_s A W hX
  have hi := step_i A W u v hX huv hu hv
  refine ⟨hi, step_ii A W u v huv hu hv hstep hus hvs a, fun K hne hprop huvK => ?_⟩
  have ha := esc_u_eq A u v a hstep K huvK
  refine ⟨ha, fun hs => ?_, fun hal => ?_⟩
  · have h1 := esc_v_one A v W.s cs hcs K hs
    refine ⟨h1, (hi K).trans (le_of_eq ?_)⟩
    rw [ha, h1]
    rfl
  · have hmem : (u ∈ K ↔ W.s ∈ K) ∧ (v ∈ K ↔ W.s ∈ K) := by
      rcases hal with hP | hP <;> simp only [pattern, Prod.mk.injEq, decide_eq_true_eq,
        decide_eq_false_iff_not] at hP <;> obtain ⟨h1, h2, h3⟩ := hP <;> tauto
    have hev := esc_v_aligned A hsc W hX cs hcs K hne hprop hmem.1 hmem.2
    have hfin : A.esc W.s K ≠ ⊤ := lem_2_3_fin_core A hsc W.s K hne hprop
    obtain ⟨f, hf⟩ := ENat.ne_top_iff_exists.mp hfin
    refine ⟨hev, (hi K).trans (le_of_eq ?_), fun hP => ?_, fun hP => ?_⟩
    · rw [ha, hev, ← add_assoc, one_add_one_eq_two]
    · obtain ⟨hesc, -, -⟩ := lem_5_10_a_proved A hsc W u v hX huv K hne hprop hP
      simp only [pattern, Prod.mk.injEq, decide_eq_true_eq] at hP
      have hk : ({u, v} : Finset Q).card ≤ K.card :=
        Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hP.1
          · exact hP.2.1)
      rw [Finset.card_pair huv] at hk
      rw [← hf] at hesc ⊢
      have hf' : f ≤ K.card - 2 := by exact_mod_cast hesc
      exact_mod_cast (show 2 + f ≤ K.card by omega)
    · obtain ⟨hesc, -⟩ := lem_5_10_b_proved A hsc W u v hX huv K hne hprop hP
      simp only [pattern, Prod.mk.injEq, decide_eq_false_iff_not] at hP
      have hk := card_add_le K {u, v} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hP.1
        · exact hP.2.1)
      rw [Finset.card_pair huv] at hk
      rw [← hf] at hesc ⊢
      have hf' : f ≤ Fintype.card Q - K.card - 2 := by exact_mod_cast hesc
      exact_mod_cast (show 2 + f ≤ Fintype.card Q - K.card by omega)

namespace Prop513

/-! ### The costs of the sets by pattern -/

/-- The costs that the count uses (steps (ii) and (iii), and Lemma 5.10). -/
theorem cost_cases (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2 ∨ A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) (K : Finset Q) (hne : K.Nonempty)
    (hprop : K ≠ Finset.univ) :
    (¬ (u ∈ K ↔ v ∈ K) → A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K = 1) ∧
      ((u ∈ K ↔ v ∈ K) → (W.s ∈ K ↔ v ∉ K) → A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ 2) ∧
      (u ∈ K → v ∈ K → W.s ∈ K → A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ K.card) ∧
      (u ∉ K → v ∉ K → W.s ∉ K →
        A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ ((Fintype.card Q - K.card : ℕ) : ℕ∞)) := by
  obtain ⟨-, hgood, hiii⟩ := prop_5_13_steps_proved A a b hab hS hsc hn W u v hX huv hu hv
  refine ⟨fun h => ?_, fun h hs => ((hiii K hne hprop h).2.1 hs).2, fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_⟩
  · have hG := (hgood (pattern u v W.s K)).mpr (by simpa [pattern] using h)
    exact (sec54_good_cost1_proved A W u v hX huv _).2 hG K rfl
  · have hP : pattern u v W.s K = (true, true, true) := by simp [pattern, h1, h2, h3]
    obtain ⟨-, hc, h111, -⟩ := (hiii K hne hprop (iff_of_true h1 h2)).2.2 (Or.inl hP)
    exact hc.trans (h111 hP)
  · have hP : pattern u v W.s K = (false, false, false) := by simp [pattern, h1, h2, h3]
    obtain ⟨-, hc, -, h000⟩ := (hiii K hne hprop (iff_of_false h1 h2)).2.2 (Or.inr hP)
    exact hc.trans (h000 hP)

/-- Sizes of sets that contain or miss `u`, `v`, `s`. -/
theorem card_facts (W : QEWitness A 2) {u v : Q} (hX : W.X = {u, v}) (huv : u ≠ v) (K : Finset Q) :
    (u ∈ K → 1 ≤ K.card) ∧ (u ∈ K → v ∈ K → 2 ≤ K.card) ∧ (u ∉ K → K.card + 1 ≤ Fintype.card Q) ∧
      (u ∉ K → v ∉ K → K.card + 2 ≤ Fintype.card Q) ∧
      (u ∉ K → v ∉ K → W.s ∉ K → K.card + 3 ≤ Fintype.card Q) := by
  obtain ⟨hus, hvs⟩ := ne_s A W hX
  refine ⟨fun h => Finset.card_pos.mpr ⟨u, h⟩, fun h h' => ?_, fun h => ?_, fun h h' => ?_, fun h h' h'' => ?_⟩
  · have hk : ({u, v} : Finset Q).card ≤ K.card := Finset.card_le_card (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    rwa [Finset.card_pair huv] at hk
  · have hk := card_add_le K {u} (by simpa using h)
    rwa [Finset.card_singleton] at hk
  · have hk := card_add_le K {u, v} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    rwa [Finset.card_pair huv] at hk
  · have hk := card_add_le K {u, v, W.s} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
    rwa [card_three huv hus hvs] at hk

omit [DecidableEq Q] in
theorem single_ne_univ (hn : 2 ≤ Fintype.card Q) (v : Q) : ({v} : Finset Q) ≠ Finset.univ := by
  intro h
  have h' := congrArg Finset.card h
  rw [Finset.card_singleton, Finset.card_univ] at h'
  omega

/-! ### The class `{1/2, 2}` (tex:890-898) -/

omit [Fintype Q] in
/-- The doubled value `2 α(K) = 2|K| - e_u + 2 e_v`. -/
def VHalf (u v : Q) (K : Finset Q) : ℕ := 2 * K.card + 2 * (if v ∈ K then 1 else 0) - (if u ∈ K then 1 else 0)

theorem V_half (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2) (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2)
    (K : Finset Q) : (VHalf u v K : ℝ) = 2 * wt (A.alphaStat W.E (fun _ => 1 / 2)) K := by
  rw [sec54_alpha_formula_proved A W u v hX huv K, hu, hv]
  unfold VHalf
  by_cases hU : u ∈ K <;> by_cases hV : v ∈ K
  · have hk : 1 ≤ K.card := Finset.card_pos.mpr ⟨u, hU⟩
    rw [ein_mem hU, ein_mem hV]
    simp only [hU, hV, ↓reduceIte]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · have hk : 1 ≤ K.card := Finset.card_pos.mpr ⟨u, hU⟩
    rw [ein_mem hU, ein_not_mem hV]
    simp only [hU, hV, ↓reduceIte]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · rw [ein_not_mem hU, ein_mem hV]
    simp only [hU, hV, ↓reduceIte, Nat.sub_zero]
    push_cast
    ring
  · rw [ein_not_mem hU, ein_not_mem hV]
    simp only [hU, hV, ↓reduceIte, Nat.sub_zero]
    push_cast
    ring

theorem cost_le_half (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2) (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2)
    (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ) :
    A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ (cHalf (Fintype.card Q) (VHalf u v K) : ℕ∞) := by
  obtain ⟨hg, h2, h111, h000⟩ := cost_cases A a b hab hS hsc hn W u v hX huv (Or.inl hu) hv K hne hprop
  obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := card_facts A W hX huv K
  by_cases hU : u ∈ K <;> by_cases hV : v ∈ K
  · by_cases hS' : W.s ∈ K
    · refine (h111 hU hV hS').trans (Nat.cast_le.mpr ?_)
      unfold cHalf VHalf ce
      simp only [hU, hV, ↓reduceIte]
      split_ifs <;> omega
    · refine (h2 (iff_of_true hU hV) (iff_of_false hS' (not_not.mpr hV))).trans ?_
      have hc : 2 ≤ cHalf (Fintype.card Q) (VHalf u v K) := by
        have := hk2 hU hV
        unfold cHalf VHalf ce
        simp only [hU, hV, ↓reduceIte]
        split_ifs <;> omega
      exact_mod_cast hc
  · rw [hg (fun h => hV (h.mp hU))]
    have hc : 1 ≤ cHalf (Fintype.card Q) (VHalf u v K) := by
      have := hk1 hU
      unfold cHalf VHalf ce
      simp only [hU, hV, ↓reduceIte]
      split_ifs <;> omega
    exact_mod_cast hc
  · rw [hg (fun h => hU (h.mpr hV))]
    have hc : 1 ≤ cHalf (Fintype.card Q) (VHalf u v K) := by
      have := hk3 hU
      unfold cHalf VHalf ce
      simp only [hU, hV, ↓reduceIte]
      split_ifs <;> omega
    exact_mod_cast hc
  · by_cases hS' : W.s ∈ K
    · refine (h2 (iff_of_false hU hV) (iff_of_true hS' hV)).trans ?_
      have hc : 2 ≤ cHalf (Fintype.card Q) (VHalf u v K) := by
        have := hk4 hU hV
        unfold cHalf VHalf ce
        simp only [hU, hV, ↓reduceIte]
        split_ifs <;> omega
      exact_mod_cast hc
    · refine (h000 hU hV hS').trans (Nat.cast_le.mpr ?_)
      have := hk5 hU hV hS'
      unfold cHalf VHalf ce
      simp only [hU, hV, ↓reduceIte]
      split_ifs <;> omega

/-- The bound `n^2 - 3n + 4` in the class `{1/2, 2}`, with `t_u = 1/2` and `t_v = 2`. -/
theorem rt_half (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v})
    (huv : u ≠ v) (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 4 - 3 * Fintype.card Q : ℕ) : ℕ∞) := by
  obtain ⟨W', hE, -, hp⟩ := lem_5_7_a_proved A a b hab hS W
  obtain ⟨-, hstat, hpos⟩ := lem_5_5_proved A hsc W'
  rw [hE, hp] at hstat hpos
  have hhalf : IsLetterWeights (fun _ : S => (1 : ℝ) / 2) := by
    rw [← hp]
    exact W'.weights
  have hsing := single_ne_univ (by omega) v
  have hv1 : A.cost (A.alphaStat W.E (fun _ => 1 / 2)) {v} = 1 :=
    (cost_cases A a b hab hS hsc hn W u v hX huv (Or.inl hu) hv {v} (Finset.singleton_nonempty v) hsing).1
      (by simp [huv])
  have hcount := rt_count A hA _ hhalf _ hstat hpos (VHalf u v) (V_half A W u v hX huv hu hv)
    (cHalf (Fintype.card Q)) 4
    (fun K hne hprop _ => cost_le_half A a b hab hS hsc hn W u v hX huv hu hv K hne hprop) v
    (by simp [VHalf, huv]) hsing hv1
  have hVu : VHalf u v (Finset.univ : Finset Q) = 2 * Fintype.card Q + 1 := by
    simp only [VHalf, Finset.mem_univ, ↓reduceIte, Finset.card_univ]
    omega
  rw [hVu] at hcount
  exact hcount.trans (Nat.cast_le.mpr (sum_half _ hn))

/-! ### The class `{3/2, 2}` (tex:900-909) -/

omit [Fintype Q] in
/-- The doubled value `2 α(K) = 2|K| + e_u + 2 e_v`. -/
def VHi (u v : Q) (K : Finset Q) : ℕ := 2 * K.card + 2 * (if v ∈ K then 1 else 0) + (if u ∈ K then 1 else 0)

theorem V_hi (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 3/2) (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2)
    (K : Finset Q) : (VHi u v K : ℝ) = 2 * wt (A.alphaStat W.E (fun _ => 1 / 2)) K := by
  rw [sec54_alpha_formula_proved A W u v hX huv K, hu, hv]
  unfold VHi
  by_cases hU : u ∈ K <;> by_cases hV : v ∈ K
  · rw [ein_mem hU, ein_mem hV]
    simp only [hU, hV, ↓reduceIte]
    push_cast
    ring
  · rw [ein_mem hU, ein_not_mem hV]
    simp only [hU, hV, ↓reduceIte]
    push_cast
    ring
  · rw [ein_not_mem hU, ein_mem hV]
    simp only [hU, hV, ↓reduceIte]
    push_cast
    ring
  · rw [ein_not_mem hU, ein_not_mem hV]
    simp only [hU, hV, ↓reduceIte]
    push_cast
    ring

theorem cost_le_hi (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 3/2) (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2)
    (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ) :
    A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ (cHi (Fintype.card Q) (VHi u v K) : ℕ∞) := by
  obtain ⟨hg, h2, h111, h000⟩ := cost_cases A a b hab hS hsc hn W u v hX huv (Or.inr hu) hv K hne hprop
  obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := card_facts A W hX huv K
  by_cases hU : u ∈ K <;> by_cases hV : v ∈ K
  · have := hk2 hU hV
    by_cases hS' : W.s ∈ K
    · refine (h111 hU hV hS').trans (Nat.cast_le.mpr ?_)
      unfold cHi VHi coHi ce
      simp only [hU, hV, ↓reduceIte]
      split_ifs <;> omega
    · refine (h2 (iff_of_true hU hV) (iff_of_false hS' (not_not.mpr hV))).trans ?_
      have hc : 2 ≤ cHi (Fintype.card Q) (VHi u v K) := by
        unfold cHi VHi coHi ce
        simp only [hU, hV, ↓reduceIte]
        split_ifs <;> omega
      exact_mod_cast hc
  · rw [hg (fun h => hV (h.mp hU))]
    have hc : 1 ≤ cHi (Fintype.card Q) (VHi u v K) := by
      have := hk1 hU
      unfold cHi VHi coHi ce
      simp only [hU, hV, ↓reduceIte]
      split_ifs <;> omega
    exact_mod_cast hc
  · rw [hg (fun h => hU (h.mpr hV))]
    have hc : 1 ≤ cHi (Fintype.card Q) (VHi u v K) := by
      have := hk3 hU
      unfold cHi VHi coHi ce
      simp only [hU, hV, ↓reduceIte]
      split_ifs <;> omega
    exact_mod_cast hc
  · by_cases hS' : W.s ∈ K
    · refine (h2 (iff_of_false hU hV) (iff_of_true hS' hV)).trans ?_
      have hc : 2 ≤ cHi (Fintype.card Q) (VHi u v K) := by
        have := hk4 hU hV
        unfold cHi VHi coHi ce
        simp only [hU, hV, ↓reduceIte]
        split_ifs <;> omega
      exact_mod_cast hc
    · refine (h000 hU hV hS').trans (Nat.cast_le.mpr ?_)
      have := hk5 hU hV hS'
      unfold cHi VHi coHi ce
      simp only [hU, hV, ↓reduceIte]
      split_ifs <;> omega

/-- The bound `n^2 - 3n + 5` in the class `{3/2, 2}`, with `t_u = 3/2` and `t_v = 2`. -/
theorem rt_hi (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v})
    (huv : u ≠ v) (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q : ℕ) : ℕ∞) := by
  obtain ⟨W', hE, -, hp⟩ := lem_5_7_a_proved A a b hab hS W
  obtain ⟨-, hstat, hpos⟩ := lem_5_5_proved A hsc W'
  rw [hE, hp] at hstat hpos
  have hhalf : IsLetterWeights (fun _ : S => (1 : ℝ) / 2) := by
    rw [← hp]
    exact W'.weights
  have hsing := single_ne_univ (by omega) v
  have hv1 : A.cost (A.alphaStat W.E (fun _ => 1 / 2)) {v} = 1 :=
    (cost_cases A a b hab hS hsc hn W u v hX huv (Or.inr hu) hv {v} (Finset.singleton_nonempty v) hsing).1
      (by simp [huv])
  have hcount := rt_count A hA _ hhalf _ hstat hpos (VHi u v) (V_hi A W u v hX huv hu hv)
    (cHi (Fintype.card Q)) 4
    (fun K hne hprop _ => cost_le_hi A a b hab hS hsc hn W u v hX huv hu hv K hne hprop) v
    (by simp [VHi, huv]) hsing hv1
  have hVu : VHi u v (Finset.univ : Finset Q) = 2 * (Fintype.card Q + 1) + 1 := by
    simp only [VHi, Finset.mem_univ, ↓reduceIte, Finset.card_univ]
    omega
  rw [hVu] at hcount
  exact hcount.trans (Nat.cast_le.mpr (sum_hi _ hn))

end Prop513

/-- Proposition 5.13, tex:890-898: in the class `{1/2, 2}`, `rt ≤ n^2 - 3n + 4` for every `n ≥ 4`. -/
theorem prop_5_13_half_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 2), (2, 1/2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 4 - 3 * Fintype.card Q : ℕ) : ℕ∞) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcl
  rcases hcl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact rt_half A a b hab hS hA hsc hn W x₁ x₂ hX h12 h₁ h₂
  · exact rt_half A a b hab hS hA hsc hn W x₂ x₁ (by rw [hX, Finset.pair_comm]) h12.symm h₂ h₁

/-- Proposition 5.13, tex:866-868. If the witness has class {1/2,2} or {3/2,2}, the bound is n²−3n+5. -/
theorem prop_5_13_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 2), (2, 1/2), (3/2, 2), (2, 3/2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧
      Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q ≤ (Fintype.card Q - 1) ^ 2 := by
  have harith : Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q ≤ (Fintype.card Q - 1) ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card Q = m + 4 := ⟨Fintype.card Q - 4, by omega⟩
    rw [hm, show m + 4 - 1 = m + 3 by omega]
    have h1 : (m + 4) ^ 2 = m * m + 8 * m + 16 := by ring
    have h2 : (m + 3) ^ 2 = m * m + 6 * m + 9 := by ring
    omega
  refine ⟨?_, harith⟩
  have hle : ((Fintype.card Q ^ 2 + 4 - 3 * Fintype.card Q : ℕ) : ℕ∞) ≤
      ((Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
  have hX' : W.X = {x₂, x₁} := by rw [hX, Finset.pair_comm]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcl
  rcases hcl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact (rt_half A a b hab hS hA hsc hn W x₁ x₂ hX h12 h₁ h₂).trans hle
  · exact (rt_half A a b hab hS hA hsc hn W x₂ x₁ hX' h12.symm h₂ h₁).trans hle
  · exact rt_hi A a b hab hS hA hsc hn W x₁ x₂ hX h12 h₁ h₂
  · exact rt_hi A a b hab hS hA hsc hn W x₂ x₁ hX' h12.symm h₂ h₁

end Binary

end CernyQE
