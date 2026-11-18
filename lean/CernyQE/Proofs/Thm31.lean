/-
CernyQE/Proofs/Thm31.lean — Theorem 3.1 with its cases and Proposition 3.3, the level counts, and extension processes.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Proofs.Basic
import CernyQE.Proofs.Sec2

namespace CernyQE

open Classical Automaton Matrix

universe u v

/-! ### Arithmetic -/

private theorem step_arith (c d d' a : ℕ) (hd : d' + 1 ≤ d) (ha : a ≤ c) : a + c * d' ≤ c * d := by
  have h1 : c * (d' + 1) ≤ c * d := Nat.mul_le_mul_left c hd
  rw [Nat.mul_add, Nat.mul_one] at h1
  omega

private theorem mul_pred_add (c d : ℕ) (hd : 1 ≤ d) : c * d = c * (d - 1) + c := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]

private theorem arith_t1 {n : ℕ} (hn : 2 ≤ n) : 1 + (n - 2) * (n - 1) ≤ (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
  nlinarith

private theorem arith_A {n : ℕ} (hn : 2 ≤ n) : 1 + (n - 2) * n ≤ (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
  nlinarith

/-- The sequence `a, f 0, f 1, …`. -/
private def consSeq {β : Type*} (a : β) (f : ℕ → β) : ℕ → β
  | 0 => a
  | i + 1 => f i

private theorem flatten_length {S : Type*} (w : ℕ → List S) (J : ℕ) :
    (((List.range J).reverse.map w).flatten).length = ∑ j ∈ Finset.range J, (w j).length := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [ext_method_word_succ, List.length_append, ih, Finset.sum_range_succ]
    omega

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-! ### Weights of sets -/

omit [Fintype Q] [DecidableEq Q] in
private theorem wt_pos_of_nonempty {α : Q → ℝ} (hpos : ∀ q, 0 < α q) {K : Finset Q} (hK : K.Nonempty) :
    0 < wt α K :=
  Finset.sum_pos (fun q _ => hpos q) hK

omit [Fintype Q] [DecidableEq Q] in
private theorem nonempty_of_wt_pos {α : Q → ℝ} {K : Finset Q} (h : 0 < wt α K) : K.Nonempty := by
  rcases K.eq_empty_or_nonempty with hK | hK
  · rw [hK, wt_empty] at h
    exact absurd h (lt_irrefl 0)
  · exact hK

omit [DecidableEq Q] in
private theorem wt_le_univ {α : Q → ℝ} (hpos : ∀ q, 0 < α q) (K : Finset Q) : wt α K ≤ wt α Finset.univ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K) (fun q _ _ => (hpos q).le)

omit [Fintype Q] [DecidableEq Q] in
private theorem wt_one (K : Finset Q) : wt (fun _ : Q => (1 : ℝ)) K = K.card := by
  simp [wt]

omit [Fintype Q] [DecidableEq Q] in
private theorem card_le_sum_of_pos (u : Q → ℕ) (hu : ∀ q, 0 < u q) (K : Finset Q) :
    K.card ≤ ∑ q ∈ K, u q := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun q _ => hu q

omit [Fintype Q] in
/-- `α(K) = |K| + (t - 1) [x ∈ K]` for `α = alphaOff x t`. -/
private theorem wt_alphaOff (x : Q) (t : ℝ) (K : Finset Q) :
    wt (alphaOff x t) K = K.card + (if x ∈ K then t - 1 else 0) := by
  have h : ∀ q, alphaOff x t q = 1 + (if q = x then t - 1 else 0) := by
    intro q
    unfold alphaOff
    split_ifs <;> ring
  simp only [wt, h, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_ite_eq']

omit [Fintype Q] in
private theorem alphaOff_pos {x : Q} {t : ℝ} (h0 : 0 < t) : ∀ q, 0 < alphaOff x t q := by
  intro q
  unfold alphaOff
  split_ifs
  · exact h0
  · exact one_pos

omit [Fintype Q] in
/-- The four kinds of a raising step for `alphaOff x t`. -/
private theorem levels_cases {x : Q} {t : ℝ} {K K' : Finset Q}
    (hlt : wt (alphaOff x t) K < wt (alphaOff x t) K') :
    (x ∈ K → x ∈ K' → (K.card : ℝ) < K'.card) ∧ (x ∉ K → x ∉ K' → (K.card : ℝ) < K'.card) ∧
      (x ∈ K → x ∉ K' → (K.card : ℝ) + (t - 1) < K'.card) ∧
      (x ∉ K → x ∈ K' → (K.card : ℝ) < K'.card + (t - 1)) := by
  rw [wt_alphaOff, wt_alphaOff] at hlt
  refine ⟨fun hx hx' => ?_, fun hx hx' => ?_, fun hx hx' => ?_, fun hx hx' => ?_⟩
  · rw [ite_eq_left hx, ite_eq_left hx'] at hlt
    linarith
  · rw [ite_eq_right hx, ite_eq_right hx'] at hlt
    linarith
  · rw [ite_eq_left hx, ite_eq_right hx'] at hlt
    linarith
  · rw [ite_eq_right hx, ite_eq_left hx'] at hlt
    linarith

omit [Fintype Q] in
/-- Lemma 3.2(c) for `0 < t < 2`, `t ≠ 1`. -/
private theorem levels_c {x : Q} {t : ℝ} (h0 : 0 < t) (h2 : t < 2) {K K' : Finset Q}
    (hlt : wt (alphaOff x t) K < wt (alphaOff x t) K') :
    K.card ≤ K'.card ∧ (K'.card = K.card → (1 < t → x ∉ K ∧ x ∈ K') ∧ (t < 1 → x ∈ K ∧ x ∉ K')) := by
  obtain ⟨hkeep, hfree, hlose, hgain⟩ := levels_cases hlt
  have hle : K.card ≤ K'.card := by
    have hr : (K.card : ℝ) < K'.card + 1 := by
      by_cases hx : x ∈ K <;> by_cases hx' : x ∈ K'
      · linarith [hkeep hx hx']
      · linarith [hlose hx hx']
      · linarith [hgain hx hx']
      · linarith [hfree hx hx']
    have : K.card < K'.card + 1 := by exact_mod_cast hr
    omega
  refine ⟨hle, fun heq => ?_⟩
  have hr : (K'.card : ℝ) = K.card := by exact_mod_cast heq
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · by_cases hx : x ∈ K <;> by_cases hx' : x ∈ K'
    · linarith [hkeep hx hx']
    · linarith [hlose hx hx']
    · exact ⟨hx, hx'⟩
    · linarith [hfree hx hx']
  · by_cases hx : x ∈ K <;> by_cases hx' : x ∈ K'
    · linarith [hkeep hx hx']
    · exact ⟨hx, hx'⟩
    · linarith [hgain hx hx']
    · linarith [hfree hx hx']

omit [Fintype Q] in
/-- A word that moves `x` across `K` changes `alphaOff x t` when `t - 1` is not an integer. -/
private theorem wt_ne_of_moves {x : Q} {t : ℝ} (hg : ∀ z : ℤ, t - 1 ≠ z) (K K' : Finset Q)
    (hm : ¬ (x ∈ K' ↔ x ∈ K)) : wt (alphaOff x t) K' ≠ wt (alphaOff x t) K := by
  rw [wt_alphaOff, wt_alphaOff]
  intro h
  by_cases hx : x ∈ K
  · have hx' : x ∉ K' := fun h' => hm ⟨fun _ => hx, fun _ => h'⟩
    rw [ite_eq_right hx', ite_eq_left hx] at h
    exact hg ((K'.card : ℤ) - K.card) (by push_cast; linarith)
  · have hx' : x ∈ K' := by
      by_contra h'
      exact hm ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hx⟩
    rw [ite_eq_left hx', ite_eq_right hx] at h
    exact hg ((K.card : ℤ) - K'.card) (by push_cast; linarith)

omit [Fintype S] in
/-- Lemma 3.2(b): the cost is at most `esc(K)` when `t - 1` is not an integer. -/
private theorem cost_le_esc {x : Q} {t : ℝ} (hg : ∀ z : ℤ, t - 1 ≠ z) (K : Finset Q) :
    A.cost (alphaOff x t) K ≤ A.esc x K :=
  minLen_mono fun w hw => wt_ne_of_moves hg K (A.pre K w) (by
    rw [A.mem_pre]
    exact (A.movesAcross_iff x K w).mp hw)

/-- A word of length `m(K)` is at most `|K|` long if `x ∈ K` and at most `n - |K|` long if `x ∉ K` (Lemma 3.2(b) and the
orbit lemma). -/
private theorem len_le_esc_bound {x : Q} {t : ℝ} (hsc : A.StronglyConnected) (hg : ∀ z : ℤ, t - 1 ≠ z)
    {K : Finset Q} (hne : K.Nonempty) (hprop : K ≠ Finset.univ) {w : List S}
    (hwl : (w.length : ℕ∞) = A.cost (alphaOff x t) K) :
    (x ∈ K → w.length ≤ K.card) ∧ (x ∉ K → w.length ≤ Fintype.card Q - K.card) := by
  have hfin := lem_2_3_fin_core A hsc x K hne hprop
  have h2 : (w.length : ℕ∞) ≤ A.esc x K := by
    rw [hwl]
    exact cost_le_esc A hg K
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · exact_mod_cast h2.trans (lem_2_3_in_core A x K hfin hx)
  · exact_mod_cast h2.trans (lem_2_3_out_core A x K hfin hx)

private theorem not_int_of_lt_two {t : ℝ} (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) : ∀ z : ℤ, t - 1 ≠ z := by
  intro z hz
  have hz1 : (z : ℝ) < 1 := by linarith
  have hz0 : (-1 : ℝ) < z := by linarith
  have hz1' : z < 1 := by exact_mod_cast hz1
  have hz0' : -1 < z := by exact_mod_cast hz0
  have hz' : z = 0 := by omega
  rw [hz', Int.cast_zero] at hz
  exact h1 (by linarith)

/-! ### Words, reset words and the extension method -/

omit [Fintype S] in
private theorem rt_le_of_pre_singleton {r : Q} {u : List S} (h : A.pre {r} u = Finset.univ) :
    A.rt ≤ (u.length : ℕ∞) := by
  have hres : A.IsReset u := ⟨r, fun q => by
    have hq : q ∈ A.pre {r} u := h ▸ Finset.mem_univ q
    simpa using hq⟩
  exact minLen_le_length hres

omit [Fintype S] in
private theorem rt_le_of_pre_merge {r : Q} {c : S} {u : List S}
    (h : A.pre (A.pre {r} [c]) u = Finset.univ) : A.rt ≤ ((u.length + 1 : ℕ) : ℕ∞) := by
  have h' : A.pre {r} (u ++ [c]) = Finset.univ := by
    rw [A.pre_append]
    exact h
  have := rt_le_of_pre_singleton A h'
  rw [List.length_append, List.length_singleton] at this
  exact this

omit [Fintype S] in
private theorem ext_le_of {K : Finset Q} {w : List S} {k : ℕ} (hw : K.card < (A.pre K w).card)
    (hl : w.length ≤ k) : A.ext K ≤ (k : ℕ∞) :=
  minLen_le_iff.mpr ⟨w, hw, hl⟩

omit [Fintype S] in
/-- Strong induction along a strictly rising value: if every set of a class `C` other than `Q` has a word that raises
the value, stays in `C`, and pays for itself in the budget `B`, then every set of `C` has a word of length at most
`B K` whose preimage is `Q`. -/
private theorem reach_univ (v : Finset Q → ℝ) (C : Finset Q → Prop) (B : Finset Q → ℕ)
    (hstep : ∀ K, C K → K ≠ Finset.univ →
      ∃ w : List S, v K < v (A.pre K w) ∧ C (A.pre K w) ∧ w.length + B (A.pre K w) ≤ B K) :
    ∀ K, C K → ∃ u : List S, A.pre K u = Finset.univ ∧ u.length ≤ B K := by
  suffices H : ∀ N : ℕ, ∀ K, (Finset.univ.filter (fun T : Finset Q => v K < v T)).card = N → C K →
      ∃ u : List S, A.pre K u = Finset.univ ∧ u.length ≤ B K from
    fun K hK => H _ K rfl hK
  intro N
  induction' N using Nat.strong_induction_on with N ih
  intro K hN hK
  by_cases hKu : K = Finset.univ
  · exact ⟨[], by simp [hKu], by simp⟩
  obtain ⟨w, hlt, hC, hB⟩ := hstep K hK hKu
  have hsub : Finset.univ.filter (fun T : Finset Q => v (A.pre K w) < v T) ⊂
      Finset.univ.filter (fun T : Finset Q => v K < v T) := by
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨A.pre K w, ?_, ?_⟩
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact hlt.trans hT
    · simp [hlt]
    · simp
  have hlt' := Finset.card_lt_card hsub
  rw [hN] at hlt'
  obtain ⟨u, hu, hul⟩ := ih _ hlt' (A.pre K w) rfl hC
  refine ⟨u ++ w, ?_, ?_⟩
  · rw [A.pre_append, hu]
  · rw [List.length_append]
    omega

omit [Fintype S] in
/-- The bound from a uniform bound on `ext`: start at `{q} c⁻¹` for a merging letter `c`. -/
private theorem rt_le_of_ext_le_aux (hn : 2 ≤ Fintype.card Q) (r : Q) (c : S)
    (hcr : 2 ≤ (A.pre {r} [c]).card) (L : ℕ)
    (hext : ∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → A.ext K ≤ (L : ℕ∞)) :
    A.rt ≤ ((1 + (Fintype.card Q - 2) * L : ℕ) : ℕ∞) := by
  have hstep : ∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → ∃ w : List S,
      (K.card : ℝ) < (A.pre K w).card ∧ (A.pre K w).Nonempty ∧
        w.length + L * (Fintype.card Q - (A.pre K w).card) ≤ L * (Fintype.card Q - K.card) := by
    intro K hK hKu
    obtain ⟨w, hw, hwl⟩ := minLen_le_iff.mp (hext K hK hKu)
    have hw' : K.card < (A.pre K w).card := hw
    refine ⟨w, by exact_mod_cast hw', Finset.card_pos.mp (by omega), ?_⟩
    have hK'n : (A.pre K w).card ≤ Fintype.card Q := Finset.card_le_univ _
    exact step_arith _ _ _ _ (by omega) hwl
  obtain ⟨u, hu, hul⟩ := reach_univ A (fun K => (K.card : ℝ)) (fun K => K.Nonempty)
    (fun K => L * (Fintype.card Q - K.card)) hstep (A.pre {r} [c]) (Finset.card_pos.mp (by omega))
  refine (rt_le_of_pre_merge A hu).trans (Nat.cast_le.mpr ?_)
  have h1 : L * (Fintype.card Q - (A.pre {r} [c]).card) ≤ L * (Fintype.card Q - 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : L * (Fintype.card Q - 2) = (Fintype.card Q - 2) * L := Nat.mul_comm _ _
  have hul' : u.length ≤ L * (Fintype.card Q - (A.pre {r} [c]).card) := hul
  omega

/-- A raising word of length `m(K) ≤ n - 1` (Lemma 2.2). -/
private theorem raise_word (hA : A.Synchronizing) {p : S → ℝ} (hp : IsLetterWeights p) {α : Q → ℝ}
    (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) {K : Finset Q} (hne : K.Nonempty)
    (hprop : K ≠ Finset.univ) :
    ∃ w : List S, (w.length : ℕ∞) = A.cost α K ∧ w.length ≤ Fintype.card Q - 1 ∧ A.Raises α K w := by
  obtain ⟨⟨m, hm, -, hmn⟩, hw⟩ := sec2_cost_bounds_core A hA α hpos K hne hprop
  obtain ⟨w, hwl, hwr⟩ := hw p hp hα
  refine ⟨w, hwl, ?_, hwr⟩
  rw [hm] at hwl
  have : w.length = m := by exact_mod_cast hwl
  omega

/-- The level count: for a positive stationary vector whose set values are natural numbers `V K`, every nonempty `K`
reaches `Q` by a word of length at most `(n - 1)(V(Q) - V(K))`. -/
private theorem level_count (hA : A.Synchronizing) {p : S → ℝ} (hp : IsLetterWeights p) {α : Q → ℝ}
    (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) (V : Finset Q → ℕ) (hV : ∀ K, wt α K = V K)
    (K : Finset Q) (hK : K.Nonempty) :
    ∃ u : List S, A.pre K u = Finset.univ ∧ u.length ≤ (Fintype.card Q - 1) * (V Finset.univ - V K) := by
  refine reach_univ A (wt α) (fun K => K.Nonempty) (fun K => (Fintype.card Q - 1) * (V Finset.univ - V K))
    ?_ K hK
  intro K hK hKu
  obtain ⟨w, -, hwl, hw⟩ := raise_word A hA hp hα hpos hK hKu
  have hlt : wt α K < wt α (A.pre K w) := hw
  have hne' : (A.pre K w).Nonempty := nonempty_of_wt_pos ((wt_pos_of_nonempty hpos hK).trans hlt)
  refine ⟨w, hlt, hne', ?_⟩
  have h1 : V K < V (A.pre K w) := by
    rw [hV, hV] at hlt
    exact_mod_cast hlt
  have h2 : V (A.pre K w) ≤ V Finset.univ := by
    have := wt_le_univ hpos (A.pre K w)
    rw [hV, hV] at this
    exact_mod_cast this
  exact step_arith _ _ _ _ (by omega) hwl

/-! ### The merging letter, the case `t = 1`, Proposition 3.3 and the case `0 < t < 2` -/

theorem thm_3_1_merging_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) :
    ∃ (c : S) (q : Q), 2 ≤ (A.pre {q} [c]).card := by
  by_contra hno
  push Not at hno
  have hinj : ∀ c : S, Function.Injective (fun q => A.step q c) := by
    intro c a b hab
    have hab' : A.step b c = A.step a c := hab.symm
    have ha : a ∈ A.pre {A.step a c} [c] := by simp
    have hb : b ∈ A.pre {A.step a c} [c] := by simp [hab']
    have h1 := hno c (A.step a c)
    exact Finset.card_le_one.mp (by omega) a ha b hb
  have hw : ∀ w : List S, Function.Injective (fun q => A.act q w) := by
    intro w
    induction w with
    | nil => intro a b h; simpa using h
    | cons c w ih =>
      intro a b h
      have h' : A.act (A.step a c) w = A.act (A.step b c) w := h
      exact hinj c (ih h')
  obtain ⟨u, r, hr⟩ := hA
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Q)
  exact hab (hw u (show A.act a u = A.act b u by rw [hr, hr]))

theorem thm_3_1_case_t1_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (hα : A.IsStationary p (fun _ => 1)) :
    (∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → A.ext K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞)) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) := by
  have hext : ∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → A.ext K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞) := by
    intro K hK hKu
    obtain ⟨w, -, hwl, hw⟩ := raise_word A hA hp hα (fun _ => one_pos) hK hKu
    have h2 : wt (fun _ : Q => (1 : ℝ)) K < wt (fun _ : Q => (1 : ℝ)) (A.pre K w) := hw
    rw [wt_one, wt_one] at h2
    exact ext_le_of A (by exact_mod_cast h2) hwl
  obtain ⟨c, r, hcr⟩ := thm_3_1_merging_proved A hA hn
  exact ⟨hext, rt_le_of_ext_le_aux A hn r c hcr _ hext⟩

/-- Method, tex:194-196. When the first raising step preserves size, the individual bounds occur in the printed order for t < 1 and in reverse order for t > 1. -/
theorem method_pair_order_proved (hsc : A.StronglyConnected) (x : Q) (t : ℝ)
    (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) (K K' : Finset Q)
    (hne : K.Nonempty) (hp : K ≠ Finset.univ) (hne' : K'.Nonempty) (hp' : K' ≠ Finset.univ)
    (hraise : wt (alphaOff x t) K < wt (alphaOff x t) K') (hsame : K'.card = K.card) :
    (t < 1 → A.cost (alphaOff x t) K ≤ K.card ∧ A.cost (alphaOff x t) K' ≤ ((Fintype.card Q - K.card : ℕ) : ℕ∞)) ∧
    (1 < t → A.cost (alphaOff x t) K ≤ ((Fintype.card Q - K.card : ℕ) : ℕ∞) ∧ A.cost (alphaOff x t) K' ≤ K.card) := by
  have h := (levels_c h0 h2 hraise).2 hsame
  have hg := not_int_of_lt_two h0 h2 h1
  have f := lem_2_3_fin_core A hsc x K hne hp
  have f' := lem_2_3_fin_core A hsc x K' hne' hp'
  have c := cost_le_esc A (x := x) hg K
  have c' := cost_le_esc A (x := x) hg K'
  constructor
  · intro ht
    obtain ⟨hin,hout⟩ := h.2 ht
    exact ⟨c.trans (lem_2_3_in_core A x K f hin), by simpa [hsame] using c'.trans (lem_2_3_out_core A x K' f' hout)⟩
  · intro ht
    obtain ⟨hout,hin⟩ := h.1 ht
    exact ⟨c.trans (lem_2_3_out_core A x K f hout), by simpa [hsame] using c'.trans (lem_2_3_in_core A x K' f' hin)⟩

theorem prop_3_3_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (x : Q) (t : ℝ) (hα : A.IsStationary p (alphaOff x t)) (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1)
    (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ) :
    A.ext K ≤ (Fintype.card Q : ℕ∞) ∧ (¬ Expensive x t K → A.ext K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞)) := by
  have hpos : ∀ q, 0 < alphaOff x t q := alphaOff_pos h0
  have hsc := lem_2_1_core A hA p (alphaOff x t) hp hα hpos
  have hg := not_int_of_lt_two h0 h2 h1
  have hKn : K.card < Fintype.card Q := (Finset.card_lt_iff_ne_univ K).mpr hprop
  obtain ⟨w₁, hw₁c, hw₁n, hw₁⟩ := raise_word A hA hp hα hpos hne hprop
  obtain ⟨hle, hsame⟩ := levels_c (K' := A.pre K w₁) h0 h2 hw₁
  rcases Nat.lt_or_ge K.card (A.pre K w₁).card with hgt | hge
  · have hext : A.ext K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞) := ext_le_of A hgt hw₁n
    exact ⟨hext.trans (Nat.cast_le.mpr (Nat.sub_le _ _)), fun _ => hext⟩
  have hc : (A.pre K w₁).card = K.card := le_antisymm hge hle
  have hexp := hsame hc
  refine ⟨?_, fun hcheap => absurd ?_ hcheap⟩
  · have hK₁ne : (A.pre K w₁).Nonempty := Finset.card_pos.mp (by rw [hc]; exact Finset.card_pos.mpr hne)
    have hK₁u : A.pre K w₁ ≠ Finset.univ := by
      intro h
      rw [h, Finset.card_univ] at hc
      omega
    obtain ⟨w₂, hw₂c, -, hw₂⟩ := raise_word A hA hp hα hpos hK₁ne hK₁u
    obtain ⟨hle₂, hsame₂⟩ := levels_c (K' := A.pre (A.pre K w₁) w₂) h0 h2 hw₂
    have hb₁ := len_le_esc_bound A hsc hg hne hprop hw₁c
    have hb₂ := len_le_esc_bound A hsc hg hK₁ne hK₁u hw₂c
    have hgt₂ : (A.pre K w₁).card < (A.pre (A.pre K w₁) w₂).card := by
      rcases Nat.lt_or_ge (A.pre K w₁).card (A.pre (A.pre K w₁) w₂).card with h | h
      · exact h
      · exfalso
        have h' := hsame₂ (le_antisymm h hle₂)
        rcases lt_or_gt_of_ne h1 with ht | ht
        · exact (hexp.2 ht).2 (h'.2 ht).1
        · exact (h'.1 ht).1 (hexp.1 ht).2
    have hlen : w₂.length + w₁.length ≤ Fintype.card Q := by
      rcases lt_or_gt_of_ne h1 with ht | ht
      · have e1 := hb₁.1 (hexp.2 ht).1
        have e2 := hb₂.2 (hexp.2 ht).2
        omega
      · have e1 := hb₁.2 (hexp.1 ht).1
        have e2 := hb₂.1 (hexp.1 ht).2
        omega
    have hbig : K.card < (A.pre K (w₂ ++ w₁)).card := by
      rw [A.pre_append]
      omega
    exact ext_le_of A hbig (by rw [List.length_append]; exact hlen)
  · show (1 < t ∧ x ∉ K) ∨ (t < 1 ∧ x ∈ K)
    rcases lt_or_gt_of_ne h1 with ht | ht
    · exact Or.inr ⟨ht, (hexp.2 ht).1⟩
    · exact Or.inl ⟨ht, (hexp.1 ht).1⟩

theorem thm_3_1_case_A_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (x : Q) (t : ℝ) (hα : A.IsStationary p (alphaOff x t)) (h0 : 0 < t) (h2 : t < 2)
    (h1 : t ≠ 1) :
    A.rt ≤ ((1 + (Fintype.card Q - 2) * Fintype.card Q : ℕ) : ℕ∞) := by
  obtain ⟨c, r, hcr⟩ := thm_3_1_merging_proved A hA hn
  exact rt_le_of_ext_le_aux A hn r c hcr _ fun K hK hKu =>
    (prop_3_3_proved A hA hn p hp x t hα h0 h2 h1 K hK hKu).1

/-! ### The integer case and the level counts of Remarks 3.4 and 5.15 -/

theorem thm_3_1_case_int_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (x : Q) (k : ℕ) (hk : 1 ≤ k) (hα : A.IsStationary p (alphaOff x k)) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  have hpos : ∀ q, 0 < alphaOff x (k : ℝ) q := alphaOff_pos (Nat.cast_pos.mpr (by omega))
  let V : Finset Q → ℕ := fun K => K.card + (if x ∈ K then k - 1 else 0)
  have hV : ∀ K, wt (alphaOff x (k : ℝ)) K = V K := by
    intro K
    rw [wt_alphaOff]
    by_cases hx : x ∈ K <;> simp [V, hx, Nat.cast_sub hk]
  obtain ⟨u, hu, hul⟩ := level_count A hA hp hα hpos V hV {x} (Finset.singleton_nonempty x)
  refine (rt_le_of_pre_singleton A hu).trans (Nat.cast_le.mpr ?_)
  have e1 : V Finset.univ = Fintype.card Q + (k - 1) := by simp [V]
  have e2 : V {x} = 1 + (k - 1) := by simp [V]
  have h1 : V Finset.univ - V {x} = Fintype.card Q - 1 := by omega
  rw [h1] at hul
  rw [sq]
  exact hul

theorem rem_3_4_level_count_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (u : Q → ℕ) (hu : ∀ q, 0 < u q) (hstat : A.IsStationary p (fun q => (u q : ℝ))) :
    A.rt ≤ ((1 + (Fintype.card Q - 1) * (∑ q, u q - 2) : ℕ) : ℕ∞) := by
  have hpos : ∀ q, 0 < (u q : ℝ) := fun q => by exact_mod_cast hu q
  obtain ⟨c, r, hcr⟩ := thm_3_1_merging_proved A hA hn
  let V : Finset Q → ℕ := fun K => ∑ q ∈ K, u q
  have hV : ∀ K, wt (fun q => (u q : ℝ)) K = V K := by
    intro K
    simp [wt, V]
  obtain ⟨w, hw, hwl⟩ := level_count A hA hp hstat hpos V hV (A.pre {r} [c]) (Finset.card_pos.mp (by omega))
  refine (rt_le_of_pre_merge A hw).trans (Nat.cast_le.mpr ?_)
  have h1 : 2 ≤ V (A.pre {r} [c]) := le_trans hcr (card_le_sum_of_pos u hu _)
  have h2 : V Finset.univ = ∑ q, u q := rfl
  have h3 : (Fintype.card Q - 1) * (V Finset.univ - V (A.pre {r} [c])) ≤ (Fintype.card Q - 1) * (∑ q, u q - 2) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ### The case `t > 2` not an integer -/

/-- The budget of the joint claim: `(n-1)(n-|K|)` if `x ∈ K`, `(n-1)(n-|K|+h) + n-|K|` if `x ∉ K`. -/
private def budget (x : Q) (h : ℕ) (K : Finset Q) : ℕ :=
  if x ∈ K then (Fintype.card Q - 1) * (Fintype.card Q - K.card)
  else (Fintype.card Q - 1) * (Fintype.card Q - K.card + h) + (Fintype.card Q - K.card)

theorem thm_3_1_case_nonint_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (x : Q) (t : ℝ) (hα : A.IsStationary p (alphaOff x t)) (h2 : 2 < t)
    (hnz : ¬ ∃ z : ℤ, t = z) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  have hpos : ∀ q, 0 < alphaOff x t q := alphaOff_pos (by linarith)
  have hsc := lem_2_1_core A hA p (alphaOff x t) hp hα hpos
  have hg : ∀ z : ℤ, t - 1 ≠ z := fun z hz => hnz ⟨z + 1, by push_cast; linarith⟩
  obtain ⟨h, hh1, hh2⟩ : ∃ h : ℕ, (h : ℝ) ≤ t - 1 ∧ t - 1 < h + 1 :=
    ⟨⌊t - 1⌋₊, Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩
  have hstep : ∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → ∃ w : List S,
      wt (alphaOff x t) K < wt (alphaOff x t) (A.pre K w) ∧ (A.pre K w).Nonempty ∧
        w.length + budget x h (A.pre K w) ≤ budget x h K := by
    intro K hK hKu
    obtain ⟨w, hwc, hwl, hw⟩ := raise_word A hA hp hα hpos hK hKu
    have hlt : wt (alphaOff x t) K < wt (alphaOff x t) (A.pre K w) := hw
    refine ⟨w, hlt, nonempty_of_wt_pos ((wt_pos_of_nonempty hpos hK).trans hlt), ?_⟩
    have hKn : K.card < Fintype.card Q := (Finset.card_lt_iff_ne_univ K).mpr hKu
    have hK'n : (A.pre K w).card ≤ Fintype.card Q := Finset.card_le_univ _
    have hb := len_le_esc_bound A hsc hg hK hKu hwc
    obtain ⟨hkeep, hfree, hlose, hgain⟩ := levels_cases hlt
    by_cases hx : x ∈ K <;> by_cases hx' : x ∈ A.pre K w
    · -- keep
      have hc : K.card < (A.pre K w).card := by exact_mod_cast hkeep hx hx'
      rw [budget, budget, ite_eq_left hx, ite_eq_left hx']
      exact step_arith _ _ _ _ (by omega) hwl
    · -- lose
      have hc : K.card + h < (A.pre K w).card := by
        have e := hlose hx hx'
        have e' : (K.card : ℝ) + h < (A.pre K w).card := by linarith
        exact_mod_cast e'
      have hwK := hb.1 hx
      rw [budget, budget, ite_eq_left hx, ite_eq_right hx']
      have e1 : (Fintype.card Q - 1) * (Fintype.card Q - (A.pre K w).card + h) ≤
          (Fintype.card Q - 1) * (Fintype.card Q - K.card - 1) := Nat.mul_le_mul_left _ (by omega)
      have e2 : (Fintype.card Q - 1) * (Fintype.card Q - K.card) =
          (Fintype.card Q - 1) * (Fintype.card Q - K.card - 1) + (Fintype.card Q - 1) :=
        mul_pred_add _ _ (by omega)
      omega
    · -- gain
      have hc : K.card ≤ (A.pre K w).card + h := by
        have e := hgain hx hx'
        have e' : (K.card : ℝ) < (A.pre K w).card + h + 1 := by linarith
        have e'' : K.card < (A.pre K w).card + h + 1 := by exact_mod_cast e'
        omega
      have hwK := hb.2 hx
      rw [budget, budget, ite_eq_right hx, ite_eq_left hx']
      have e1 : (Fintype.card Q - 1) * (Fintype.card Q - (A.pre K w).card) ≤
          (Fintype.card Q - 1) * (Fintype.card Q - K.card + h) := Nat.mul_le_mul_left _ (by omega)
      omega
    · -- free
      have hc : K.card < (A.pre K w).card := by exact_mod_cast hfree hx hx'
      rw [budget, budget, ite_eq_right hx, ite_eq_right hx']
      have e1 : (Fintype.card Q - 1) * (Fintype.card Q - (A.pre K w).card + h) ≤
          (Fintype.card Q - 1) * (Fintype.card Q - K.card + h - 1) := Nat.mul_le_mul_left _ (by omega)
      have e2 : (Fintype.card Q - 1) * (Fintype.card Q - K.card + h) =
          (Fintype.card Q - 1) * (Fintype.card Q - K.card + h - 1) + (Fintype.card Q - 1) :=
        mul_pred_add _ _ (by omega)
      omega
  obtain ⟨u, hu, hul⟩ := reach_univ A (wt (alphaOff x t)) (fun K => K.Nonempty) (budget x h) hstep {x}
    (Finset.singleton_nonempty x)
  refine (rt_le_of_pre_singleton A hu).trans (Nat.cast_le.mpr ?_)
  rw [budget, ite_eq_left (Finset.mem_singleton_self x), Finset.card_singleton] at hul
  rw [sq]
  exact hul

theorem thm_3_1_nonint_pair_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (x : Q) (t : ℝ) (hα : A.IsStationary p (alphaOff x t)) (h2 : 2 < t)
    (hnz : ¬ ∃ z : ℤ, t = z) (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ)
    (hP : A.IsProcess (alphaOff x t) K w J) (hK0 : K 0 = {x}) (j j' : ℕ) (hjj : j < j') (hj' : j' < J)
    (hlose : x ∈ K j ∧ x ∉ K (j + 1)) (hfree : ∀ i, j < i → i ≤ j' → x ∉ K i) (hgain : x ∈ K (j' + 1)) :
    (w j).length + (w j').length ≤ Fintype.card Q - 2 := by
  have hpos : ∀ q, 0 < alphaOff x t q := alphaOff_pos (by linarith)
  have hsc := lem_2_1_core A hA p (alphaOff x t) hp hα hpos
  have hg : ∀ z : ℤ, t - 1 ≠ z := fun z hz => hnz ⟨z + 1, by push_cast; linarith⟩
  obtain ⟨hstep, -⟩ := hP
  have hraise : ∀ i < J, wt (alphaOff x t) (K i) < wt (alphaOff x t) (K (i + 1)) := by
    intro i hi
    obtain ⟨-, hKs, -, hr⟩ := hstep i hi
    rw [hKs]
    exact hr
  have hmono : ∀ d, j + 1 + d ≤ j' → (K (j + 1)).card ≤ (K (j + 1 + d)).card := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      have e1 := ih (by omega)
      have hi : j + 1 + d < J := by omega
      have hfa := hfree (j + 1 + d) (by omega) (by omega)
      have hfb := hfree (j + 1 + d + 1) (by omega) (by omega)
      have e2 := (levels_cases (hraise _ hi)).2.1 hfa hfb
      have e3 : (K (j + 1 + d)).card < (K (j + 1 + d + 1)).card := by exact_mod_cast e2
      rw [show j + 1 + (d + 1) = j + 1 + d + 1 by omega]
      omega
  have hjJ : j < J := by omega
  obtain ⟨hju, -, hjc, -⟩ := hstep j hjJ
  obtain ⟨hj'u, -, hj'c, -⟩ := hstep j' hj'
  have hl := (levels_cases (hraise j hjJ)).2.2.1 hlose.1 hlose.2
  have hjc2 : (K j).card + 2 ≤ (K (j + 1)).card := by
    have e1 : ((K j).card : ℝ) + 1 < (K (j + 1)).card := by linarith
    have e2 : (K j).card + 1 < (K (j + 1)).card := by exact_mod_cast e1
    omega
  have hm := hmono (j' - (j + 1)) (by omega)
  rw [show j + 1 + (j' - (j + 1)) = j' by omega] at hm
  have hx' : x ∉ K j' := hfree j' hjj le_rfl
  have hj'ne : (K j').Nonempty := Finset.card_pos.mp (by omega)
  have hjne : (K j).Nonempty := ⟨x, hlose.1⟩
  have hb1 := (len_le_esc_bound A hsc hg hjne hju hjc).1 hlose.1
  have hb2 := (len_le_esc_bound A hsc hg hj'ne hj'u hj'c).2 hx'
  have hcardn : (K j').card ≤ Fintype.card Q := Finset.card_le_univ _
  omega

/-! ### Theorem 3.1 -/

theorem thm_3_1_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (α : Q → ℝ) (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) (x : Q)
    (hconst : ∀ q q', q ≠ x → q' ≠ x → α q = α q') :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  obtain ⟨q₁, hq₁⟩ : ∃ q, q ≠ x := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Q)
    by_cases ha : a = x
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  have hcpos : 0 < α q₁ := hpos q₁
  obtain ⟨t, ht⟩ : ∃ t, t = α x / α q₁ := ⟨_, rfl⟩
  have hscale : alphaOff x t = (α q₁)⁻¹ • α := by
    funext q
    simp only [alphaOff, Pi.smul_apply, smul_eq_mul]
    split_ifs with hq
    · rw [hq, ht, div_eq_inv_mul]
    · rw [hconst q q₁ hq hq₁, inv_mul_cancel₀ hcpos.ne']
  have hα' : A.IsStationary p (alphaOff x t) := by
    rw [hscale]
    refine ⟨smul_ne_zero (inv_ne_zero hcpos.ne') hα.1, ?_⟩
    rw [Matrix.smul_vecMul, hα.2]
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos (hpos x) hcpos
  rcases lt_trichotomy t 1 with hlt1 | heq1 | hgt1
  · exact (thm_3_1_case_A_proved A hA hn p hp x t hα' htpos (by linarith) hlt1.ne).trans
      (Nat.cast_le.mpr (arith_A hn))
  · have h1 : alphaOff x t = fun _ => 1 := by
      funext q
      simp [alphaOff, heq1]
    rw [h1] at hα'
    exact (thm_3_1_case_t1_proved A hA hn p hp hα').2.trans (Nat.cast_le.mpr (arith_t1 hn))
  · by_cases ht2 : t < 2
    · exact (thm_3_1_case_A_proved A hA hn p hp x t hα' htpos ht2 hgt1.ne').trans
        (Nat.cast_le.mpr (arith_A hn))
    · by_cases hint : ∃ z : ℤ, t = z
      · obtain ⟨z, hz⟩ := hint
        have hz2 : (2 : ℝ) ≤ z := by linarith
        have hz2' : (2 : ℤ) ≤ z := by exact_mod_cast hz2
        obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ z)
        have htk : t = (k : ℝ) := by
          rw [hz]
          push_cast
          rfl
        rw [htk] at hα'
        exact thm_3_1_case_int_proved A hA hn p hp x k (by omega) hα'
      · have h2' : 2 < t := by
          rcases (not_lt.mp ht2).lt_or_eq with h | h
          · exact h
          · exact absurd ⟨2, by rw [← h]; norm_num⟩ hint
        exact thm_3_1_case_nonint_proved A hA hn p hp x t hα' h2' hint

/-! ### Extension processes (Section 5.4) -/

theorem sec54_process_exists_proved (hA : A.Synchronizing) (p : S → ℝ) (hp : IsLetterWeights p) (α : Q → ℝ)
    (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) (K₀ : Finset Q) (hne : K₀.Nonempty) :
    ∃ (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ), K 0 = K₀ ∧ A.IsProcess α K w J := by
  suffices H : ∀ N : ℕ, ∀ K₀ : Finset Q,
      (Finset.univ.filter (fun T : Finset Q => wt α K₀ < wt α T)).card = N → K₀.Nonempty →
      ∃ (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ), K 0 = K₀ ∧ A.IsProcess α K w J from
    H _ K₀ rfl hne
  intro N
  induction' N using Nat.strong_induction_on with N ih
  intro K₀ hN hne
  by_cases hKu : K₀ = Finset.univ
  · exact ⟨fun _ => K₀, fun _ => [], 0, rfl, fun j hj => absurd hj (Nat.not_lt_zero j), hKu⟩
  obtain ⟨-, hw⟩ := sec2_cost_bounds_core A hA α hpos K₀ hne hKu
  obtain ⟨w₀, hw₀c, hw₀⟩ := hw p hp hα
  have hlt : wt α K₀ < wt α (A.pre K₀ w₀) := hw₀
  have hne' : (A.pre K₀ w₀).Nonempty := nonempty_of_wt_pos ((wt_pos_of_nonempty hpos hne).trans hlt)
  have hsub : Finset.univ.filter (fun T : Finset Q => wt α (A.pre K₀ w₀) < wt α T) ⊂
      Finset.univ.filter (fun T : Finset Q => wt α K₀ < wt α T) := by
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨A.pre K₀ w₀, ?_, ?_⟩
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact hlt.trans hT
    · simp [hlt]
    · simp
  have hlt' := Finset.card_lt_card hsub
  rw [hN] at hlt'
  obtain ⟨K, w, J, hK0, hP⟩ := ih _ hlt' (A.pre K₀ w₀) rfl hne'
  refine ⟨consSeq K₀ K, consSeq w₀ w, J + 1, rfl, ?_, hP.2⟩
  intro j hj
  cases j with
  | zero => exact ⟨hKu, hK0, hw₀c, hw₀⟩
  | succ i => exact hP.1 i (by omega)

theorem sec54_process_props_proved (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (K : ℕ → Finset Q) (w : ℕ → List S)
    (J : ℕ) (hP : A.IsProcess α K w J) (hne : (K 0).Nonempty) :
    (∀ i j, i < j → j ≤ J → wt α (K i) < wt α (K j)) ∧ (∀ i j, i ≤ J → j ≤ J → K i = K j → i = j) ∧
      (∀ j ≤ J, (K j).Nonempty) ∧ (∀ q, A.act q (((List.range J).reverse.map w).flatten) ∈ K 0) ∧
      ((∃ r, K 0 = {r}) → A.rt ≤ ((∑ j ∈ Finset.range J, (w j).length : ℕ) : ℕ∞)) ∧
      (∀ (r : Q) (c : S), K 0 = A.pre {r} [c] →
        A.rt ≤ ((∑ j ∈ Finset.range J, (w j).length + 1 : ℕ) : ℕ∞)) := by
  obtain ⟨hstep, hJ⟩ := hP
  have hraise : ∀ i < J, wt α (K i) < wt α (K (i + 1)) := by
    intro i hi
    obtain ⟨-, hKs, -, hr⟩ := hstep i hi
    rw [hKs]
    exact hr
  have hmono : ∀ i j, i < j → j ≤ J → wt α (K i) < wt α (K j) := by
    intro i j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro hij hjJ
      by_cases h : i < j
      · exact (ih h (by omega)).trans (hraise j (by omega))
      · have e : i = j := by omega
        subst e
        exact hraise i (by omega)
  have hinj : ∀ i j, i ≤ J → j ≤ J → K i = K j → i = j := by
    intro i j hi hj hK
    rcases lt_trichotomy i j with h | h | h
    · exact absurd (congrArg (wt α) hK) (hmono i j h hj).ne
    · exact h
    · exact absurd (congrArg (wt α) hK).symm (hmono j i h hi).ne
  have hnej : ∀ j ≤ J, (K j).Nonempty := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h]
      exact hne
    · exact nonempty_of_wt_pos ((wt_pos_of_nonempty hpos hne).trans (hmono 0 j h hj))
  obtain ⟨-, hmap, hsing, hmerge⟩ := sec2_ext_method_core A K w J (fun j hj => (hstep j hj).2.1) hJ
  have hlen := flatten_length w J
  refine ⟨hmono, hinj, hnej, hmap, fun hr => ?_, fun r c hrc => ?_⟩
  · have e := minLen_le_length (hsing hr)
    rw [hlen] at e
    exact e
  · have e := minLen_le_length (hmerge r c hrc)
    rw [List.length_append, List.length_singleton, hlen] at e
    exact e

/-! ### Section 6 -/

theorem sec6_thm31_answers_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (α : Q → ℝ) (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) (v₁ v₂ : ℝ)
    (hrange : ∀ q, α q = v₁ ∨ α q = v₂) (hone : (Finset.univ.filter (fun q => α q = v₁)).card = 1) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
  have hv : ∀ r, r ≠ x → α r = v₂ := by
    intro r hr
    rcases hrange r with h | h
    · exfalso
      have hmem : r ∈ Finset.univ.filter (fun q => α q = v₁) := by simp [h]
      rw [hx, Finset.mem_singleton] at hmem
      exact hr hmem
    · exact h
  exact thm_3_1_proved A hA hn p hp α hα hpos x fun q q' hq hq' => by rw [hv q hq, hv q' hq']

end General

/-! ### Corollary 5.15 (level count) -/

theorem rem_5_15_level_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]
    (A : Automaton Q S) (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (u : Q → ℕ) (hu : ∀ q, 0 < u q) (hstat : A.IsStationary p (fun q => (u q : ℝ)))
    (hmax : ∃ q₀, ∑ q, u q ≤ Fintype.card Q + u q₀) :
    A.rt ≤ ((Fintype.card Q * (Fintype.card Q - 1) : ℕ) : ℕ∞) := by
  obtain ⟨q₀, hq₀⟩ := hmax
  have hpos : ∀ q, 0 < (u q : ℝ) := fun q => by exact_mod_cast hu q
  let V : Finset Q → ℕ := fun K => ∑ q ∈ K, u q
  have hV : ∀ K, wt (fun q => (u q : ℝ)) K = V K := by
    intro K
    simp [wt, V]
  obtain ⟨w, hw, hwl⟩ := level_count A hA hp hstat hpos V hV {q₀} (Finset.singleton_nonempty q₀)
  refine (rt_le_of_pre_singleton A hw).trans (Nat.cast_le.mpr ?_)
  have h1 : V {q₀} = u q₀ := by simp [V]
  have h2 : V Finset.univ = ∑ q, u q := rfl
  have h3 : (Fintype.card Q - 1) * (V Finset.univ - V {q₀}) ≤ (Fintype.card Q - 1) * Fintype.card Q :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_comm (Fintype.card Q)]
  omega

end CernyQE
