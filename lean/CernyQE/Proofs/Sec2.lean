/-
CernyQE/Proofs/Sec2.lean — proofs of the results of Section 2: Lemmas 2.1-2.4 and Remark 2.5.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Automaton
import CernyQE.Defs.Tier
import CernyQE.Proofs.LinAlg
import CernyQE.Proofs.Basic

open Matrix

namespace CernyQE

namespace Automaton

variable {Q S : Type*} (A : Automaton Q S)

/-- A set of states that every letter maps into itself is mapped into itself by every word. -/
theorem act_mem_of_closed (P : Q → Prop) (hP : ∀ q, P q → ∀ b, P (A.step q b)) :
    ∀ (w : List S) (q : Q), P q → P (A.act q w) := by
  intro w
  induction w with
  | nil => intro q hq; exact hq
  | cons b w ih => intro q hq; exact ih _ (hP q hq b)

variable [Fintype Q] [DecidableEq Q]

omit [Fintype Q] in
/-- `w` moves `x` across `K` iff exactly one of `x`, `x.w` lies in `K`. -/
theorem movesAcross_iff (x : Q) (K : Finset Q) (w : List S) :
    A.MovesAcross x K w ↔ ¬ (A.act x w ∈ K ↔ x ∈ K) := by
  simp [MovesAcross, decide_eq_decide]

open Classical in
/-- The states reachable from `x` by words of length at most `i` (the sets `R_i` of tex:320). -/
noncomputable def reach (x : Q) (i : ℕ) : Finset Q :=
  Finset.univ.filter (fun q => ∃ w : List S, w.length ≤ i ∧ A.act x w = q)

omit [Fintype Q] [DecidableEq Q] in
/-- A nonempty word is a shorter word followed by one letter. -/
theorem exists_concat_of_length (w : List S) {i : ℕ} (hw : w.length = i + 1) :
    ∃ (v : List S) (b : S), w = v ++ [b] ∧ v.length = i := by
  have hne : w ≠ [] := by rintro rfl; simp at hw
  refine ⟨w.dropLast, w.getLast hne, (List.dropLast_append_getLast hne).symm, ?_⟩
  simp [List.length_dropLast, hw]

omit [DecidableEq Q] in
theorem reach_mono (x : Q) (i : ℕ) : A.reach x i ⊆ A.reach x (i + 1) := by
  intro q hq
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  obtain ⟨w, hw, rfl⟩ := hq
  exact ⟨w, by omega, rfl⟩

omit [DecidableEq Q] in
theorem reach_step (x : Q) (i : ℕ) (h : A.reach x i = A.reach x (i + 1)) :
    A.reach x (i + 1) = A.reach x (i + 2) := by
  refine Finset.Subset.antisymm (A.reach_mono x (i + 1)) ?_
  intro q hq
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  by_cases hshort : w.length ≤ i + 1
  · simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hshort, rfl⟩
  obtain ⟨v, b, rfl, hv⟩ := exists_concat_of_length w (i := i + 1) (by omega)
  have hvmem : A.act x v ∈ A.reach x (i + 1) := by
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv.le, rfl⟩
  rw [← h] at hvmem
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hvmem
  obtain ⟨v', hv', hvv'⟩ := hvmem
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v' ++ [b], by simp; omega, by rw [act_concat, act_concat, hvv']⟩

/-- The orbit bound behind Lemma 2.3: if every word shorter than `f` keeps `x` in `G` and some word of length `f`
takes it out, then `f ≤ |G|`. -/
theorem orbit_bound (x : Q) (G : Finset Q) (f : ℕ) (hx : x ∈ G)
    (hshort : ∀ w : List S, w.length < f → A.act x w ∈ G) (w0 : List S) (hw0 : w0.length = f)
    (hout : A.act x w0 ∉ G) : f ≤ G.card := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      rw [List.length_eq_zero_iff] at hw0
      subst hw0
      exact absurd hx hout
    · exact h0
  have hsub : A.reach x (f - 1) ⊆ G := by
    intro q hq
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    exact hshort w (by omega)
  have hne : A.reach x (f - 1) ≠ A.reach x f := by
    intro heq
    have hmem : A.act x w0 ∈ A.reach x f := by
      simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w0, hw0.le, rfl⟩
    rw [← heq] at hmem
    exact hout (hsub hmem)
  have hchain := finset_chain_card_ge (A.reach x) (A.reach_mono x) (A.reach_step x) f hne (f - 1) le_rfl
  have h0 : 1 ≤ (A.reach x 0).card := by
    refine Finset.card_pos.mpr ⟨x, ?_⟩
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], le_rfl, rfl⟩
  have hG := Finset.card_le_card hsub
  omega

end Automaton

open Automaton

/-! ### Lemma 2.1 (strong connectivity) -/

theorem lem_2_1_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → ∀ (p : S → ℝ) (α : Q → ℝ), IsLetterWeights p → A.IsStationary p α →
    (∀ q, 0 < α q) → A.StronglyConnected := by
  rintro ⟨u, r, hr⟩ p α hp hα hpos C hC
  by_cases hCe : C = ∅
  · exact Or.inl hCe
  right
  -- π(q) = (M 𝟙_C)_q = ∑_b p_b [q.b ∈ C]
  have hμ : ∀ q, (A.M p *ᵥ ind C) q = ∑ b, p b * ind C (A.step q b) := A.M_mulVec p (ind C)
  have hμnn : ∀ q, 0 ≤ ∑ b, p b * ind C (A.step q b) := fun q =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hp.1 b).le (by rw [ind_apply]; split_ifs <;> norm_num)
  have hμC : ∀ q ∈ C, ∑ b, p b * ind C (A.step q b) = 1 := by
    intro q hq
    simp only [ind_apply, hC q hq, ↓reduceIte, mul_one]
    exact hp.2
  have hsum := (eq_2_1_core A p α hα C).2
  rw [dotProduct, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ C)] at hsum
  have hin : ∑ q ∈ Finset.univ.filter (· ∈ C), α q * (A.M p *ᵥ ind C) q = wt α C := by
    rw [wt]
    have hfilt : Finset.univ.filter (· ∈ C) = C := by ext q; simp
    rw [hfilt]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hμ, hμC q hq, mul_one]
  rw [hin, add_eq_left] at hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => mul_nonneg (hpos q).le (by rw [hμ]; exact hμnn q)).mp hsum
  -- the complement of C is closed
  have hcomp : ∀ q, q ∉ C → ∀ b, A.step q b ∉ C := by
    intro q hq b hb
    have h1 := hz q (by simpa using hq)
    rw [hμ] at h1
    have h2 : ∑ b, p b * ind C (A.step q b) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (hpos q).ne'
      · exact h
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
      mul_nonneg (hp.1 b).le (by rw [ind_apply]; split_ifs <;> norm_num)).mp h2 b (Finset.mem_univ b)
    simp only [ind_apply, hb, ↓reduceIte, mul_one] at h3
    exact (hp.1 b).ne' h3
  -- a reset word maps C into C and the complement into the complement
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hCe
  rw [Finset.eq_univ_iff_forall]
  intro q
  by_contra hq
  have h1 : A.act c u ∈ C := A.act_mem_of_closed (· ∈ C) (fun q hq b => hC q hq b) u c hc
  have h2 : A.act q u ∉ C := A.act_mem_of_closed (· ∉ C) (fun q hq b => hcomp q hq b) u q hq
  rw [hr] at h1 h2
  exact h2 h1

/-! ### Lemma 2.3 (orbit lemma) -/

theorem lem_2_3_in_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (x : Q) (K : Finset Q), A.esc x K ≠ ⊤ → x ∈ K → A.esc x K ≤ K.card := by
  intro x K hfin hx
  obtain ⟨f, hf⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨⟨w0, hw0, hw0l⟩, hshort⟩ := minLen_eq_coe hf.symm
  rw [← hf]
  refine Nat.cast_le.mpr (A.orbit_bound x K f hx (fun w hw => ?_) w0 hw0l ?_)
  · have h := hshort w hw
    rw [movesAcross_iff] at h
    push Not at h
    tauto
  · rw [movesAcross_iff] at hw0
    tauto

theorem lem_2_3_out_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (x : Q) (K : Finset Q), A.esc x K ≠ ⊤ → x ∉ K → A.esc x K ≤ (Fintype.card Q - K.card : ℕ) := by
  intro x K hfin hx
  obtain ⟨f, hf⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨⟨w0, hw0, hw0l⟩, hshort⟩ := minLen_eq_coe hf.symm
  rw [← hf]
  have hcard : (Finset.univ \ K).card = Fintype.card Q - K.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K), Finset.card_univ]
  rw [← hcard]
  refine Nat.cast_le.mpr (A.orbit_bound x (Finset.univ \ K) f (by simpa using hx) (fun w hw => ?_) w0 hw0l ?_)
  · have h := hshort w hw
    rw [movesAcross_iff] at h
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  · rw [movesAcross_iff] at hw0
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto

theorem lem_2_3_fin_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.StronglyConnected → ∀ (x : Q) (K : Finset Q), K.Nonempty → K ≠ Finset.univ → A.esc x K ≠ ⊤ := by
  classical
  intro hsc x K hK hKu
  let Rall : Finset Q := Finset.univ.filter (fun q => ∃ w : List S, A.act x w = q)
  have hclosed : A.IsClosed Rall := by
    intro q hq b
    simp only [Rall, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    obtain ⟨w, rfl⟩ := hq
    exact ⟨w ++ [b], A.act_concat x w b⟩
  have hall : ∀ q, ∃ w : List S, A.act x w = q := by
    rcases hsc Rall hclosed with h | h
    · have hx : x ∈ Rall := by
        simp only [Rall, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨[], rfl⟩
      rw [h] at hx
      simp at hx
    · intro q
      have hq : q ∈ Rall := by rw [h]; exact Finset.mem_univ q
      simpa [Rall] using hq
  have hmove : ∃ w : List S, A.MovesAcross x K w := by
    by_cases hx : x ∈ K
    · obtain ⟨q, hq⟩ : ∃ q, q ∉ K := by
        by_contra h
        push Not at h
        exact hKu (Finset.eq_univ_iff_forall.mpr h)
      obtain ⟨w, hw⟩ := hall q
      exact ⟨w, by rw [movesAcross_iff, hw]; tauto⟩
    · obtain ⟨q, hq⟩ := hK
      obtain ⟨w, hw⟩ := hall q
      exact ⟨w, by rw [movesAcross_iff, hw]; tauto⟩
  obtain ⟨w, hw⟩ := hmove
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top w.length) (minLen_le_length hw)

/-! ### Lemma 2.2 (the extension step) -/

namespace Automaton

section Step

variable {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- The linear functional `v ↦ β ⬝ v`. -/
noncomputable def dotL (β : Q → ℝ) : (Q → ℝ) →ₗ[ℝ] ℝ where
  toFun v := β ⬝ᵥ v
  map_add' u v := dotProduct_add β u v
  map_smul' c v := by simp [dotProduct_smul]

omit [Fintype S] in
/-- The weight of a preimage under a reset word is `0` or `β(Q)`. -/
theorem wt_pre_reset (β : Q → ℝ) (K : Finset Q) {u : List S} (hu : A.IsReset u) :
    wt β (A.pre K u) = 0 ∨ wt β (A.pre K u) = wt β Finset.univ := by
  obtain ⟨r, hr⟩ := hu
  by_cases hrK : r ∈ K
  · right
    congr 1
    ext q
    simp [hr, hrK]
  · left
    have : A.pre K u = ∅ := by
      ext q
      simp [hr, hrK]
    rw [this, wt_empty]

omit [Fintype S] in
/-- Under the hypotheses of Lemma 2.2, the cost is finite. -/
theorem cost_ne_top (hsync : A.Synchronizing) (β : Q → ℝ) (K : Finset Q) (hK0 : wt β K ≠ 0)
    (hKQ : wt β K ≠ wt β Finset.univ) : A.cost β K ≠ ⊤ := by
  obtain ⟨u, hu⟩ := hsync
  have hP : wt β (A.pre K u) ≠ wt β K := by
    rcases A.wt_pre_reset β K hu with h | h <;> rw [h]
    · exact Ne.symm hK0
    · exact Ne.symm hKQ
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top u.length) (minLen_le_length hP)

omit [Fintype S] in
/-- The cost is at least one: the empty word changes nothing. -/
theorem one_le_of_cost_eq (β : Q → ℝ) (K : Finset Q) {m : ℕ} (hm : A.cost β K = m) : 1 ≤ m := by
  obtain ⟨⟨w0, hw0, hw0l⟩, -⟩ := minLen_eq_coe hm
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [List.length_eq_zero_iff] at hw0l
    subst hw0l
    simp at hw0
  · exact h

/-- The chain `L_i = span{M_w ζ_K : |w| ≤ i}` of the proof of Lemma 2.2(a). -/
noncomputable def chainL (v : Q → ℝ) (i : ℕ) : Submodule ℝ (Q → ℝ) :=
  Submodule.span ℝ {u | ∃ w : List S, w.length ≤ i ∧ u = A.Mw w *ᵥ v}

omit [Fintype S] in
theorem chainL_mono (v : Q → ℝ) (i : ℕ) : A.chainL v i ≤ A.chainL v (i + 1) := by
  refine Submodule.span_mono ?_
  rintro u ⟨w, hw, rfl⟩
  exact ⟨w, by omega, rfl⟩

omit [Fintype S] in
/-- `M_b L_i ⊆ L_{i+1}`. -/
theorem Mw_mem_chainL (v : Q → ℝ) (i : ℕ) (b : S) {u : Q → ℝ} (hu : u ∈ A.chainL v i) :
    A.Mw [b] *ᵥ u ∈ A.chainL v (i + 1) := by
  have hle : A.chainL v i ≤ (A.chainL v (i + 1)).comap (A.Mw [b]).mulVecLin := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    refine Submodule.subset_span ⟨[b] ++ w, by simp; omega, ?_⟩
    rw [A.Mw_append]
  exact hle hu

omit [Fintype S] in
theorem chainL_step (v : Q → ℝ) (i : ℕ) (h : A.chainL v i = A.chainL v (i + 1)) :
    A.chainL v (i + 1) = A.chainL v (i + 2) := by
  refine le_antisymm (A.chainL_mono v (i + 1)) (Submodule.span_le.mpr ?_)
  rintro u ⟨w, hw, rfl⟩
  by_cases hshort : w.length ≤ i + 1
  · exact Submodule.subset_span ⟨w, hshort, rfl⟩
  · cases w with
    | nil => simp at hshort
    | cons b w' =>
      have hw' : w'.length ≤ i + 1 := by simp at hw; omega
      have hmem : A.Mw w' *ᵥ v ∈ A.chainL v i := by
        rw [h]; exact Submodule.subset_span ⟨w', hw', rfl⟩
      have h2 := A.Mw_mem_chainL v i b hmem
      rw [Matrix.mulVec_mulVec, ← A.Mw_append] at h2
      exact h2

omit [Fintype S] in
/-- Lemma 2.2(a), the bound `m ≤ n - 1`, from the chain `L_i`. -/
theorem cost_le_card_sub_one (β : Q → ℝ) (K : Finset Q) (hQ : wt β Finset.univ ≠ 0) (hK0 : wt β K ≠ 0)
    (hKQ : wt β K ≠ wt β Finset.univ) {m : ℕ} (hm : A.cost β K = m) : m ≤ Fintype.card Q - 1 := by
  obtain ⟨⟨w0, hw0, hw0l⟩, hshort⟩ := minLen_eq_coe hm
  set c := wt β K / wt β Finset.univ with hc
  let vK : Q → ℝ := ind K - c • (fun _ => 1)
  have hφ : ∀ w : List S, dotL β (A.Mw w *ᵥ vK) = wt β (A.pre K w) - wt β K := by
    intro w
    simp only [dotL, LinearMap.coe_mk, AddHom.coe_mk, vK, Matrix.mulVec_sub, Matrix.mulVec_smul,
      A.Mw_mulVec_one, A.Mw_mulVec_ind, dotProduct_sub, dotProduct_smul, dot_ind, smul_eq_mul]
    rw [← wt_univ, hc, div_mul_cancel₀ _ hQ]
  let H := LinearMap.ker (dotL β)
  have hin : ∀ i < m, A.chainL vK i ≤ H := by
    intro i hi
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw, rfl⟩
    have h := hshort w (by omega)
    simp only [ne_eq, not_not] at h
    simp only [SetLike.mem_coe, H, LinearMap.mem_ker, hφ, h, sub_self]
  have hout : ¬ A.chainL vK m ≤ H := by
    intro hle
    have hmem := hle (Submodule.subset_span ⟨w0, hw0l.le, rfl⟩)
    simp only [H, LinearMap.mem_ker, hφ] at hmem
    exact hw0 (sub_eq_zero.mp hmem)
  have hvK : vK ≠ 0 := by
    have hKne : K.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; rintro rfl; exact hK0 (wt_empty β)
    have hKnu : ∃ q, q ∉ K := by
      by_contra h; push Not at h; exact hKQ (by rw [Finset.eq_univ_iff_forall.mpr h])
    obtain ⟨q1, hq1⟩ := hKne
    obtain ⟨q2, hq2⟩ := hKnu
    intro h0
    have e1 := congrFun h0 q1
    have e2 := congrFun h0 q2
    simp [vK, ind, hq1, hq2] at e1 e2
    linarith
  have h0 : 1 ≤ Module.finrank ℝ (A.chainL vK 0) := by
    have hsub : (ℝ ∙ vK) ≤ A.chainL vK 0 := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span ⟨[], le_rfl, by simp⟩
    calc 1 = Module.finrank ℝ (ℝ ∙ vK) := (finrank_span_singleton hvK).symm
      _ ≤ Module.finrank ℝ (A.chainL vK 0) := Submodule.finrank_mono hsub
  have hexit := chain_exit_le (A.chainL vK) (A.chainL_mono vK) (A.chainL_step vK) H m hin hout h0
  have hH : Module.finrank ℝ H < Fintype.card Q := by
    have hne : H ≠ ⊤ := by
      intro htop
      have h1 : (fun _ => (1 : ℝ)) ∈ H := htop ▸ Submodule.mem_top
      simp only [H, LinearMap.mem_ker, dotL, LinearMap.coe_mk, AddHom.coe_mk] at h1
      exact hQ (by rw [wt_univ]; exact h1)
    have := Submodule.finrank_lt hne
    rwa [Module.finrank_fintype_fun_eq_card] at this
  omega

end Step

end Automaton

theorem lem_2_2_a_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → ∀ (β : Q → ℝ) (K : Finset Q), wt β Finset.univ ≠ 0 → wt β K ≠ 0 →
    wt β K ≠ wt β Finset.univ → ∃ m : ℕ, A.cost β K = m ∧ 1 ≤ m ∧ m ≤ Fintype.card Q - 1 := by
  intro hsync β K hQ hK0 hKQ
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (A.cost_ne_top hsync β K hK0 hKQ)
  exact ⟨m, hm.symm, A.one_le_of_cost_eq β K hm.symm, A.cost_le_card_sub_one β K hQ hK0 hKQ hm.symm⟩

/-- Lemma 2.2(b) without the hypotheses on `β(Q)`: they serve only part (a). -/
theorem raise_of_avg {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)
    (β : Q → ℝ) (K : Finset Q) (m : ℕ) (hm : A.cost β K = m) (p : S → ℝ) (hp : IsLetterWeights p)
    (havg : ∀ v : List S, v.length = m - 1 → wt β (A.pre K v) ≤ ∑ b, p b * wt β (A.pre (A.pre K v) [b])) :
    ∃ w : List S, w.length = m ∧ A.Raises β K w := by
  obtain ⟨⟨w0, hw0, hw0l⟩, hshort⟩ := minLen_eq_coe hm
  have hm1 := A.one_le_of_cost_eq β K hm
  obtain ⟨a, v, rfl⟩ : ∃ a v, w0 = a :: v := by
    cases w0 with
    | nil => simp at hw0l; omega
    | cons a v => exact ⟨a, v, rfl⟩
  have hvl : v.length = m - 1 := by simp at hw0l; omega
  set T := A.pre K v with hT
  have hTK : wt β T = wt β K := by
    have h := hshort v (by omega)
    simpa using h
  have hTa : wt β (A.pre T [a]) ≠ wt β T := by
    rw [hTK, hT, ← A.pre_append]
    simpa using hw0
  have hav := havg v hvl
  rw [← hT] at hav
  -- some letter raises
  obtain ⟨b, hb⟩ : ∃ b, wt β T < wt β (A.pre T [b]) := by
    by_contra hno
    push Not at hno
    have hle : ∑ b, p b * wt β (A.pre T [b]) ≤ ∑ b, p b * wt β T :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hno b) (hp.1 b).le
    rw [← Finset.sum_mul, hp.2, one_mul] at hle
    have heq : ∑ b, p b * (wt β T - wt β (A.pre T [b])) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]
      linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
      mul_nonneg (hp.1 b).le (sub_nonneg.mpr (hno b))).mp heq a (Finset.mem_univ a)
    rcases mul_eq_zero.mp hz with h | h
    · exact (hp.1 a).ne' h
    · exact hTa (sub_eq_zero.mp h).symm
  refine ⟨b :: v, by simp; omega, ?_⟩
  show wt β K < wt β (A.pre K ([b] ++ v))
  rw [A.pre_append, ← hT, ← hTK]
  exact hb

theorem lem_2_2_b_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → ∀ (β : Q → ℝ) (K : Finset Q), wt β Finset.univ ≠ 0 → wt β K ≠ 0 →
    wt β K ≠ wt β Finset.univ → ∀ (m : ℕ), A.cost β K = m → ∀ p : S → ℝ, IsLetterWeights p →
    (∀ v : List S, v.length = m - 1 → wt β (A.pre K v) ≤ ∑ b, p b * wt β (A.pre (A.pre K v) [b])) →
    ∃ w : List S, w.length = m ∧ A.Raises β K w := by
  intro _ β K _ _ _ m hm p hp havg
  exact raise_of_avg A β K m hm p hp havg

/-- For a stationary vector, a word that raises `α` exists at the cost, and no shorter word raises. -/
theorem raises_at_cost {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)
    (p : S → ℝ) (α : Q → ℝ) (hp : IsLetterWeights p) (hα : A.IsStationary p α) (K : Finset Q) (m : ℕ)
    (hm : A.cost α K = m) : (∃ w : List S, w.length = m ∧ A.Raises α K w) ∧ minLen (A.Raises α K) = A.cost α K := by
  have hraise := raise_of_avg A α K m hm p hp (fun v _ => by
    rw [(eq_2_1_core A p α hα (A.pre K v)).1, (eq_2_1_core A p α hα (A.pre K v)).2])
  refine ⟨hraise, le_antisymm ?_ (minLen_mono fun w hw => ne_of_gt hw)⟩
  obtain ⟨w, hwl, hw⟩ := hraise
  rw [hm, ← hwl]
  exact minLen_le_length hw

theorem lem_2_2_last_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → ∀ (p : S → ℝ) (α : Q → ℝ), IsLetterWeights p → A.IsStationary p α →
    wt α Finset.univ ≠ 0 → ∀ K : Finset Q, wt α K ≠ 0 → wt α K ≠ wt α Finset.univ →
    (∃ w : List S, w.length ≤ Fintype.card Q - 1 ∧ A.Raises α K w) ∧ minLen (A.Raises α K) = A.cost α K := by
  intro hsync p α hp hα hQ K hK0 hKQ
  obtain ⟨m, hm, -, hmn⟩ := lem_2_2_a_core A hsync α K hQ hK0 hKQ
  obtain ⟨⟨w, hwl, hw⟩, hmin⟩ := raises_at_cost A p α hp hα K m hm
  exact ⟨⟨w, hwl ▸ hmn, hw⟩, hmin⟩

/-- For a positive vector, a nonempty proper set has weight strictly between `0` and `α(Q)`. -/
theorem wt_pos_proper {Q : Type*} [Fintype Q] [DecidableEq Q] (α : Q → ℝ) (hpos : ∀ q, 0 < α q)
    (K : Finset Q) (hK : K.Nonempty) (hKu : K ≠ Finset.univ) :
    0 < wt α K ∧ wt α K < wt α Finset.univ := by
  refine ⟨Finset.sum_pos (fun q _ => hpos q) hK, ?_⟩
  obtain ⟨q, hq⟩ : ∃ q, q ∉ K := by
    by_contra h; push Not at h; exact hKu (Finset.eq_univ_iff_forall.mpr h)
  exact Finset.sum_lt_sum_of_subset (Finset.subset_univ K) (Finset.mem_univ q) hq (hpos q)
    (fun r _ _ => (hpos r).le)

theorem sec2_cost_bounds_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → ∀ α : Q → ℝ, (∀ q, 0 < α q) → ∀ K : Finset Q, K.Nonempty →
    K ≠ Finset.univ → (∃ m : ℕ, A.cost α K = m ∧ 1 ≤ m ∧ m ≤ Fintype.card Q - 1) ∧
    ∀ p : S → ℝ, IsLetterWeights p → A.IsStationary p α → ∃ w : List S, (w.length : ℕ∞) = A.cost α K ∧ A.Raises α K w := by
  intro hsync α hpos K hK hKu
  obtain ⟨h0, h1⟩ := wt_pos_proper α hpos K hK hKu
  have hQ : wt α Finset.univ ≠ 0 := (h0.trans h1).ne'
  obtain ⟨m, hm, hm1, hmn⟩ := lem_2_2_a_core A hsync α K hQ h0.ne' h1.ne
  refine ⟨⟨m, hm, hm1, hmn⟩, fun p hp hα => ?_⟩
  obtain ⟨⟨w, hwl, hw⟩, -⟩ := raises_at_cost A p α hp hα K m hm
  exact ⟨w, by rw [hm, hwl], hw⟩

/-! ### Equation (2.2) and the tier lemma 2.4 -/

namespace Automaton

section Tier

variable {Q S : Type*} [Fintype Q] [DecidableEq Q] (A : Automaton Q S)

/-- The telescope identity (2.2), first part. -/
theorem telescope (α : Q → ℝ) (w : List S) :
    Matrix.vecMul α (A.Mw w) - α =
      ∑ i : Fin w.length, Matrix.vecMul (A.delta α (w.get i)) (A.Mw (w.drop (i.1 + 1))) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    show _ = ∑ i : Fin (w.length + 1), Matrix.vecMul (A.delta α ((c :: w).get i))
      (A.Mw ((c :: w).drop (i.1 + 1)))
    rw [Fin.sum_univ_succ]
    have h1 : A.Mw (c :: w) = A.Mw [c] * A.Mw w := A.Mw_append [c] w
    have h2 : Matrix.vecMul α (A.Mw [c]) = A.delta α c + α := by simp [delta]
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, zero_add, List.drop_succ_cons,
      List.drop_zero, Fin.val_succ, List.getElem_cons_succ]
    simp only [List.get_eq_getElem] at ih
    rw [← ih, h1, ← Matrix.vecMul_vecMul, h2, Matrix.add_vecMul]
    abel

/-- `δ_c 1 = 0`. -/
theorem delta_dot_one (α : Q → ℝ) (c : S) : A.delta α c ⬝ᵥ (fun _ => (1 : ℝ)) = 0 := by
  rw [delta, sub_dotProduct, ← Matrix.dotProduct_mulVec, A.Mw_mulVec_one, sub_self]

omit [DecidableEq Q] in
/-- The linear functional `λ ↦ λ ⬝ x`, as a kernel test for spans. -/
theorem mem_ker_dotL_iff (x lam : Q → ℝ) : lam ∈ LinearMap.ker (dotL x) ↔ lam ⬝ᵥ x = 0 := by
  simp [dotL, dotProduct_comm]

/-- Every vector of `D_k` has entry sum `0` (tex:340). -/
theorem Dk_dot_one (α : Q → ℝ) (k : ℕ) : ∀ lam ∈ A.Dk α k, lam ⬝ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hle : A.Dk α k ≤ LinearMap.ker (dotL (fun _ => (1 : ℝ))) := by
    refine Submodule.span_le.mpr ?_
    rintro lam ⟨c, v, -, rfl⟩
    rw [SetLike.mem_coe, mem_ker_dotL_iff, ← Matrix.dotProduct_mulVec, A.Mw_mulVec_one, A.delta_dot_one]
  exact fun lam hlam => (mem_ker_dotL_iff _ _).mp (hle hlam)

/-- A generator `δ_c M_v` paired with `𝟙_T` is a difference of two preimage weights. -/
theorem delta_Mw_dot_ind (α : Q → ℝ) (c : S) (v : List S) (T : Finset Q) :
    Matrix.vecMul (A.delta α c) (A.Mw v) ⬝ᵥ ind T = wt α (A.pre T (c :: v)) - wt α (A.pre T v) := by
  rw [delta, Matrix.sub_vecMul, sub_dotProduct, Matrix.vecMul_vecMul, ← A.Mw_append, List.singleton_append,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, A.wt_pre_eq_dot, A.wt_pre_eq_dot]

omit [DecidableEq Q] in
/-- The cost is at least one. -/
theorem one_le_cost [DecidableEq Q] (α : Q → ℝ) (T : Finset Q) : (1 : ℕ∞) ≤ A.cost α T := by
  refine le_minLen_iff.mpr fun w hw => ?_
  cases w with
  | nil => simp at hw
  | cons c w => simp

theorem Dk_mono (α : Q → ℝ) (k : ℕ) : A.Dk α k ≤ A.Dk α (k + 1) := by
  refine Submodule.span_mono ?_
  rintro lam ⟨c, v, hv, rfl⟩
  exact ⟨c, v, by omega, rfl⟩

/-- `D_k M_b ⊆ D_{k+1}`. -/
theorem vecMul_mem_Dk (α : Q → ℝ) (k : ℕ) (b : S) {lam : Q → ℝ} (h : lam ∈ A.Dk α k) :
    Matrix.vecMul lam (A.Mw [b]) ∈ A.Dk α (k + 1) := by
  have hle : A.Dk α k ≤ (A.Dk α (k + 1)).comap (A.Mw [b]).vecMulLinear := by
    refine Submodule.span_le.mpr ?_
    rintro lam ⟨c, v, hv, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul]
    refine Submodule.subset_span ⟨c, v ++ [b], by simp; omega, ?_⟩
    rw [A.Mw_append]
  exact hle h

theorem Dk_step (α : Q → ℝ) (k : ℕ) (h : A.Dk α k = A.Dk α (k + 1)) : A.Dk α (k + 1) = A.Dk α (k + 2) := by
  refine le_antisymm (A.Dk_mono α (k + 1)) (Submodule.span_le.mpr ?_)
  rintro lam ⟨c, v, hv, rfl⟩
  by_cases hshort : v.length + 1 ≤ k + 1
  · exact Submodule.subset_span ⟨c, v, hshort, rfl⟩
  obtain ⟨v', b, rfl, hv'⟩ := exists_concat_of_length v (i := k) (by omega)
  have hmem : Matrix.vecMul (A.delta α c) (A.Mw v') ∈ A.Dk α k := by
    rw [h]; exact Submodule.subset_span ⟨c, v', by omega, rfl⟩
  have h2 := A.vecMul_mem_Dk α k b hmem
  rwa [Matrix.vecMul_vecMul, ← A.Mw_append] at h2

/-- Every term of the telescope (2.2) for a word of length at most `k` lies in `D_k`. -/
theorem telescope_mem_Dk (α : Q → ℝ) (w : List S) (k : ℕ) (hw : w.length ≤ k) :
    Matrix.vecMul α (A.Mw w) - α ∈ A.Dk α k := by
  rw [A.telescope]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨w.get i, w.drop (i.1 + 1), ?_, rfl⟩
  simp only [List.length_drop]
  omega

/-- The vectors orthogonal to a subspace `D` (for the dot product). -/
noncomputable def perp (D : Submodule ℝ (Q → ℝ)) : Submodule ℝ (Q → ℝ) :=
  (D.map (dotProductEquiv ℝ Q).toLinearMap).dualCoannihilator

omit [DecidableEq Q] in
theorem mem_perp [DecidableEq Q] (D : Submodule ℝ (Q → ℝ)) (ξ : Q → ℝ) :
    ξ ∈ perp D ↔ ∀ lam ∈ D, lam ⬝ᵥ ξ = 0 := by
  simp only [perp, Submodule.mem_dualCoannihilator, Submodule.mem_map_equiv]
  constructor
  · intro h lam hlam
    have h1 := h (dotProductEquiv ℝ Q lam) (by simpa using hlam)
    simpa using h1
  · intro h φ hφ
    have h1 := h _ hφ
    calc φ ξ = (dotProductEquiv ℝ Q ((dotProductEquiv ℝ Q).symm φ)) ξ := by
          rw [LinearEquiv.apply_symm_apply]
      _ = (dotProductEquiv ℝ Q).symm φ ⬝ᵥ ξ := rfl
      _ = 0 := h1

omit [DecidableEq Q] in
theorem finrank_add_finrank_perp [DecidableEq Q] (D : Submodule ℝ (Q → ℝ)) :
    Module.finrank ℝ D + Module.finrank ℝ (perp D) = Fintype.card Q := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (D.map (dotProductEquiv ℝ Q).toLinearMap)
  rw [LinearEquiv.finrank_map_eq, Module.finrank_fintype_fun_eq_card] at h
  exact h

end Tier

end Automaton

theorem eq_2_2_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (α : Q → ℝ) (w : List S), Matrix.vecMul α (A.Mw w) - α =
    ∑ i : Fin w.length, Matrix.vecMul (A.delta α (w.get i)) (A.Mw (w.drop (i.1 + 1))) ∧
    ∀ c : S, A.delta α c ⬝ᵥ (fun _ => (1 : ℝ)) = 0 :=
  fun α w => ⟨A.telescope α w, A.delta_dot_one α⟩

theorem lem_2_4_i_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ (α : Q → ℝ) (T : Finset Q) (k : ℕ),
    ((k + 1 : ℕ) : ℕ∞) ≤ A.cost α T ↔ ∀ lam ∈ A.Dk α k, lam ⬝ᵥ ind T = 0 := by
  intro α T k
  constructor
  · intro hcost
    have hkeep : ∀ v : List S, v.length ≤ k → wt α (A.pre T v) = wt α T := by
      intro v hv
      by_contra hne
      have h2 : ((v.length : ℕ) : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_of_le hv
      exact absurd (lt_of_le_of_lt (minLen_le_length hne) h2) (not_lt.mpr hcost)
    have hle : A.Dk α k ≤ LinearMap.ker (dotL (ind T)) := by
      refine Submodule.span_le.mpr ?_
      rintro lam ⟨c, v, hv, rfl⟩
      rw [SetLike.mem_coe, mem_ker_dotL_iff, A.delta_Mw_dot_ind, hkeep (c :: v) (by simp; omega),
        hkeep v (by omega), sub_self]
    exact fun lam hlam => (mem_ker_dotL_iff _ _).mp (hle hlam)
  · intro hD
    refine le_minLen_iff.mpr fun w hw => ?_
    by_contra hlt
    push Not at hlt
    have hwk : w.length ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
    have h1 := hD _ (A.telescope_mem_Dk α w k hwk)
    rw [sub_dotProduct, ← Matrix.dotProduct_mulVec, A.wt_pre_eq_dot, dot_ind, sub_eq_zero] at h1
    exact hw h1

/-- `D_1 ≠ 0`: some `δ_c` is nonzero (tex:348-350). -/
theorem Dk_one_ne_bot {Q S : Type*} [Fintype Q] [DecidableEq Q] (A : Automaton Q S) (hsync : A.Synchronizing)
    (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (hn : 2 ≤ Fintype.card Q) : 1 ≤ Module.finrank ℝ (A.Dk α 1) := by
  obtain ⟨u, r, hr⟩ := hsync
  have hex : ∃ c : S, A.delta α c ≠ 0 := by
    by_contra hall
    push Not at hall
    have hfix : Matrix.vecMul α (A.Mw u) = α := by
      rw [← sub_eq_zero, A.telescope]
      exact Finset.sum_eq_zero fun i _ => by rw [hall, Matrix.zero_vecMul]
    obtain ⟨r', hr'⟩ : ∃ r', r' ≠ r := by
      by_contra h
      push Not at h
      have : Fintype.card Q ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (h a).trans (h b).symm
      omega
    have h1 := congrFun hfix r'
    rw [vecMul_Mw] at h1
    simp only [hr, hr'.symm, ↓reduceIte, mul_zero, Finset.sum_const_zero] at h1
    exact (hpos r').ne' h1.symm
  obtain ⟨c, hc⟩ := hex
  have hmem : A.delta α c ∈ A.Dk α 1 :=
    Submodule.subset_span ⟨c, [], by simp, by simp [Matrix.vecMul_one]⟩
  calc 1 = Module.finrank ℝ (ℝ ∙ A.delta α c) := (finrank_span_singleton hc).symm
    _ ≤ Module.finrank ℝ (A.Dk α 1) :=
      Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem)

/-- For a synchronizing strongly connected automaton, every state is the image of `Q` under some word. -/
theorem exists_word_image {Q S : Type*} [Fintype Q] [DecidableEq Q] (A : Automaton Q S)
    (hsync : A.Synchronizing) (hsc : A.StronglyConnected) (r : Q) : ∃ w : List S, ∀ q, A.act q w = r := by
  classical
  obtain ⟨u, r0, hr0⟩ := hsync
  let Rall : Finset Q := Finset.univ.filter (fun q => ∃ v : List S, A.act r0 v = q)
  have hclosed : A.IsClosed Rall := by
    intro q hq b
    simp only [Rall, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    obtain ⟨v, rfl⟩ := hq
    exact ⟨v ++ [b], A.act_concat r0 v b⟩
  have hr : r ∈ Rall := by
    rcases hsc Rall hclosed with h | h
    · have hx : r0 ∈ Rall := by
        simp only [Rall, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨[], rfl⟩
      rw [h] at hx
      simp at hx
    · rw [h]; exact Finset.mem_univ r
  simp only [Rall, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  obtain ⟨v, hv⟩ := hr
  exact ⟨u ++ v, fun q => by rw [A.act_append, hr0, hv]⟩

/-- The final value of the chain `D_k` has dimension at least `n - 1` (tex:352-355). -/
theorem Dk_final {Q S : Type*} [Fintype Q] [DecidableEq Q] (A : Automaton Q S) (hsync : A.Synchronizing)
    (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) :
    ∃ K, Fintype.card Q - 1 ≤ Module.finrank ℝ (A.Dk α K) := by
  by_cases hQne : Nonempty Q
  swap
  · refine ⟨0, ?_⟩
    have : Fintype.card Q = 0 := Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hQne)
    omega
  have hmono : Monotone (A.Dk α) := monotone_nat_of_le_succ (A.Dk_mono α)
  obtain ⟨K, hK⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance ⟨A.Dk α, hmono⟩
  refine ⟨K, ?_⟩
  set D := A.Dk α K
  -- every ξ ⊥ D is constant
  have hconst : ∀ ξ ∈ Automaton.perp D, ∀ r r' : Q, ξ r = ξ r' := by
    intro ξ hξ
    rw [Automaton.mem_perp] at hξ
    have hinv : ∀ w : List S, Matrix.vecMul α (A.Mw w) ⬝ᵥ ξ = α ⬝ᵥ ξ := by
      intro w
      have hmem : Matrix.vecMul α (A.Mw w) - α ∈ D := by
        have h1 := A.telescope_mem_Dk α w (max w.length K) (le_max_left _ _)
        have h2 : A.Dk α (max w.length K) = D := (hK (max w.length K) (le_max_right _ _)).symm
        rwa [h2] at h1
      have h3 := hξ _ hmem
      rwa [sub_dotProduct, sub_eq_zero] at h3
    have hval : ∀ r, wt α Finset.univ * ξ r = α ⬝ᵥ ξ := by
      intro r
      obtain ⟨w, hw⟩ := exists_word_image A hsync hsc r
      rw [← hinv w]
      have hrow : Matrix.vecMul α (A.Mw w) = fun r' => if r' = r then wt α Finset.univ else 0 := by
        funext r'
        rw [vecMul_Mw]
        by_cases h : r' = r
        · subst h; simp [hw, wt]
        · simp [hw, Ne.symm h, h]
      rw [hrow, dotProduct]
      simp [ite_mul]
    have hQpos : 0 < wt α Finset.univ := Finset.sum_pos (fun q _ => hpos q) Finset.univ_nonempty
    intro r r'
    have e1 := hval r
    have e2 := hval r'
    exact mul_left_cancel₀ hQpos.ne' (e1.trans e2.symm)
  -- so perp D ⊆ span {1}, of dimension at most 1
  have hsub : Automaton.perp D ≤ ℝ ∙ (fun _ : Q => (1 : ℝ)) := by
    intro ξ hξ
    obtain ⟨q0⟩ := hQne
    rw [Submodule.mem_span_singleton]
    exact ⟨ξ q0, funext fun r => by simp [hconst ξ hξ q0 r]⟩
  have hle := Submodule.finrank_mono hsub
  have hone : (fun _ : Q => (1 : ℝ)) ≠ 0 := by
    obtain ⟨q0⟩ := hQne
    intro h
    exact one_ne_zero (congrFun h q0)
  have h1 : Module.finrank ℝ (ℝ ∙ (fun _ : Q => (1 : ℝ))) ≤ 1 := (finrank_span_singleton hone).le
  have hsum := Automaton.finrank_add_finrank_perp D
  omega

theorem lem_2_4_ii_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → A.StronglyConnected → ∀ α : Q → ℝ, (∀ q, 0 < α q) → ∀ k : ℕ,
    min k (Fintype.card Q - 1) ≤ Module.finrank ℝ (A.Dk α k) := by
  intro hsync hsc α hpos k
  by_cases hn : 2 ≤ Fintype.card Q
  · exact chain_finrank_ge (A.Dk α) (A.Dk_mono α) (A.Dk_step α) (Dk_one_ne_bot A hsync α hpos hn)
      (Fintype.card Q - 1) (Dk_final A hsync hsc α hpos) k
  · have : Fintype.card Q - 1 = 0 := by omega
    rw [this, min_zero]
    exact Nat.zero_le _

theorem lem_2_4_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → A.StronglyConnected → ∀ α : Q → ℝ, (∀ q, 0 < α q) → ∀ j : ℕ, 2 ≤ j →
    j ≤ Fintype.card Q → (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      ((Fintype.card Q - j + 1 : ℕ) : ℕ∞) ≤ A.cost α T)).card ≤ 2 ^ j - 2 := by
  intro hsync hsc α hpos j hj2 hjn
  set F := Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      ((Fintype.card Q - j + 1 : ℕ) : ℕ∞) ≤ A.cost α T) with hF
  set k := Fintype.card Q - j with hk
  have hdimD := lem_2_4_ii_core A hsync hsc α hpos k
  have hsum := Automaton.finrank_add_finrank_perp (A.Dk α k)
  have hV : Module.finrank ℝ (Automaton.perp (A.Dk α k)) ≤ j := by
    have : min k (Fintype.card Q - 1) = k := min_eq_left (by omega)
    omega
  have hcount := indicator_card_le (Automaton.perp (A.Dk α k))
  -- every set in F, and ∅ and Q, has its indicator vector in perp D_k
  have hindV : ∀ T : Finset Q, (∀ lam ∈ A.Dk α k, lam ⬝ᵥ ind T = 0) →
      (fun i => if i ∈ T then (1 : ℝ) else 0) ∈ Automaton.perp (A.Dk α k) :=
    fun T hT => (Automaton.mem_perp _ _).mpr hT
  have hle : (F ∪ {∅, Finset.univ}).card ≤ 2 ^ Module.finrank ℝ (Automaton.perp (A.Dk α k)) := by
    classical
    refine le_trans (Finset.card_le_card ?_) hcount
    intro T hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hT with hTF | hT2
    · simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hTF
      exact hindV T ((lem_2_4_i_core A α T k).mp (by rw [hk]; exact hTF.2.2))
    · rcases Finset.mem_insert.mp hT2 with rfl | hT3
      · exact hindV ∅ fun lam _ => by rw [ind_empty, dotProduct_zero]
      · rw [Finset.mem_singleton] at hT3
        subst hT3
        exact hindV _ fun lam hlam => by rw [ind_univ]; exact A.Dk_dot_one α k lam hlam
  have hne : (∅ : Finset Q) ≠ Finset.univ := by
    intro h
    have : Fintype.card Q = 0 := by rw [← Finset.card_univ, ← h, Finset.card_empty]
    omega
  have hdisj : Disjoint F {∅, Finset.univ} := by
    rw [Finset.disjoint_left]
    intro T hTF hT2
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hTF
    rcases Finset.mem_insert.mp hT2 with rfl | hT3
    · exact Finset.not_nonempty_empty hTF.1
    · exact hTF.2.1 (Finset.mem_singleton.mp hT3)
  have hcard2 : ({∅, Finset.univ} : Finset (Finset Q)).card = 2 := Finset.card_pair hne
  rw [Finset.card_union_of_disjoint hdisj, hcard2] at hle
  have hpow : 2 ^ Module.finrank ℝ (Automaton.perp (A.Dk α k)) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hV
  omega

/-- No nonempty proper set exists when `n ≤ 1`. -/
theorem filter_proper_empty {Q : Type*} [Fintype Q] [DecidableEq Q] (hn : Fintype.card Q ≤ 1)
    (P : Finset Q → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧ P T)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro T - ⟨⟨q, hq⟩, hTu, -⟩
  apply hTu
  rw [Finset.eq_univ_iff_forall]
  intro r
  have : r = q := Fintype.card_le_one_iff.mp hn r q
  rw [this]; exact hq

theorem lem_2_4_two_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → A.StronglyConnected → ∀ α : Q → ℝ, (∀ q, 0 < α q) →
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      A.cost α T = ((Fintype.card Q - 1 : ℕ) : ℕ∞))).card ≤ 2 := by
  intro hsync hsc α hpos
  by_cases hn : 2 ≤ Fintype.card Q
  · have h := lem_2_4_core A hsync hsc α hpos 2 le_rfl hn
    refine le_trans (Finset.card_le_card ?_) h
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    refine ⟨hT.1, hT.2.1, ?_⟩
    rw [hT.2.2]
    exact_mod_cast le_of_eq (by omega)
  · rw [filter_proper_empty (by omega)]
    norm_num

theorem lem_2_4_six_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    A.Synchronizing → A.StronglyConnected → ∀ α : Q → ℝ, (∀ q, 0 < α q) →
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      ((Fintype.card Q - 2 : ℕ) : ℕ∞) ≤ A.cost α T)).card ≤ 6 := by
  intro hsync hsc α hpos
  by_cases hn3 : 3 ≤ Fintype.card Q
  · have h := lem_2_4_core A hsync hsc α hpos 3 (by norm_num) hn3
    refine le_trans (Finset.card_le_card ?_) (le_trans h (by norm_num))
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    refine ⟨hT.1, hT.2.1, ?_⟩
    have he : Fintype.card Q - 3 + 1 = Fintype.card Q - 2 := by omega
    rw [he]
    exact hT.2.2
  · by_cases hn2 : 2 ≤ Fintype.card Q
    · have h := lem_2_4_core A hsync hsc α hpos 2 le_rfl hn2
      refine le_trans (Finset.card_le_card ?_) (le_trans h (by norm_num))
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      refine ⟨hT.1, hT.2.1, ?_⟩
      have he : Fintype.card Q - 2 + 1 = 1 := by omega
      rw [he]
      exact_mod_cast A.one_le_cost α T
    · rw [filter_proper_empty (by omega)]
      norm_num

theorem rem_2_5_direct_core {Q S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) :
    ∀ α : Q → ℝ, wt α Finset.univ ≠ 0 → ∀ k : ℕ,
    A.Uk α (k + 1) = (ℝ ∙ α) ⊔ A.Dk α k ∧ Disjoint (ℝ ∙ α) (A.Dk α k) := by
  intro α hQ k
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro lam ⟨u, hu, rfl⟩
    have h1 := A.telescope_mem_Dk α u k (by omega)
    have h2 : Matrix.vecMul α (A.Mw u) = α + (Matrix.vecMul α (A.Mw u) - α) := by abel
    rw [SetLike.mem_coe, h2]
    exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self α) h1
  · refine sup_le ?_ (Submodule.span_le.mpr ?_)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span ⟨[], by simp, by simp [Matrix.vecMul_one]⟩
    · rintro lam ⟨c, v, hv, rfl⟩
      have e : Matrix.vecMul (A.delta α c) (A.Mw v) =
          Matrix.vecMul α (A.Mw (c :: v)) - Matrix.vecMul α (A.Mw v) := by
        rw [Automaton.delta, Matrix.sub_vecMul, Matrix.vecMul_vecMul, ← A.Mw_append, List.singleton_append]
      rw [SetLike.mem_coe, e]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨c :: v, by simp; omega, rfl⟩)
        (Submodule.subset_span ⟨v, by omega, rfl⟩)
  · rw [Submodule.disjoint_def]
    intro x hx hxD
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have h1 := A.Dk_dot_one α k _ hxD
    rw [smul_dotProduct, ← wt_univ, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h, zero_smul]
    · exact absurd h hQ

end CernyQE
