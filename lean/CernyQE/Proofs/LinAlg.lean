/-
CernyQE/Proofs/LinAlg.lean — linear-algebra lemmas for the proofs of Lemmas 2.2, 2.4 and 5.5.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib

namespace CernyQE

/-! ### Chains that stop growing stay constant -/

/-- A sequence whose one-step equality propagates is constant from the first repeat on. -/
theorem seq_const_of_eq {β : Type*} (L : ℕ → β)
    (hstep : ∀ i, L i = L (i + 1) → L (i + 1) = L (i + 2)) {i : ℕ} (h : L i = L (i + 1)) :
    ∀ j, i ≤ j → L j = L i := by
  have key : ∀ j, i ≤ j → L j = L (j + 1) ∧ L j = L i := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact ⟨h, rfl⟩
    | succ j _ ih => exact ⟨hstep j ih.1, ih.1.symm.trans ih.2⟩
  exact fun j hj => (key j hj).2

/-- L3, first part (proof of Lemma 2.2(a)): a chain of subspaces that stops growing stays constant. -/
theorem chain_const_of_eq {W : Type*} [AddCommGroup W] [Module ℝ W] (L : ℕ → Submodule ℝ W)
    (hstep : ∀ i, L i = L (i + 1) → L (i + 1) = L (i + 2)) {i : ℕ} (h : L i = L (i + 1)) :
    ∀ j, i ≤ j → L j = L i :=
  seq_const_of_eq L hstep h

/-- L3, second part (proof of Lemma 2.2(a)): a growing chain that first leaves `H` at step `m`, starting from a
subspace of dimension at least one, has `m ≤ dim H`. -/
theorem chain_exit_le {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (L : ℕ → Submodule ℝ W) (hmono : ∀ i, L i ≤ L (i + 1))
    (hstep : ∀ i, L i = L (i + 1) → L (i + 1) = L (i + 2))
    (H : Submodule ℝ W) (m : ℕ) (hin : ∀ i < m, L i ≤ H) (hout : ¬ L m ≤ H)
    (h0 : 1 ≤ Module.finrank ℝ (L 0)) : m ≤ Module.finrank ℝ H := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  have hstrict : ∀ i, i + 1 < m → L i < L (i + 1) := by
    intro i hi
    refine lt_of_le_of_ne (hmono i) (fun heq => hout ?_)
    rw [seq_const_of_eq L hstep heq m (by omega)]
    exact hin i (by omega)
  have hgrow : ∀ i, i < m → i + 1 ≤ Module.finrank ℝ (L i) := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have h1 := ih (by omega)
      have h2 := Submodule.finrank_lt_finrank_of_lt (hstrict i hi)
      omega
  have h3 := hgrow (m - 1) (by omega)
  have h4 := Submodule.finrank_mono (hin (m - 1) (by omega))
  omega

/-- L4 (proof of Lemma 2.4(ii)): a growing chain with `dim L 1 ≥ 1` that reaches dimension `N` has
`dim L k ≥ min k N` for every `k`. -/
theorem chain_finrank_ge {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (L : ℕ → Submodule ℝ W) (hmono : ∀ i, L i ≤ L (i + 1))
    (hstep : ∀ i, L i = L (i + 1) → L (i + 1) = L (i + 2))
    (h1 : 1 ≤ Module.finrank ℝ (L 1)) (N : ℕ) (hN : ∃ K, N ≤ Module.finrank ℝ (L K)) :
    ∀ k, min k N ≤ Module.finrank ℝ (L k) := by
  obtain ⟨K, hK⟩ := hN
  have hmono' : Monotone L := monotone_nat_of_le_succ hmono
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact le_trans (min_le_left 1 N) h1
    by_cases heq : L k = L (k + 1)
    · have hc := seq_const_of_eq L hstep heq
      have hKk : N ≤ Module.finrank ℝ (L k) := by
        have h4 : L K ≤ L (max K k) := hmono' (le_max_left _ _)
        rw [hc (max K k) (le_max_right _ _)] at h4
        exact le_trans hK (Submodule.finrank_mono h4)
      rw [← heq]
      exact le_trans (min_le_right _ _) hKk
    · have h5 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono k) heq)
      omega

/-- L5 (orbit lemma 2.3, joint orbit 5.10): a growing chain of finite sets that still grows at step `f` grows by
at least one element at each of the steps before. -/
theorem finset_chain_card_ge {α : Type*} [DecidableEq α] (R : ℕ → Finset α) (hmono : ∀ i, R i ⊆ R (i + 1))
    (hstep : ∀ i, R i = R (i + 1) → R (i + 1) = R (i + 2)) (f : ℕ) (hstrict : R (f - 1) ≠ R f) :
    ∀ i, i ≤ f - 1 → (R 0).card + i ≤ (R i).card := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := ih (by omega)
    have hne : R i ≠ R (i + 1) := by
      intro heq
      have hc := seq_const_of_eq R hstep heq
      exact hstrict ((hc (f - 1) (by omega)).trans (hc f (by omega)).symm)
    have h2 := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hmono i, hne⟩)
    omega

/-! ### Counting 0/1 vectors in a subspace (proof of Lemma 2.4(iii)) -/

/-- Some set of at most `dim V` coordinates determines every vector of `V`. -/
theorem exists_coords_injOn {ι : Type*} [Fintype ι] (V : Submodule ℝ (ι → ℝ)) :
    ∃ J : Finset ι, J.card ≤ Module.finrank ℝ V ∧
      ∀ ξ ∈ V, ∀ ξ' ∈ V, (∀ j ∈ J, ξ j = ξ' j) → ξ = ξ' := by
  classical
  let f : ι → Module.Dual ℝ V := fun i => (LinearMap.proj i).comp V.subtype
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ f
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ha, Finset.card_univ]
    exact hli.fintype_card_le_finrank.trans Subspace.dual_finrank_eq.le
  · intro ξ hξ ξ' hξ' hJ
    let v : V := ⟨ξ - ξ', V.sub_mem hξ hξ'⟩
    have hle : Submodule.span ℝ (Set.range (f ∘ a)) ≤ LinearMap.ker (Module.Dual.eval ℝ V v) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hk := hJ (a k) (Finset.mem_image_of_mem a (Finset.mem_univ k))
      simp [f, v, hk]
    rw [hspan] at hle
    funext i
    have hi := hle (Submodule.subset_span ⟨i, rfl⟩)
    simp [f, v] at hi
    linarith

/-- Two numbers in `{0, 1}` that are equal to `1` together are equal. -/
theorem zeroOne_eq_of_iff {r s : ℝ} (hr : r = 0 ∨ r = 1) (hs : s = 0 ∨ s = 1) (h : r = 1 ↔ s = 1) :
    r = s := by
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> first | rfl | norm_num at h

/-- L1 (Lemma 2.4 proof (iii)): a subspace of dimension `ρ` contains at most `2 ^ ρ` vectors with entries in
`{0, 1}`. -/
theorem zeroOne_ncard_le {ι : Type*} [Fintype ι] (V : Submodule ℝ (ι → ℝ)) :
    {ξ : ι → ℝ | ξ ∈ V ∧ ∀ i, ξ i = 0 ∨ ξ i = 1}.ncard ≤ 2 ^ Module.finrank ℝ V := by
  classical
  obtain ⟨J, hJcard, hJinj⟩ := exists_coords_injOn V
  let g : (ι → ℝ) → (J → Bool) := fun ξ j => decide (ξ j.1 = 1)
  calc {ξ : ι → ℝ | ξ ∈ V ∧ ∀ i, ξ i = 0 ∨ ξ i = 1}.ncard
      ≤ (Set.univ : Set (J → Bool)).ncard := by
        refine Set.ncard_le_ncard_of_injOn g (fun _ _ => Set.mem_univ _) ?_
        rintro ξ ⟨hξV, hξ01⟩ ξ' ⟨hξ'V, hξ'01⟩ hg
        refine hJinj ξ hξV ξ' hξ'V (fun j hj => ?_)
        have h := congrFun hg ⟨j, hj⟩
        simp only [g, decide_eq_decide] at h
        exact zeroOne_eq_of_iff (hξ01 j) (hξ'01 j) h
    _ = 2 ^ J.card := by simp [Set.ncard_univ, Nat.card_eq_fintype_card]
    _ ≤ 2 ^ Module.finrank ℝ V := Nat.pow_le_pow_right (by norm_num) hJcard

open Classical in
/-- L2 (the form Lemma 2.4 uses): a subspace of dimension `ρ` contains the indicator vectors of at most `2 ^ ρ`
sets. -/
theorem indicator_card_le {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Submodule ℝ (ι → ℝ)) :
    (Finset.univ.filter (fun S : Finset ι => (fun i => if i ∈ S then (1 : ℝ) else 0) ∈ V)).card
      ≤ 2 ^ Module.finrank ℝ V := by
  obtain ⟨J, hJcard, hJinj⟩ := exists_coords_injOn V
  let g : Finset ι → (J → Bool) := fun S j => decide (j.1 ∈ S)
  calc _ ≤ (Finset.univ : Finset (J → Bool)).card := by
        refine Finset.card_le_card_of_injOn g (by intro _ _; simp) ?_
        intro S hS S' hS' hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS hS'
        have hind := hJinj _ hS _ hS' (fun j hj => by
          have h := congrFun hg ⟨j, hj⟩
          simp only [g, decide_eq_decide] at h
          by_cases hjS : j ∈ S
          · simp [hjS, h.mp hjS]
          · have hjS' : j ∉ S' := fun h' => hjS (h.mpr h')
            simp [hjS, hjS'])
        ext i
        have hi := congrFun hind i
        by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;> simp_all
    _ = 2 ^ J.card := by simp
    _ ≤ 2 ^ Module.finrank ℝ V := Nat.pow_le_pow_right (by norm_num) hJcard

/-! ### Lemma 5.5 without Perron-Frobenius -/

/-- L6 (Lemma 5.5, "I - Z is invertible"): a nonnegative matrix with row sums at most one, none of whose nonempty
sets of indices is closed with full row sums, has `1 - Z` invertible (max-modulus argument on `|u|`). -/
theorem one_sub_isUnit {X : Type*} [Fintype X] [DecidableEq X] (Z : Matrix X X ℝ)
    (hnn : ∀ x x', 0 ≤ Z x x') (hrow : ∀ x, ∑ x', Z x x' ≤ 1)
    (hno : ∀ Y : Finset X, Y.Nonempty → ¬ ∀ x ∈ Y, (∑ x', Z x x' = 1 ∧ ∀ x' ∉ Y, Z x x' = 0)) :
    IsUnit (1 - Z) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfix : ∀ x, u x = ∑ x', Z x x' * u x' := by
    intro x
    have h := congrFun hu x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
    simp only [Pi.sub_apply, Pi.zero_apply, Matrix.mulVec, dotProduct] at h
    linarith
  have hne : (Finset.univ : Finset X).Nonempty := by
    by_contra h
    apply hu0
    funext x
    exact absurd ⟨x, Finset.mem_univ x⟩ h
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ (fun x => |u x|) hne
  set μ := |u x0| with hμ
  have hμpos : 0 < μ := by
    by_contra h
    apply hu0
    funext x
    exact abs_nonpos_iff.mp (le_trans (hx0 x (Finset.mem_univ x)) (not_lt.mp h))
  let Y : Finset X := Finset.univ.filter (fun x => |u x| = μ)
  apply hno Y ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ.symm⟩⟩
  intro x hx
  have hxμ : |u x| = μ := (Finset.mem_filter.mp hx).2
  have hA : μ ≤ ∑ x', Z x x' * |u x'| := by
    rw [← hxμ, hfix x]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq (Finset.sum_congr rfl fun x' _ => ?_))
    rw [abs_mul, abs_of_nonneg (hnn x x')]
  have hB : ∑ x', Z x x' * |u x'| ≤ ∑ x', Z x x' * μ :=
    Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hx0 x' (Finset.mem_univ _)) (hnn x x')
  have hC : (∑ x', Z x x') * μ ≤ 1 * μ := mul_le_mul_of_nonneg_right (hrow x) hμpos.le
  rw [Finset.sum_mul] at hC
  have hsum1 : ∑ x', Z x x' = 1 := by
    have h6 : (∑ x', Z x x') * μ = 1 * μ := by rw [Finset.sum_mul]; linarith
    exact mul_right_cancel₀ (ne_of_gt hμpos) h6
  have heq : ∑ x', Z x x' * (μ - |u x'|) = 0 := by
    have h7 : ∑ x', Z x x' * (μ - |u x'|) = ∑ x', Z x x' * μ - ∑ x', Z x x' * |u x'| := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x' _ => by ring
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun x' _ =>
    mul_nonneg (hnn x x') (sub_nonneg.mpr (hx0 x' (Finset.mem_univ _)))).mp heq
  refine ⟨hsum1, fun x' hx' => ?_⟩
  have h8 : |u x'| ≠ μ := fun h => hx' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have h9 : 0 < μ - |u x'| := sub_pos.mpr (lt_of_le_of_ne (hx0 x' (Finset.mem_univ _)) h8)
  rcases mul_eq_zero.mp (hterm x' (Finset.mem_univ _)) with h | h
  · exact h
  · linarith

/-- A nonnegative stationary vector of an irreducible nonnegative matrix that is positive somewhere is positive
everywhere: its positive support is closed under the edges of `M`. -/
theorem stationary_pos_of_nonneg {Q : Type*} [Fintype Q] [DecidableEq Q] (M : Matrix Q Q ℝ)
    (hnn : ∀ q q', 0 ≤ M q q')
    (hirr : ∀ S : Finset Q, S.Nonempty → (∀ q ∈ S, ∀ q', 0 < M q q' → q' ∈ S) → S = Finset.univ)
    (β : Q → ℝ) (hβ0 : ∀ q, 0 ≤ β q) (hβ : ∀ q', β q' = ∑ q, β q * M q q')
    (q0 : Q) (hq0 : 0 < β q0) : ∀ q, 0 < β q := by
  have hS := hirr (Finset.univ.filter (fun q => 0 < β q)) ⟨q0, by simpa using hq0⟩ (by
    intro q hq q' hM
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hβ q']
    calc 0 < β q * M q q' := mul_pos hq.2 hM
      _ ≤ ∑ r, β r * M r q' :=
        Finset.single_le_sum (f := fun r => β r * M r q')
          (fun r _ => mul_nonneg (hβ0 r) (hnn r q')) (Finset.mem_univ q))
  intro q
  have hq : q ∈ Finset.univ.filter (fun q => 0 < β q) := by rw [hS]; exact Finset.mem_univ q
  exact (Finset.mem_filter.mp hq).2

/-- L7 (Lemma 5.5, "α > 0"): a stationary vector of a nonnegative, row-stochastic, irreducible matrix that is
positive at one state is positive at every state. -/
theorem stationary_pos {Q : Type*} [Fintype Q] [DecidableEq Q] (M : Matrix Q Q ℝ)
    (hnn : ∀ q q', 0 ≤ M q q') (hrow : ∀ q, ∑ q', M q q' = 1)
    (hirr : ∀ S : Finset Q, S.Nonempty → (∀ q ∈ S, ∀ q', 0 < M q q' → q' ∈ S) → S = Finset.univ)
    (α : Q → ℝ) (hα : Matrix.vecMul α M = α) (q0 : Q) (hq0 : 0 < α q0) : ∀ q, 0 < α q := by
  have hst : ∀ q', α q' = ∑ q, α q * M q q' := by
    intro q'
    have h := congrFun hα q'
    simp only [Matrix.vecMul, dotProduct] at h
    exact h.symm
  have habs_le : ∀ q', |α q'| ≤ ∑ q, |α q| * M q q' := by
    intro q'
    calc |α q'| = |∑ q, α q * M q q'| := by rw [← hst q']
      _ ≤ ∑ q, |α q * M q q'| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q, |α q| * M q q' :=
        Finset.sum_congr rfl fun q _ => by rw [abs_mul, abs_of_nonneg (hnn q q')]
  have hsum : ∑ q', ∑ q, |α q| * M q q' = ∑ q', |α q'| := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.mul_sum, hrow q, mul_one]
  have habs : ∀ q', |α q'| = ∑ q, |α q| * M q q' := by
    have hnn' : ∀ q' ∈ (Finset.univ : Finset Q), 0 ≤ (∑ q, |α q| * M q q') - |α q'| :=
      fun q' _ => sub_nonneg.mpr (habs_le q')
    have h0 : ∑ q', ((∑ q, |α q| * M q q') - |α q'|) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn').mp h0
    intro q'
    linarith [hz q' (Finset.mem_univ _)]
  have hβst : ∀ q', |α q'| - α q' = ∑ q, (|α q| - α q) * M q q' := by
    intro q'
    have e3 : ∑ q, (|α q| - α q) * M q q' = ∑ q, |α q| * M q q' - ∑ q, α q * M q q' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    linarith [habs q', hst q']
  have hβ0 : ∀ q, 0 ≤ |α q| - α q := fun q => sub_nonneg.mpr (le_abs_self _)
  have hαnn : ∀ q, 0 ≤ α q := by
    intro q
    by_contra hneg
    have hneg' : α q < 0 := not_le.mp hneg
    have hpos : 0 < |α q| - α q := by rw [abs_of_neg hneg']; linarith
    have h10 := stationary_pos_of_nonneg M hnn hirr (fun q => |α q| - α q) hβ0 hβst q hpos q0
    simp only [abs_of_pos hq0, sub_self] at h10
    exact lt_irrefl 0 h10
  exact stationary_pos_of_nonneg M hnn hirr α hαnn hst q0 hq0

end CernyQE
