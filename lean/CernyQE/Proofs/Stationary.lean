/-
CernyQE/Proofs/Stationary.lean — the stationary vectors of quasi-Eulerian automata (Lemmas 4.2, 5.2, 5.5).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Proofs.LinAlg

namespace CernyQE

open Classical Automaton Matrix

universe u v

section Helpers

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-! ### Entries of the weighted matrix -/

omit [Fintype Q] in
private theorem M_apply' (p : S → ℝ) (q q' : Q) :
    A.M p q q' = ∑ b, p b * (if A.step q b = q' then 1 else 0) := by
  simp only [Automaton.M, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rfl

omit [Fintype Q] in
/-- `M_{q q'}` is the weight of the letters that map `q` to `q'`. -/
private theorem M_eq_filter (p : S → ℝ) (q q' : Q) :
    A.M p q q' = ∑ b ∈ Finset.univ.filter (fun b => A.step q b = q'), p b := by
  rw [M_apply', Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

omit [Fintype Q] in
private theorem M_nonneg {p : S → ℝ} (hp : IsLetterWeights p) (q q' : Q) : 0 ≤ A.M p q q' := by
  rw [M_apply']
  exact Finset.sum_nonneg fun b _ => mul_nonneg (hp.1 b).le (by split_ifs <;> norm_num)

private theorem M_row {p : S → ℝ} (hp : IsLetterWeights p) (q : Q) : ∑ q', A.M p q q' = 1 := by
  simp only [M_apply']
  rw [Finset.sum_comm]
  have hb : ∀ b, ∑ q', p b * (if A.step q b = q' then (1 : ℝ) else 0) = p b := by
    intro b
    rw [← Finset.mul_sum]
    simp
  simp only [hb]
  exact hp.2

omit [Fintype Q] in
private theorem M_pos_step {p : S → ℝ} (hp : IsLetterWeights p) (q : Q) (b : S) :
    0 < A.M p q (A.step q b) := by
  rw [M_apply']
  calc (0 : ℝ) < p b * (if A.step q b = A.step q b then 1 else 0) := by simp [hp.1 b]
    _ ≤ _ := Finset.single_le_sum (f := fun c => p c * (if A.step q c = A.step q b then (1 : ℝ) else 0))
        (fun c _ => mul_nonneg (hp.1 c).le (by split_ifs <;> norm_num)) (Finset.mem_univ b)

/-- Strong connectivity in the closed-set form that the lemmas on stationary vectors use. -/
private theorem M_irr (hsc : A.StronglyConnected) {p : S → ℝ} (hp : IsLetterWeights p) :
    ∀ T : Finset Q, T.Nonempty → (∀ q ∈ T, ∀ q', 0 < A.M p q q' → q' ∈ T) → T = Finset.univ := by
  intro T hne hcl
  rcases hsc T (fun q hq b => hcl q hq _ (M_pos_step A hp q b)) with h | h
  · exact absurd h hne.ne_empty
  · exact h

/-- `in_p(r) = ∑_b p_b |{q : q.b = r}|`, written with indicators. -/
private theorem inW_eq_ind (p : S → ℝ) (r : Q) :
    A.inW p r = ∑ b, p b * ∑ q, (if A.step q b = r then (1 : ℝ) else 0) := by
  simp only [Automaton.inW]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [Automaton.pre, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Automaton.act]

/-- The in-weight of `r` is the column sum of `M` at `r`. -/
private theorem inW_eq_sum_M (p : S → ℝ) (r : Q) : A.inW p r = ∑ q, A.M p q r := by
  rw [inW_eq_ind]
  simp only [M_apply']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]

/-- The in-weights add up to `n`. -/
private theorem sum_inW {p : S → ℝ} (hp : IsLetterWeights p) : ∑ q, A.inW p q = Fintype.card Q := by
  simp only [inW_eq_ind]
  rw [Finset.sum_comm]
  have hb : ∀ b : S, ∑ r : Q, p b * ∑ q, (if A.step q b = r then (1 : ℝ) else 0) =
      p b * Fintype.card Q := by
    intro b
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    simp [Finset.sum_ite_eq]
  simp only [hb, ← Finset.sum_mul, hp.2, one_mul]

omit [Fintype Q] in
/-- The `E`-part of the column of `M` at `x` is `y_x`. -/
private theorem sum_E_M (E : Finset Q) (p : S → ℝ) (x : Q) :
    ∑ q ∈ E, A.M p q x = A.yIn E p x := by
  simp only [M_apply', Automaton.yIn]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum, Finset.natCast_card_filter]

/-! ### Stationarity -/

/-- If `αᵀ M` agrees with `α` off one state, it agrees everywhere (the rows of `M` sum to one). -/
private theorem vecMul_eq_of_ne {p : S → ℝ} (hp : IsLetterWeights p) (α : Q → ℝ) (s : Q)
    (h : ∀ q', q' ≠ s → vecMul α (A.M p) q' = α q') : vecMul α (A.M p) = α := by
  have htot : ∑ q', vecMul α (A.M p) q' = ∑ q', α q' := by
    simp only [vecMul, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.mul_sum, M_row A hp q, mul_one]
  have hrest : ∑ x ∈ Finset.univ.erase s, vecMul α (A.M p) x = ∑ x ∈ Finset.univ.erase s, α x :=
    Finset.sum_congr rfl fun x hx => h x (Finset.ne_of_mem_erase hx)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), ← Finset.add_sum_erase _ _ (Finset.mem_univ s),
    hrest] at htot
  funext q'
  by_cases hq : q' = s
  · rw [hq]
    linarith
  · exact h q' hq

/-- A vector equal to `1` on `E` whose product with `M` is right on `X = Q \ E` is stationary
(Definition 1.1 (a), (b)). -/
private theorem stat_of_X {d : ℕ} (W : QEWitness A d) (α : Q → ℝ) (hE : ∀ q ∈ W.E, α q = 1)
    (hX : ∀ x, x ∉ W.E → vecMul α (A.M W.p) x = α x) : A.IsStationary W.p α := by
  refine ⟨fun h0 => ?_, vecMul_eq_of_ne A W.weights α W.s fun q' hq' => ?_⟩
  · have h1 := hE W.s W.s_mem
    rw [h0] at h1
    simp at h1
  · by_cases hq'E : q' ∈ W.E
    · rw [hE q' hq'E, ← W.inW_one q' hq'E hq', inW_eq_sum_M]
      simp only [vecMul, dotProduct]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hqE : q ∈ W.E
      · rw [hE q hqE, one_mul]
      · have hM : A.M W.p q q' = 0 := by
          rw [M_apply']
          refine Finset.sum_eq_zero fun b _ => ?_
          have hne : A.step q b ≠ q' := by
            intro h'
            rcases W.edge_X q hqE b with h | h
            · exact h (by rw [h']; exact hq'E)
            · exact hq' (h'.symm.trans h)
          simp [hne]
        rw [hM, mul_zero]
    · exact hX q' hq'E

/-! ### Degree one -/

/-- For a witness with `X = {x}`, a sum over `Q` splits into the sum over `E` and the term at `x`. -/
private theorem sum_split {d : ℕ} (W : QEWitness A d) (x : Q) (hx : W.X = {x}) (f : Q → ℝ) :
    ∑ q, f q = ∑ q ∈ W.E, f q + f x := by
  rw [← Finset.sum_sdiff (Finset.subset_univ W.E)]
  have hX : Finset.univ \ W.E = {x} := hx
  rw [hX, Finset.sum_singleton, add_comm]

private theorem x_not_mem {d : ℕ} (W : QEWitness A d) (x : Q) (hx : W.X = {x}) : x ∉ W.E := by
  have h : x ∈ Finset.univ \ W.E := by
    have hX : Finset.univ \ W.E = {x} := hx
    rw [hX]
    exact Finset.mem_singleton_self x
  exact (Finset.mem_sdiff.mp h).2

private theorem eq_x_of_not_mem {d : ℕ} (W : QEWitness A d) (x : Q) (hx : W.X = {x}) (q : Q) (hq : q ∉ W.E) :
    q = x := by
  have h : q ∈ Finset.univ \ W.E := Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hq⟩
  have hX : Finset.univ \ W.E = {x} := hx
  rw [hX] at h
  exact Finset.mem_singleton.mp h

end Helpers

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- tex:506-510: the edges leaving `x` end at `x` or at `s`; `in_p(x) = y + z`; `in_p(s) = 2 - y - z`. -/
theorem sec4_inW_xs_proved (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) :
    (∀ b, A.step x b = x ∨ A.step x b = W.s) ∧ A.inW W.p x = A.yIn W.E W.p x + A.zLoop W.p x ∧
      A.inW W.p W.s = 2 - A.yIn W.E W.p x - A.zLoop W.p x := by
  have hxE := x_not_mem A W x hx
  have hinx : A.inW W.p x = A.yIn W.E W.p x + A.zLoop W.p x := by
    rw [inW_eq_sum_M, sum_split A W x hx, sum_E_M, M_eq_filter]
    rfl
  refine ⟨fun b => ?_, hinx, ?_⟩
  · rcases W.edge_X x hxE b with h | h
    · exact Or.inl (eq_x_of_not_mem A W x hx _ h)
    · exact Or.inr h
  · have htot := sum_inW A W.weights
    have hn : (Fintype.card Q : ℝ) = W.E.card + 1 := by
      have h1 := sum_split A W x hx (fun _ => (1 : ℝ))
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
      exact h1
    rw [sum_split A W x hx, ← Finset.add_sum_erase _ _ W.s_mem] at htot
    have hrest : ∑ q ∈ W.E.erase W.s, A.inW W.p q = (W.E.erase W.s).card := by
      rw [Finset.sum_congr rfl fun q hq =>
        W.inW_one q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)]
      simp
    have hcard : ((W.E.erase W.s).card : ℝ) + 1 = W.E.card := by
      exact_mod_cast Finset.card_erase_add_one W.s_mem
    rw [hrest, hinx] at htot
    linarith

/-- Lemma 4.2, tex:512-514. -/
theorem lem_4_2_proved (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) (hz : A.zLoop W.p x < 1) :
    A.IsStationary W.p (A.alphaDeg1 W.E W.p x) := by
  have hxE := x_not_mem A W x hx
  refine stat_of_X A W _ (fun q hq => ?_) (fun x' hx' => ?_)
  · have hqx : q ≠ x := fun h => hxE (h ▸ hq)
    simp [Automaton.alphaDeg1, hqx]
  · rw [eq_x_of_not_mem A W x hx x' hx']
    simp only [vecMul, dotProduct]
    rw [sum_split A W x hx]
    have hE : ∑ q ∈ W.E, A.alphaDeg1 W.E W.p x q * A.M W.p q x = A.yIn W.E W.p x := by
      rw [← sum_E_M]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqx : q ≠ x := fun h => hxE (h ▸ hq)
      simp [Automaton.alphaDeg1, hqx]
    have hMxx : A.M W.p x x = A.zLoop W.p x := by rw [M_eq_filter]; rfl
    rw [hE, hMxx]
    simp only [Automaton.alphaDeg1, ite_true]
    have h1 : (1 : ℝ) - A.zLoop W.p x ≠ 0 := by linarith
    field_simp
    ring

/-- Lemma 5.2 (weight count), tex:580-582 (for a witness of any degree). -/
theorem lem_5_2_proved {d : ℕ} (W : QEWitness A d) (T : Finset Q) (hT : T ⊆ W.E.erase W.s)
    (_hne : T.Nonempty) (hin : ∀ q b, A.step q b ∈ T → q ∈ T) : A.IsClosed T := by
  have hp := W.weights
  let gap : S → Q → ℝ := fun b q => (if q ∈ T then 1 else 0) - (if A.step q b ∈ T then 1 else 0)
  have hgap0 : ∀ b q, 0 ≤ gap b q := by
    intro b q
    simp only [gap]
    by_cases h1 : A.step q b ∈ T
    · simp [h1, hin q b h1]
    · by_cases h2 : q ∈ T <;> simp [h1, h2]
  have hsumT : ∑ r ∈ T, A.inW W.p r = T.card := by
    rw [Finset.sum_congr rfl fun r hr =>
      W.inW_one r (Finset.mem_of_mem_erase (hT hr)) (Finset.ne_of_mem_erase (hT hr))]
    simp
  have hsum2 : ∑ r ∈ T, A.inW W.p r = ∑ b, W.p b * ∑ q, (if A.step q b ∈ T then (1 : ℝ) else 0) := by
    simp only [inW_eq_ind]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Finset.sum_ite_eq]
  have hsum3 : (T.card : ℝ) = ∑ b, W.p b * ∑ q, (if q ∈ T then (1 : ℝ) else 0) := by
    rw [← Finset.sum_mul, hp.2, one_mul, Finset.sum_boole]
    simp
  have htot : ∑ b, W.p b * ∑ q, gap b q = 0 := by
    simp only [gap, Finset.sum_sub_distrib, mul_sub]
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
    mul_nonneg (hp.1 b).le (Finset.sum_nonneg fun q _ => hgap0 b q)).mp htot
  intro q hq b
  have hb := hterm b (Finset.mem_univ b)
  have hsum0 : ∑ q, gap b q = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact absurd h (hp.1 b).ne'
    · exact h
  have hq0 := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hgap0 b q).mp hsum0 q (Finset.mem_univ q)
  by_contra hqb
  simp [gap, hq, hqb] at hq0

end General

section General2

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- The entries of `Z` are the entries of `M` between exceptional states. -/
private theorem Zmat_eq (E : Finset Q) (p : S → ℝ) (x x' : (Finset.univ \ E : Finset Q)) :
    A.Zmat E p x x' = A.M p x.1 x'.1 := by
  rw [M_eq_filter]
  rfl

/-- A row of `Z` sums to the weight of the letters that keep the state in `X`. -/
private theorem Zmat_row (E : Finset Q) (p : S → ℝ) (x : (Finset.univ \ E : Finset Q)) :
    ∑ x', A.Zmat E p x x' = ∑ q' ∈ Finset.univ \ E, A.M p x.1 q' := by
  simp only [Zmat_eq]
  exact Finset.sum_coe_sort (Finset.univ \ E) (fun q' => A.M p x.1 q')

/-- `I - Z` is invertible (Lemma 5.5, first part). -/
private theorem one_sub_Zmat_isUnit (hsc : A.StronglyConnected) {d : ℕ} (W : QEWitness A d) :
    IsUnit (1 - A.Zmat W.E W.p) := by
  have hp := W.weights
  refine one_sub_isUnit _ (fun x x' => ?_) (fun x => ?_) ?_
  · rw [Zmat_eq]
    exact M_nonneg A hp _ _
  · rw [Zmat_row, ← M_row A hp x.1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun q' _ _ => M_nonneg A hp _ _)
  · intro Y hYne hY
    let Y' : Finset Q := Y.map (Function.Embedding.subtype _)
    have hcl : A.IsClosed Y' := by
      intro q hq b
      obtain ⟨x, hxY, rfl⟩ := Finset.mem_map.mp hq
      obtain ⟨hrow1, hzero⟩ := hY x hxY
      have hnotE : A.step x.1 b ∉ W.E := by
        intro hrE
        have hsplit := Finset.sum_sdiff (Finset.subset_univ W.E) (f := fun q' => A.M W.p x.1 q')
        rw [M_row A hp x.1, ← Zmat_row, hrow1] at hsplit
        have hE0 : ∑ q' ∈ W.E, A.M W.p x.1 q' = 0 := by linarith
        have hle := Finset.single_le_sum (f := fun q' => A.M W.p x.1 q')
          (fun q' _ => M_nonneg A hp _ _) hrE
        have hpos := M_pos_step A hp x.1 b
        linarith
      let x' : (Finset.univ \ W.E : Finset Q) :=
        ⟨A.step x.1 b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotE⟩⟩
      have hx'Y : x' ∈ Y := by
        by_contra hx'
        have h0 := hzero x' hx'
        rw [Zmat_eq] at h0
        have hpos := M_pos_step A hp x.1 b
        simp only [x'] at h0
        linarith
      exact Finset.mem_map.mpr ⟨x', hx'Y, rfl⟩
    rcases hsc Y' hcl with h | h
    · obtain ⟨y, hy⟩ := hYne
      have : y.1 ∈ Y' := Finset.mem_map.mpr ⟨y, hy, rfl⟩
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have hs : W.s ∈ Y' := by rw [h]; exact Finset.mem_univ _
      obtain ⟨y, -, hy⟩ := Finset.mem_map.mp hs
      have hy' : y.1 = W.s := hy
      have hyX : W.s ∈ Finset.univ \ W.E := by rw [← hy']; exact y.2
      exact (Finset.mem_sdiff.mp hyX).2 W.s_mem

private theorem alphaStat_E (E : Finset Q) (p : S → ℝ) (q : Q) (hq : q ∈ E) : A.alphaStat E p q = 1 := by
  have h : q ∉ Finset.univ \ E := fun h => (Finset.mem_sdiff.mp h).2 hq
  simp [Automaton.alphaStat, h]

private theorem alphaStat_X (E : Finset Q) (p : S → ℝ) (x : (Finset.univ \ E : Finset Q)) :
    A.alphaStat E p x.1 = A.tvec E p x := by
  simp [Automaton.alphaStat, x.2]

/-- Lemma 5.5, tex:638-643 (for every degree). -/
theorem lem_5_5_proved (hsc : A.StronglyConnected) {d : ℕ} (W : QEWitness A d) :
    IsUnit (1 - A.Zmat W.E W.p) ∧ A.IsStationary W.p (A.alphaStat W.E W.p) ∧
      ∀ q, 0 < A.alphaStat W.E W.p q := by
  have hp := W.weights
  have hU := one_sub_Zmat_isUnit A hsc W
  set Z := A.Zmat W.E W.p with hZ
  set t := A.tvec W.E W.p with ht
  have hfix : t = A.yvec W.E W.p + vecMul t Z := by
    have h1 : vecMul t (1 - Z) = A.yvec W.E W.p := by
      rw [ht, Automaton.tvec, Matrix.vecMul_vecMul,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.vecMul_one]
    rw [Matrix.vecMul_sub, Matrix.vecMul_one] at h1
    rw [← h1]
    abel
  have hstat : A.IsStationary W.p (A.alphaStat W.E W.p) := by
    refine stat_of_X A W _ (alphaStat_E A W.E W.p) (fun x hxE => ?_)
    have hxX : x ∈ Finset.univ \ W.E := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxE⟩
    let xx : (Finset.univ \ W.E : Finset Q) := ⟨x, hxX⟩
    simp only [vecMul, dotProduct]
    rw [← Finset.sum_sdiff (Finset.subset_univ W.E)]
    have hEpart : ∑ q ∈ W.E, A.alphaStat W.E W.p q * A.M W.p q x = A.yIn W.E W.p x := by
      rw [← sum_E_M]
      exact Finset.sum_congr rfl fun q hq => by rw [alphaStat_E A W.E W.p q hq, one_mul]
    have hXpart : ∑ q ∈ Finset.univ \ W.E, A.alphaStat W.E W.p q * A.M W.p q x = vecMul t Z xx := by
      rw [← Finset.sum_coe_sort (Finset.univ \ W.E)]
      simp only [vecMul, dotProduct]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [alphaStat_X, hZ, Zmat_eq]
    rw [hEpart, hXpart, alphaStat_X A W.E W.p xx]
    have h2 := congrFun hfix xx
    simp only [Pi.add_apply] at h2
    rw [← ht, h2]
    simp only [Automaton.yvec, xx]
    ring
  refine ⟨hU, hstat, ?_⟩
  exact stationary_pos (A.M W.p) (M_nonneg A hp) (M_row A hp) (M_irr A hsc hp) _ hstat.2 W.s
    (by rw [alphaStat_E A W.E W.p W.s W.s_mem]; norm_num)

/-- The uniqueness part, given one stationary vector positive somewhere. -/
private theorem unique_of_pos (hsc : A.StronglyConnected) {p : S → ℝ} (hp : IsLetterWeights p) (π : Q → ℝ)
    (hπ : vecMul π (A.M p) = π) (q0 : Q) (hq0 : 0 < π q0) :
    ∃ π : Q → ℝ, (∀ q, 0 < π q) ∧ A.IsStationary p π ∧ ∀ α, A.IsStationary p α → ∃ c : ℝ, α = c • π := by
  have hpos := stationary_pos (A.M p) (M_nonneg A hp) (M_row A hp) (M_irr A hsc hp) π hπ q0 hq0
  refine ⟨π, hpos, ⟨fun h => by rw [h] at hq0; simp at hq0, hπ⟩, fun α hα => ?_⟩
  obtain ⟨q1, -, hq1⟩ := Finset.exists_min_image Finset.univ (fun q => α q / π q) ⟨q0, Finset.mem_univ _⟩
  set c := α q1 / π q1 with hc
  refine ⟨c, ?_⟩
  set γ := α - c • π with hγ
  have hγ0 : ∀ q, 0 ≤ γ q := by
    intro q
    have h1 : c ≤ α q / π q := hq1 q (Finset.mem_univ q)
    rw [le_div_iff₀ (hpos q)] at h1
    simp only [hγ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hγ1 : γ q1 = 0 := by
    simp only [hγ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc]
    rw [div_mul_cancel₀ _ (hpos q1).ne']
    ring
  have hγst : ∀ q', γ q' = ∑ q, γ q * A.M p q q' := by
    have h1 : vecMul γ (A.M p) = γ := by
      rw [hγ, Matrix.sub_vecMul, Matrix.smul_vecMul, hα.2, hπ]
    intro q'
    have h2 := congrFun h1 q'
    simp only [vecMul, dotProduct] at h2
    exact h2.symm
  have hγz : γ = 0 := by
    by_contra hne
    obtain ⟨q2, hq2⟩ : ∃ q2, γ q2 ≠ 0 := Function.ne_iff.mp hne
    have hq2pos : 0 < γ q2 := lt_of_le_of_ne (hγ0 q2) (Ne.symm hq2)
    have h3 := stationary_pos_of_nonneg (A.M p) (M_nonneg A hp) (M_irr A hsc hp) γ hγ0 hγst q2 hq2pos q1
    rw [hγ1] at h3
    exact lt_irrefl 0 h3
  exact sub_eq_zero.mp hγz

/-- tex:653-654: for a strongly connected automaton and letter weights, the stationary vectors are the multiples of
one positive vector. -/
theorem lem_5_5_unique_proved (hsc : A.StronglyConnected) [Nonempty Q] (p : S → ℝ) (hp : IsLetterWeights p) :
    ∃ π : Q → ℝ, (∀ q, 0 < π q) ∧ A.IsStationary p π ∧ ∀ α, A.IsStationary p α → ∃ c : ℝ, α = c • π := by
  have hdet : (A.M p - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      obtain ⟨q⟩ := ‹Nonempty Q›
      exact one_ne_zero (congrFun h q)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
      funext q
      simp only [mulVec, dotProduct, mul_one]
      exact M_row A hp q
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hvst : vecMul v (A.M p) = v := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hv
    exact hv
  obtain ⟨q0, hq0⟩ : ∃ q0, v q0 ≠ 0 := Function.ne_iff.mp hv0
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · refine unique_of_pos A hsc hp (-v) (by rw [Matrix.neg_vecMul, hvst]) q0 ?_
    simp only [Pi.neg_apply]
    linarith
  · exact unique_of_pos A hsc hp v hvst q0 hpos

/-- tex:93-94: for a strongly connected quasi-Eulerian automaton the stationary vector can be taken equal to `1` on
`E` and positive on the exceptional states (Lemma 5.5). -/
theorem intro_statd_proved (hsc : A.StronglyConnected) {d : ℕ} (W : QEWitness A d) :
    ∃ α : Q → ℝ, A.IsStationary W.p α ∧ (∀ q ∈ W.E, α q = 1) ∧ ∀ q, 0 < α q := by
  obtain ⟨-, hst, hpos⟩ := lem_5_5_proved A hsc W
  exact ⟨A.alphaStat W.E W.p, hst, alphaStat_E A W.E W.p, hpos⟩

/-- tex:973: every automaton with `n ≥ 2` states over a nonempty alphabet is quasi-Eulerian of degree `n - 1`
(with `E = {s}`). -/
theorem sec6_qe_n_minus_1_proved [Nonempty S] (hn : 2 ≤ Fintype.card Q) : QuasiEulerian A (Fintype.card Q - 1) := by
  obtain ⟨s⟩ : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  refine ⟨⟨{s}, s, fun _ => 1 / (Fintype.card S : ℝ), ?_, Finset.mem_singleton_self s, ?_, ?_, ?_⟩⟩
  · rw [Finset.card_singleton]
    omega
  · refine ⟨fun _ => by positivity, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · intro q _ b
    by_cases h : A.step q b = s
    · exact Or.inr h
    · exact Or.inl (by simpa using h)
  · intro r hr hrs
    exact absurd (Finset.mem_singleton.mp hr) hrs

end General2

end CernyQE
