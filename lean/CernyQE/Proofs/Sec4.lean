/-
CernyQE/Proofs/Sec4.lean — Section 4: quasi-Eulerian automata of degree one (Theorem 4.1, Remark 4.3).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Proofs.Rows2
import CernyQE.Proofs.Sec3Levels
import CernyQE.Proofs.Stationary
import CernyQE.Proofs.Sec51
import CernyQE.Proofs.Thm31
import CernyQE.Proofs.CernyLower

namespace CernyQE

open Classical Automaton Matrix

universe u v

/-! ### The Cerny automata: letters, preimages, in-weights -/

section Cerny

theorem sec4_cn_step_a0 (n : ℕ) [NeZero n] : (cerny n).step 0 0 = 1 := by
  simp [cerny]

theorem sec4_cn_step_a {n : ℕ} [NeZero n] {q : Fin n} (hq : q ≠ 0) : (cerny n).step q 0 = q := by
  simp [cerny, hq]

theorem sec4_cn_step_b (n : ℕ) [NeZero n] (q : Fin n) : (cerny n).step q 1 = q + 1 := by
  simp [cerny]

theorem sec4_fin_two (c : Fin 2) : c = 0 ∨ c = 1 := by
  revert c; decide

theorem sec4_cn_step_zero (n : ℕ) [NeZero n] (b : Fin 2) : (cerny n).step 0 b = 1 := by
  rcases sec4_fin_two b with rfl | rfl
  · exact sec4_cn_step_a0 n
  · rw [sec4_cn_step_b, zero_add]

theorem sec4_cn_one_ne_zero (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (1 : Fin n) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
  exact one_ne_zero hv

theorem sec4_cn_pre_a {n : ℕ} [NeZero n] {r : Fin n} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    (cerny n).pre {r} [0] = {r} := by
  ext q
  simp only [mem_pre, act_singleton, Finset.mem_singleton]
  by_cases hq : q = 0
  · subst hq
    rw [sec4_cn_step_a0]
    exact ⟨fun h => absurd h.symm h1, fun h => absurd h.symm h0⟩
  · rw [sec4_cn_step_a hq]

theorem sec4_cn_pre_b (n : ℕ) [NeZero n] (r : Fin n) : (cerny n).pre {r} [1] = {r - 1} := by
  ext q
  simp only [mem_pre, act_singleton, Finset.mem_singleton, sec4_cn_step_b]
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

theorem sec4_cn_inW {n : ℕ} [NeZero n] (p : Fin 2 → ℝ) (hp : IsLetterWeights p) {r : Fin n}
    (h0 : r ≠ 0) (h1 : r ≠ 1) : (cerny n).inW p r = 1 := by
  have hsum := hp.2
  rw [Fin.sum_univ_two] at hsum
  unfold Automaton.inW
  rw [Fin.sum_univ_two, sec4_cn_pre_a h0 h1, sec4_cn_pre_b, Finset.card_singleton, Finset.card_singleton]
  push_cast
  linarith

theorem sec4_cn_zLoop (n : ℕ) [NeZero n] (hn : 2 ≤ n) (p : Fin 2 → ℝ) : (cerny n).zLoop p 0 = 0 := by
  unfold Automaton.zLoop
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.mem_filter, sec4_cn_step_zero] at hb
  exact absurd hb.2 (sec4_cn_one_ne_zero n hn)

theorem sec4_cn_yIn (n : ℕ) [NeZero n] (hn : 2 ≤ n) (p : Fin 2 → ℝ) :
    (cerny n).yIn (Finset.univ.erase 0) p 0 = p 1 := by
  have ha : (Finset.univ.erase (0 : Fin n)).filter (fun q => (cerny n).step q 0 = 0) = ∅ := by
    apply Finset.filter_false_of_mem
    intro q hq h
    have hq0 := Finset.ne_of_mem_erase hq
    rw [sec4_cn_step_a hq0] at h
    exact hq0 h
  have hb : (Finset.univ.erase (0 : Fin n)).filter (fun q => (cerny n).step q 1 = 0) = {-1} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton, sec4_cn_step_b]
    constructor
    · rintro ⟨_, h⟩
      exact eq_neg_of_add_eq_zero_left h
    · rintro rfl
      exact ⟨⟨neg_ne_zero.mpr (sec4_cn_one_ne_zero n hn), Finset.mem_univ _⟩, neg_add_cancel 1⟩
  unfold Automaton.yIn
  rw [Fin.sum_univ_two, ha, hb, Finset.card_empty, Finset.card_singleton]
  simp

end Cerny

/-! ### Rows on `C_n` -/

theorem thm_4_1_cn_witness_core (n : ℕ) [NeZero n] (hn : 2 ≤ n) (p : Fin 2 → ℝ) (hp : IsLetterWeights p) :
    ∃ W : QEWitness (cerny n) 1, W.E = Finset.univ.erase 0 ∧ W.s = 1 ∧ W.p = p := by
  have h10 := sec4_cn_one_ne_zero n hn
  refine ⟨⟨Finset.univ.erase 0, 1, p, ?_, ?_, hp, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  · exact Finset.mem_erase.mpr ⟨h10, Finset.mem_univ _⟩
  · intro q hq b
    have hq0 : q = 0 := by simpa using hq
    subst hq0
    exact Or.inr (sec4_cn_step_zero n b)
  · intro r hr hr1
    exact sec4_cn_inW p hp (Finset.ne_of_mem_erase hr) hr1

theorem rem_4_3_cn_zyt_core (n : ℕ) [NeZero n] (hn : 2 ≤ n) (p : Fin 2 → ℝ) (hp : IsLetterWeights p) :
    (cerny n).zLoop p 0 = 0 ∧ (cerny n).yIn (Finset.univ.erase 0) p 0 = p 1 ∧
      (cerny n).yIn (Finset.univ.erase 0) p 0 / (1 - (cerny n).zLoop p 0) = p 1 ∧ 0 < p 1 ∧ p 1 < 1 := by
  have hz := sec4_cn_zLoop n hn p
  have hy := sec4_cn_yIn n hn p
  have hsum := hp.2
  rw [Fin.sum_univ_two] at hsum
  refine ⟨hz, hy, by rw [hz, hy, sub_zero, div_one], hp.1 1, ?_⟩
  linarith [hp.1 0]

/-! ### Degree one: the exceptional state, `z` and `y` -/

section Degree1

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

theorem sec4_x_not_mem (W : QEWitness A 1) {x : Q} (hx : W.X = {x}) : x ∉ W.E := by
  have h : x ∈ W.X := by rw [hx]; exact Finset.mem_singleton_self x
  simpa [QEWitness.X] using h

theorem sec4_eq_x_of_not_mem (W : QEWitness A 1) {x : Q} (hx : W.X = {x}) {q : Q} (hq : q ∉ W.E) : q = x := by
  have h : q ∈ W.X := by simpa [QEWitness.X] using hq
  rw [hx] at h
  exact Finset.mem_singleton.mp h

theorem sec4_zLoop_split {d : ℕ} (W : QEWitness A d) (x : Q) :
    A.zLoop W.p x + ∑ b ∈ Finset.univ.filter (fun b => ¬ A.step x b = x), W.p b = 1 := by
  unfold Automaton.zLoop
  rw [Finset.sum_filter_add_sum_filter_not]
  exact W.weights.2

theorem sec4_zLoop_le_one {d : ℕ} (W : QEWitness A d) (x : Q) : A.zLoop W.p x ≤ 1 := by
  have h := sec4_zLoop_split A W x
  have h0 : 0 ≤ ∑ b ∈ Finset.univ.filter (fun b => ¬ A.step x b = x), W.p b :=
    Finset.sum_nonneg (fun b _ => (W.weights.1 b).le)
  linarith

theorem sec4_zLoop_lt_one_iff {d : ℕ} (W : QEWitness A d) (x : Q) :
    A.zLoop W.p x < 1 ↔ ∃ b, A.step x b ≠ x := by
  have h := sec4_zLoop_split A W x
  constructor
  · intro hz
    by_contra hall
    push Not at hall
    have hempty : Finset.univ.filter (fun b => ¬ A.step x b = x) = ∅ :=
      Finset.filter_false_of_mem (fun b _ hb => hb (hall b))
    rw [hempty, Finset.sum_empty] at h
    linarith
  · rintro ⟨b, hb⟩
    have hpos : 0 < ∑ b ∈ Finset.univ.filter (fun b => ¬ A.step x b = x), W.p b :=
      Finset.sum_pos (fun c _ => W.weights.1 c) ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
    linarith

theorem sec4_yIn_nonneg {d : ℕ} (W : QEWitness A d) (x : Q) : 0 ≤ A.yIn W.E W.p x :=
  Finset.sum_nonneg (fun b _ => mul_nonneg (W.weights.1 b).le (Nat.cast_nonneg _))

theorem sec4_yIn_pos_iff {d : ℕ} (W : QEWitness A d) (x : Q) :
    0 < A.yIn W.E W.p x ↔ ∃ q ∈ W.E, ∃ b, A.step q b = x := by
  constructor
  · intro hy
    by_contra hno
    push Not at hno
    have h0 : ∀ b, W.E.filter (fun q => A.step q b = x) = ∅ := fun b =>
      Finset.filter_false_of_mem (fun q hq => hno q hq b)
    unfold Automaton.yIn at hy
    simp [h0] at hy
  · rintro ⟨q, hq, b, hb⟩
    unfold Automaton.yIn
    apply Finset.sum_pos' (fun c _ => mul_nonneg (W.weights.1 c).le (Nat.cast_nonneg _))
    refine ⟨b, Finset.mem_univ _, mul_pos (W.weights.1 b) ?_⟩
    exact_mod_cast Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hb⟩⟩

theorem sec4_E_closed (W : QEWitness A 1) {x : Q} (hx : W.X = {x}) (hy : A.yIn W.E W.p x = 0) :
    A.IsClosed W.E := by
  intro q hq b
  by_contra hb
  have hqb := sec4_eq_x_of_not_mem A W hx hb
  have : 0 < A.yIn W.E W.p x := (sec4_yIn_pos_iff A W x).mpr ⟨q, hq, b, hqb⟩
  linarith

omit [Fintype Q] [DecidableEq Q] [Fintype S] in
theorem sec4_singleton_closed {x : Q} (h : ∀ b, A.step x b = x) : A.IsClosed {x} := by
  intro q hq b
  rw [Finset.mem_singleton] at hq ⊢
  subst hq
  exact h b

theorem sec4_sc_imp (W : QEWitness A 1) {x : Q} (hx : W.X = {x}) (hsc : A.StronglyConnected) :
    A.zLoop W.p x < 1 ∧ 0 < A.yIn W.E W.p x := by
  have hxE := sec4_x_not_mem A W hx
  have hsx : W.s ≠ x := fun h => hxE (h ▸ W.s_mem)
  constructor
  · rw [sec4_zLoop_lt_one_iff]
    by_contra hall
    push Not at hall
    rcases hsc {x} (sec4_singleton_closed A hall) with h | h
    · exact Finset.singleton_ne_empty x h
    · have hs : W.s ∈ ({x} : Finset Q) := by rw [h]; exact Finset.mem_univ _
      exact hsx (Finset.mem_singleton.mp hs)
  · rcases (sec4_yIn_nonneg A W x).lt_or_eq with h | h
    · exact h
    · rcases hsc W.E (sec4_E_closed A W hx h.symm) with h' | h'
      · have hs := W.s_mem
        rw [h'] at hs
        simp at hs
      · exact absurd (by rw [h']; exact Finset.mem_univ x) hxE

theorem sec4_alphaDeg1_pos (W : QEWitness A 1) {x : Q} (hz : A.zLoop W.p x < 1) (hy : 0 < A.yIn W.E W.p x)
    (q : Q) : 0 < A.alphaDeg1 W.E W.p x q := by
  unfold Automaton.alphaDeg1
  split_ifs
  · exact div_pos hy (by linarith)
  · exact one_pos

theorem sec4_alphaDeg1_off (W : QEWitness A 1) (x : Q) {q : Q} (hq : q ≠ x) : A.alphaDeg1 W.E W.p x q = 1 := by
  simp [Automaton.alphaDeg1, hq]

theorem intro_deg1_in_thm31_core (_hA : A.Synchronizing) (hsc : A.StronglyConnected) (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) :
    A.zLoop W.p x < 1 ∧ A.IsStationary W.p (A.alphaDeg1 W.E W.p x) ∧ (∀ q, 0 < A.alphaDeg1 W.E W.p x q) ∧
      ∀ q ∈ W.E, A.alphaDeg1 W.E W.p x q = 1 := by
  obtain ⟨hz, hy⟩ := sec4_sc_imp A W hx hsc
  refine ⟨hz, lem_4_2_proved A W x hx hz, sec4_alphaDeg1_pos A W hz hy, fun q hq => ?_⟩
  exact sec4_alphaDeg1_off A W x (fun h => sec4_x_not_mem A W hx (h ▸ hq))

theorem thm_4_1_case_sc_core (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) :
    (A.zLoop W.p x < 1 → 0 < A.yIn W.E W.p x → A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞)) ∧
      (A.StronglyConnected ↔ A.zLoop W.p x < 1 ∧ 0 < A.yIn W.E W.p x) := by
  refine ⟨fun hz hy => ?_, ⟨sec4_sc_imp A W hx, fun ⟨hz, hy⟩ => ?_⟩⟩
  · exact thm_3_1_proved A hA hn W.p W.weights _ (lem_4_2_proved A W x hx hz) (sec4_alphaDeg1_pos A W hz hy) x
      (fun q q' hq hq' => by rw [sec4_alphaDeg1_off A W x hq, sec4_alphaDeg1_off A W x hq'])
  · exact lem_2_1_proved A hA W.p W.weights _ (lem_4_2_proved A W x hx hz) (sec4_alphaDeg1_pos A W hz hy)

/-! ### Restriction to a closed set -/

omit [Fintype Q] [DecidableEq Q] [Fintype S] in
theorem sec4_restrict_act (C : Finset Q) (hC : A.IsClosed C) :
    ∀ (w : List S) (q : C), ((A.restrict C hC).act q w).1 = A.act q.1 w
  | [], _ => rfl
  | b :: w, q => sec4_restrict_act C hC w ((A.restrict C hC).step q b)

omit [Fintype Q] [DecidableEq Q] [Fintype S] in
theorem sec4_restrict_sync (hA : A.Synchronizing) (C : Finset Q) (hne : C.Nonempty) (hC : A.IsClosed C) :
    (A.restrict C hC).Synchronizing := by
  obtain ⟨w, r, hr⟩ := hA
  obtain ⟨q₀, hq₀⟩ := hne
  have hrC : r ∈ C := by
    rw [← hr q₀]
    exact Automaton.act_mem_of_closed A (· ∈ C) (fun q hq b => hC q hq b) w q₀ hq₀
  refine ⟨w, ⟨r, hrC⟩, fun q => Subtype.ext ?_⟩
  rw [sec4_restrict_act A C hC w q, hr]

omit [Fintype Q] [DecidableEq Q] [Fintype S] in
/-- A letter mapping every state into a closed set `C`, then a reset word of `A|_C`. -/
theorem sec4_rt_le_succ (C : Finset Q) (hC : A.IsClosed C) (c : S) (hc : ∀ q, A.step q c ∈ C)
    (hB : (A.restrict C hC).Synchronizing) : A.rt ≤ (A.restrict C hC).rt + 1 := by
  obtain ⟨w₀, hw₀⟩ := hB
  have hne : (A.restrict C hC).rt ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top w₀.length) (minLen_le_length hw₀)
  obtain ⟨w, ⟨r, hr⟩, hwl⟩ := exists_of_minLen_ne_top hne
  have hreset : A.IsReset (c :: w) := ⟨r.1, fun q => by
    have h := sec4_restrict_act A C hC w ⟨A.step q c, hc q⟩
    rw [hr] at h
    exact h.symm⟩
  calc A.rt ≤ ((c :: w).length : ℕ∞) := minLen_le_length hreset
    _ = (A.restrict C hC).rt + 1 := by
      rw [List.length_cons, Nat.cast_add, Nat.cast_one]
      exact congrArg (· + 1) hwl

omit [Fintype Q] [Fintype S] in
theorem sec4_restrict_pre_card (C : Finset Q) (hC : A.IsClosed C) (r : C) (b : S) :
    ((A.restrict C hC).pre {r} [b]).card = (C.filter (fun q => A.step q b = r.1)).card := by
  apply Finset.card_bij (fun q _ => q.1)
  · intro q hq
    rw [mem_pre, act_singleton, Finset.mem_singleton] at hq
    exact Finset.mem_filter.mpr ⟨q.2, by rw [← hq]; rfl⟩
  · intro q _ q' _ h
    exact Subtype.ext h
  · intro q hq
    obtain ⟨hqC, hqb⟩ := Finset.mem_filter.mp hq
    refine ⟨⟨q, hqC⟩, ?_, rfl⟩
    rw [mem_pre, act_singleton, Finset.mem_singleton]
    exact Subtype.ext hqb

omit [Fintype S] in
/-- `|r b⁻¹|` in `A` = the edges into `r` from `C` (those of `A|_C`) + those from outside `C`. -/
theorem sec4_pre_card_split (C : Finset Q) (hC : A.IsClosed C) (r : C) (b : S) :
    ((A.pre {r.1} [b]).card : ℝ) = ((A.restrict C hC).pre {r} [b]).card +
      ((Finset.univ \ C).filter (fun q => A.step q b = r.1)).card := by
  rw [sec4_restrict_pre_card]
  have h : A.pre {r.1} [b] = C.filter (fun q => A.step q b = r.1) ∪
      (Finset.univ \ C).filter (fun q => A.step q b = r.1) := by
    ext q
    by_cases hq : q ∈ C <;> simp [hq]
  rw [h, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff)]
  push_cast
  ring

/-! ### Case `z < 1`, `y = 0` (tex:537-543) -/

theorem sec4_inW_restrict (W : QEWitness A 1) {x : Q} (hx : W.X = {x}) (hE : A.IsClosed W.E) (r : W.E) :
    A.inW W.p r.1 = (A.restrict W.E hE).inW W.p r + ∑ b, W.p b * (if A.step x b = r.1 then 1 else 0) := by
  unfold Automaton.inW
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [sec4_pre_card_split A W.E hE r b]
  have hX : Finset.univ \ W.E = {x} := hx
  rw [hX, Finset.filter_singleton]
  split_ifs <;> simp [mul_add]

theorem sec4_y0_restrict_inW (W : QEWitness A 1) {x : Q} (hx : W.X = {x}) (hy : A.yIn W.E W.p x = 0)
    (hE : A.IsClosed W.E) (r : W.E) : (A.restrict W.E hE).inW W.p r = 1 := by
  have hsplit := sec4_inW_restrict A W hx hE r
  obtain ⟨hxs, _, hins⟩ := sec4_inW_xs_proved A W x hx
  have hxE := sec4_x_not_mem A W hx
  have hrx : r.1 ≠ x := fun h => hxE (h ▸ r.2)
  have hsx : W.s ≠ x := fun h => hxE (h ▸ W.s_mem)
  by_cases hrs : r.1 = W.s
  · have hterm : ∀ b, W.p b * (if A.step x b = r.1 then (1 : ℝ) else 0) =
        if ¬ A.step x b = x then W.p b else 0 := by
      intro b
      rcases hxs b with h1 | h1
      · simp [h1, Ne.symm hrx]
      · simp [h1, hrs, hsx]
    have hsum : ∑ b, W.p b * (if A.step x b = r.1 then (1 : ℝ) else 0) = 1 - A.zLoop W.p x := by
      rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.sum_filter]
      linarith [sec4_zLoop_split A W x]
    rw [hsum, hrs, hins, hy] at hsplit
    linarith
  · have hsum : ∑ b, W.p b * (if A.step x b = r.1 then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      rcases hxs b with h1 | h1
      · simp [h1, Ne.symm hrx]
      · simp [h1, Ne.symm hrs]
    rw [hsum, W.inW_one r.1 r.2 hrs] at hsplit
    linarith

theorem sec4_arith_y0 {n : ℕ} (h3 : 3 ≤ n) : 2 + (n - 3) * (n - 2) ≤ 1 + (n - 2) * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 3 = m by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega]
  nlinarith

theorem sec4_arith_t1 {n : ℕ} (hn : 2 ≤ n) : 1 + (n - 2) * (n - 1) ≤ (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega]
  nlinarith

theorem thm_4_1_case_y0_core (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) (hz : A.zLoop W.p x < 1) (hy : A.yIn W.E W.p x = 0) :
    ∃ hE : A.IsClosed W.E, (∀ r, (A.restrict W.E hE).inW W.p r = 1) ∧
      (3 ≤ Fintype.card Q →
        (A.restrict W.E hE).rt ≤ ((1 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞)) ∧
      (3 ≤ Fintype.card Q → A.rt ≤ ((2 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞)) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) := by
  have hE := sec4_E_closed A W hx hy
  have hinB := sec4_y0_restrict_inW A W hx hy hE
  have hB := sec4_restrict_sync A hA W.E ⟨W.s, W.s_mem⟩ hE
  have hcardB : Fintype.card W.E = Fintype.card Q - 1 := by rw [Fintype.card_coe, W.card_E]
  obtain ⟨c, hc⟩ := (sec4_zLoop_lt_one_iff A W x).mp hz
  have hxc : A.step x c = W.s := ((sec4_inW_xs_proved A W x hx).1 c).resolve_left hc
  have hcE : ∀ q, A.step q c ∈ W.E := by
    intro q
    by_cases hq : q ∈ W.E
    · exact hE q hq c
    · rw [sec4_eq_x_of_not_mem A W hx hq, hxc]
      exact W.s_mem
  have hrt := sec4_rt_le_succ A W.E hE c hcE hB
  have hBt1 : 3 ≤ Fintype.card Q →
      (A.restrict W.E hE).rt ≤ ((1 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞) := by
    intro h3
    have : Nonempty W.E := ⟨⟨W.s, W.s_mem⟩⟩
    have hstat : (A.restrict W.E hE).IsStationary W.p (fun _ => 1) :=
      (sec2_one_stationary_iff_proved (A.restrict W.E hE) W.p W.weights).mpr hinB
    have h := (thm_3_1_case_t1_proved (A.restrict W.E hE) hB (by rw [hcardB]; omega) W.p W.weights hstat).2
    rw [hcardB, show Fintype.card Q - 1 - 2 = Fintype.card Q - 3 by omega,
      show Fintype.card Q - 1 - 1 = Fintype.card Q - 2 by omega] at h
    exact h
  have hA3 : 3 ≤ Fintype.card Q → A.rt ≤ ((2 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞) := by
    intro h3
    have h := hBt1 h3
    calc A.rt ≤ (A.restrict W.E hE).rt + 1 := hrt
      _ ≤ ((1 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞) + 1 := by gcongr
      _ = ((2 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞) := by push_cast; ring
  refine ⟨hE, hinB, hBt1, hA3, ?_⟩
  by_cases h3 : 3 ≤ Fintype.card Q
  · calc A.rt ≤ ((2 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞) := hA3 h3
      _ ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) := by
        exact_mod_cast sec4_arith_y0 h3
  · have h2 : Fintype.card Q = 2 := by omega
    have hcard1 : Fintype.card W.E = 1 := by rw [hcardB, h2]
    have hreset : (A.restrict W.E hE).IsReset [] :=
      ⟨⟨W.s, W.s_mem⟩, fun q => Fintype.card_le_one_iff.mp hcard1.le _ _⟩
    have hB0 : (A.restrict W.E hE).rt ≤ 0 := by
      show minLen (A.restrict W.E hE).IsReset ≤ 0
      simpa using minLen_le_length hreset
    calc A.rt ≤ (A.restrict W.E hE).rt + 1 := hrt
      _ ≤ 0 + 1 := by gcongr
      _ = ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) := by rw [h2]; norm_num

/-! ### Case `z = 1` (tex:529-535) -/

omit [Fintype S] in
/-- `|T b⁻¹| = ∑_{q ∈ T} |{q} b⁻¹|`. -/
theorem sec4_pre_card_sum (T : Finset Q) (b : S) :
    ((A.pre T [b]).card : ℝ) = ∑ q ∈ T, ((A.pre {q} [b]).card : ℝ) := by
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q => A.step q b) (t := T)]
  · refine Finset.sum_congr rfl (fun r hr => ?_)
    congr 1
    ext q
    simp only [Finset.mem_filter, mem_pre, act_singleton, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h]; exact hr, h⟩
  · intro q hq
    simpa using hq

/-- `∑_b p_b |T b⁻¹| = ∑_{q ∈ T} in_p(q)`. -/
theorem sec4_sum_pre_eq (p : S → ℝ) (T : Finset Q) :
    ∑ b, p b * ((A.pre T [b]).card : ℝ) = ∑ q ∈ T, A.inW p q := by
  simp only [sec4_pre_card_sum A T, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

omit [Fintype S] in
/-- A chain of enlargements: if every set with property `P` other than `Q` is enlarged, keeping `P`, by a word of
length at most `L`, then a set with `P` and at least `n - k` states is mapped onto `Q` by a word of length `≤ k L`. -/
theorem sec4_chain (P : Finset Q → Prop) (L : ℕ)
    (hstep : ∀ K, P K → K ≠ Finset.univ →
      ∃ w : List S, w.length ≤ L ∧ K.card < (A.pre K w).card ∧ P (A.pre K w)) :
    ∀ k : ℕ, ∀ K, P K → Fintype.card Q - K.card ≤ k →
      ∃ u : List S, u.length ≤ k * L ∧ A.pre K u = Finset.univ := by
  intro k
  induction k with
  | zero =>
    intro K _ hk
    refine ⟨[], by simp, ?_⟩
    rw [pre_nil]
    exact Finset.eq_univ_of_card K (by have := Finset.card_le_univ K; omega)
  | succ k ih =>
    intro K hK hk
    by_cases hu : K = Finset.univ
    · exact ⟨[], by simp, by rw [pre_nil, hu]⟩
    · obtain ⟨w, hwl, hcard, hP⟩ := hstep K hK hu
      obtain ⟨u, hul, hu'⟩ := ih (A.pre K w) hP (by have := Finset.card_le_univ (A.pre K w); omega)
      refine ⟨u ++ w, ?_, by rw [pre_append, hu']⟩
      rw [List.length_append, show (k + 1) * L = k * L + L by ring]
      exact Nat.add_le_add hul hwl

omit [Fintype S] in
/-- A set `{r} w⁻¹ = Q` gives a reset word. -/
theorem sec4_reset_of_pre {r : Q} {w : List S} (h : A.pre {r} w = Finset.univ) : A.IsReset w :=
  ⟨r, fun q => by
    have hq : q ∈ A.pre {r} w := by rw [h]; exact Finset.mem_univ q
    rw [mem_pre, Finset.mem_singleton] at hq
    exact hq⟩

omit [Fintype Q] [DecidableEq Q] in
theorem sec4_wt_one (K : Finset Q) : wt (fun _ : Q => (1 : ℝ)) K = K.card := by
  simp [wt]

theorem thm_4_1_case_z1_core (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) (hz : A.zLoop W.p x = 1) :
    0 < A.yIn W.E W.p x ∧ A.inW W.p x = 1 + A.yIn W.E W.p x ∧ A.inW W.p W.s = 1 - A.yIn W.E W.p x ∧
      (∀ T : Finset Q, x ∈ T → ∑ b, W.p b * ((A.pre T [b]).card : ℝ) = T.card + A.yIn W.E W.p x * (1 - ein W.s T) ∧
        (T.card : ℝ) ≤ ∑ b, W.p b * ((A.pre T [b]).card : ℝ)) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) := by
  have hxE := sec4_x_not_mem A W hx
  have hsx : W.s ≠ x := fun h => hxE (h ▸ W.s_mem)
  obtain ⟨_, hinx, hins⟩ := sec4_inW_xs_proved A W x hx
  have hfix : ∀ b, A.step x b = x := by
    have h := (sec4_zLoop_lt_one_iff A W x).not.mp (by rw [hz]; exact lt_irrefl 1)
    push Not at h
    exact h
  have hy : 0 < A.yIn W.E W.p x := by
    by_contra hy0
    have hy' : A.yIn W.E W.p x = 0 := le_antisymm (not_lt.mp hy0) (sec4_yIn_nonneg A W x)
    have : Nonempty Q := ⟨x⟩
    exact (sec5_unique_min_closed_proved A hA).1 W.E {x} ⟨W.s, W.s_mem⟩ ⟨x, Finset.mem_singleton_self x⟩
      (sec4_E_closed A W hx hy') (sec4_singleton_closed A hfix) (Finset.disjoint_singleton_right.mpr hxE)
  set y := A.yIn W.E W.p x with hydef
  have hinx' : A.inW W.p x = 1 + y := by rw [hinx, hz]; ring
  have hins' : A.inW W.p W.s = 1 - y := by rw [hins, hz]; ring
  have hinq : ∀ q, A.inW W.p q = 1 + y * (if q = x then 1 else 0) - y * (if q = W.s then 1 else 0) := by
    intro q
    by_cases hqx : q = x
    · subst hqx
      simp [hinx', Ne.symm hsx]
    · by_cases hqs : q = W.s
      · subst hqs
        simp [hins', hsx]
      · have hqE : q ∈ W.E := by
          by_contra hq
          exact hqx (sec4_eq_x_of_not_mem A W hx hq)
        simp [W.inW_one q hqE hqs, hqx, hqs]
  have hsumT : ∀ T : Finset Q, x ∈ T →
      ∑ b, W.p b * ((A.pre T [b]).card : ℝ) = T.card + y * (1 - ein W.s T) ∧
        (T.card : ℝ) ≤ ∑ b, W.p b * ((A.pre T [b]).card : ℝ) := by
    intro T hxT
    have heq : ∑ b, W.p b * ((A.pre T [b]).card : ℝ) = T.card + y * (1 - ein W.s T) := by
      rw [sec4_sum_pre_eq A W.p T, Finset.sum_congr rfl (fun q _ => hinq q)]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
        hxT, ein, Finset.sum_const, nsmul_eq_mul, mul_one]
      split_ifs <;> ring
    refine ⟨heq, ?_⟩
    rw [heq]
    have hein : ein W.s T ≤ 1 := by unfold ein; split_ifs <;> norm_num
    nlinarith
  refine ⟨hy, hinx', hins', hsumT, ?_⟩
  -- the chain of enlargements from `{x} c⁻¹`
  have hstep : ∀ K, x ∈ K → K ≠ Finset.univ →
      ∃ w : List S, w.length ≤ Fintype.card Q - 1 ∧ K.card < (A.pre K w).card ∧ x ∈ A.pre K w := by
    intro K hxK hKu
    have hKlt : K.card < Fintype.card Q := by
      rw [← Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hKu)
    have hQ : wt (fun _ : Q => (1 : ℝ)) Finset.univ ≠ 0 := by
      rw [sec4_wt_one, Finset.card_univ]
      exact_mod_cast (show Fintype.card Q ≠ 0 by omega)
    have hK0 : wt (fun _ : Q => (1 : ℝ)) K ≠ 0 := by
      rw [sec4_wt_one]
      exact_mod_cast (Finset.card_pos.mpr ⟨x, hxK⟩).ne'
    have hK1 : wt (fun _ : Q => (1 : ℝ)) K ≠ wt (fun _ : Q => (1 : ℝ)) Finset.univ := by
      rw [sec4_wt_one, sec4_wt_one, Finset.card_univ]
      exact_mod_cast hKlt.ne
    obtain ⟨_, hle⟩ := lem_2_2_a_proved A hA _ K hQ hK0 hK1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, A.cost (fun _ => (1 : ℝ)) K = m :=
      ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle)).symm⟩
    have hxv : ∀ v : List S, A.act x v = x := fun v =>
      Automaton.act_mem_of_closed A (fun q => q = x) (fun q hq b => by rw [hq]; exact hfix b) v x rfl
    have havg : ∀ v : List S, v.length = m - 1 →
        wt (fun _ => (1 : ℝ)) (A.pre K v) ≤ ∑ b, W.p b * wt (fun _ => (1 : ℝ)) (A.pre (A.pre K v) [b]) := by
      intro v _
      have hxKv : x ∈ A.pre K v := by rw [mem_pre, hxv v]; exact hxK
      simp only [sec4_wt_one]
      exact (hsumT (A.pre K v) hxKv).2
    obtain ⟨w, hwl, hraise⟩ := lem_2_2_b_proved A hA _ K hQ hK0 hK1 m hm W.p W.weights havg
    refine ⟨w, ?_, ?_, by rw [mem_pre, hxv w]; exact hxK⟩
    · rw [hwl]
      rw [hm] at hle
      exact_mod_cast hle
    · have h := hraise
      unfold Automaton.Raises at h
      rw [sec4_wt_one, sec4_wt_one] at h
      exact_mod_cast h
  obtain ⟨q₀, hq₀E, c, hq₀c⟩ := (sec4_yIn_pos_iff A W x).mp hy
  have hq₀x : q₀ ≠ x := fun h => hxE (h ▸ hq₀E)
  have hxK₀ : x ∈ A.pre {x} [c] := by simp [hfix c]
  have hq₀K₀ : q₀ ∈ A.pre {x} [c] := by simp [hq₀c]
  have hK₀card : 2 ≤ (A.pre {x} [c]).card := Finset.one_lt_card.mpr ⟨x, hxK₀, q₀, hq₀K₀, hq₀x.symm⟩
  obtain ⟨u, hul, hu⟩ := sec4_chain A (fun K => x ∈ K) (Fintype.card Q - 1) hstep (Fintype.card Q - 2)
    (A.pre {x} [c]) hxK₀ (by omega)
  have hreset : A.IsReset (u ++ [c]) := sec4_reset_of_pre A (r := x) (by rw [pre_append]; exact hu)
  calc A.rt ≤ ((u ++ [c]).length : ℕ∞) := minLen_le_length hreset
    _ ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) := by
      rw [List.length_append, List.length_singleton]
      have h : u.length + 1 ≤ 1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) := by
        rw [Nat.add_comm]
        exact Nat.add_le_add_left hul 1
      exact_mod_cast h

/-! ### Theorem 4.1 (tex:501-547) and the automata that are not strongly connected (tex:135) -/

theorem sec4_exists_x (W : QEWitness A 1) (hn : 2 ≤ Fintype.card Q) : ∃ x, W.X = {x} := by
  apply Finset.card_eq_one.mp
  unfold QEWitness.X
  rw [Finset.card_univ_sdiff, W.card_E]
  omega

theorem thm_4_1_core (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (hqe : QuasiEulerian A 1) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  obtain ⟨W⟩ := hqe
  obtain ⟨x, hx⟩ := sec4_exists_x A W hn
  have ht1 : ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) ≤
      (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
    exact_mod_cast sec4_arith_t1 hn
  by_cases hz : A.zLoop W.p x < 1
  · by_cases hy : 0 < A.yIn W.E W.p x
    · exact (thm_4_1_case_sc_core A hA hn W x hx).1 hz hy
    · have hy0 : A.yIn W.E W.p x = 0 := le_antisymm (not_lt.mp hy) (sec4_yIn_nonneg A W x)
      obtain ⟨_, _, _, _, h⟩ := thm_4_1_case_y0_core A hA hn W x hx hz hy0
      exact h.trans ht1
  · have hz1 : A.zLoop W.p x = 1 := le_antisymm (sec4_zLoop_le_one A W x) (not_lt.mp hz)
    exact (thm_4_1_case_z1_core A hA hn W x hx hz1).2.2.2.2.trans ht1

theorem intro_deg1_nonsc_core (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) (hsc : ¬ A.StronglyConnected) :
    ((∀ b, A.step x b = x) ∨ A.IsClosed W.E) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) := by
  have hiff := (thm_4_1_case_sc_core A hA hn W x hx).2
  by_cases hz : A.zLoop W.p x < 1
  · have hy0 : A.yIn W.E W.p x = 0 := by
      refine le_antisymm ?_ (sec4_yIn_nonneg A W x)
      by_contra hy
      exact hsc (hiff.mpr ⟨hz, not_le.mp hy⟩)
    obtain ⟨hE, _, _, _, h⟩ := thm_4_1_case_y0_core A hA hn W x hx hz hy0
    exact ⟨Or.inr hE, h⟩
  · have hz1 : A.zLoop W.p x = 1 := le_antisymm (sec4_zLoop_le_one A W x) (not_lt.mp hz)
    have hfix : ∀ b, A.step x b = x := by
      have h := (sec4_zLoop_lt_one_iff A W x).not.mp hz
      push Not at h
      exact h
    exact ⟨Or.inl hfix, (thm_4_1_case_z1_core A hA hn W x hx hz1).2.2.2.2⟩

end Degree1

/-! ### `C_n` is synchronizing; the bound is attained (tex:545-547) -/

section CernyAttained

open Fin.NatCast

theorem sec4_cn_act_b (n : ℕ) [NeZero n] :
    ∀ (j : ℕ) (q : Fin n), (cerny n).act q (List.replicate j 1) = q + (j : Fin n)
  | 0, q => by rw [Nat.cast_zero, add_zero]; rfl
  | j + 1, q => by
    show (cerny n).act ((cerny n).step q 1) (List.replicate j 1) = q + ((j + 1 : ℕ) : Fin n)
    rw [sec4_cn_act_b n j, sec4_cn_step_b, Nat.cast_succ]
    abel

theorem sec4_cn_mem_pre_b {n : ℕ} [NeZero n] (K : Finset (Fin n)) (j : ℕ) (q : Fin n) :
    q ∈ (cerny n).pre K (List.replicate j 1) ↔ q + (j : Fin n) ∈ K := by
  rw [mem_pre, sec4_cn_act_b]

theorem sec4_cn_card_pre_b {n : ℕ} [NeZero n] (K : Finset (Fin n)) (j : ℕ) :
    ((cerny n).pre K (List.replicate j 1)).card = K.card := by
  apply Finset.card_bij (fun q _ => q + (j : Fin n))
  · intro q hq
    exact (sec4_cn_mem_pre_b K j q).mp hq
  · intro q _ q' _ h
    exact add_right_cancel h
  · intro k hk
    exact ⟨k - (j : Fin n), (sec4_cn_mem_pre_b K j _).mpr (by rw [sub_add_cancel]; exact hk),
      sub_add_cancel k (j : Fin n)⟩

theorem sec4_cn_boundary {n : ℕ} [NeZero n] {K : Finset (Fin n)} (hne : K.Nonempty) (hu : K ≠ Finset.univ) :
    ∃ q ∈ K, q - 1 ∉ K := by
  by_contra hno
  push Not at hno
  obtain ⟨q, hq⟩ := hne
  have hall : ∀ k : ℕ, q - (k : Fin n) ∈ K := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      have h := hno _ ih
      rwa [Nat.cast_succ, ← sub_sub]
  apply hu
  apply Finset.eq_univ_of_forall
  intro r
  have h := hall (q - r).val
  rwa [Fin.cast_val_eq_self, sub_sub_cancel] at h

/-- Every nonempty proper set of `C_n` is enlarged by a word `a b^j` with `j < n`. -/
theorem sec4_cn_enlarge {n : ℕ} [NeZero n] (K : Finset (Fin n)) (hne : K.Nonempty) (hu : K ≠ Finset.univ) :
    ∃ w : List (Fin 2), w.length ≤ n ∧ K.card < ((cerny n).pre K w).card := by
  obtain ⟨q, hqK, hq1⟩ := sec4_cn_boundary hne hu
  have hjcast : (((q - 1).val : ℕ) : Fin n) = q - 1 := Fin.cast_val_eq_self _
  have h1 : (1 : Fin n) ∈ (cerny n).pre K (List.replicate (q - 1).val 1) := by
    rw [sec4_cn_mem_pre_b, hjcast, show (1 : Fin n) + (q - 1) = q by abel]
    exact hqK
  have h0 : (0 : Fin n) ∉ (cerny n).pre K (List.replicate (q - 1).val 1) := by
    rw [sec4_cn_mem_pre_b, hjcast, zero_add]
    exact hq1
  refine ⟨[0] ++ List.replicate (q - 1).val 1, ?_, ?_⟩
  · rw [List.length_append, List.length_singleton, List.length_replicate]
    have := (q - 1).isLt
    omega
  · rw [pre_append]
    set K' := (cerny n).pre K (List.replicate (q - 1).val 1) with hK'
    have hsub : insert 0 K' ⊆ (cerny n).pre K' [0] := by
      intro r hr
      rw [Finset.mem_insert] at hr
      rw [mem_pre, act_singleton]
      rcases hr with rfl | hr
      · rw [sec4_cn_step_a0]
        exact h1
      · have hr0 : r ≠ 0 := fun h => h0 (h ▸ hr)
        rw [sec4_cn_step_a hr0]
        exact hr
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem h0] at hcard
    have hK'card : K'.card = K.card := sec4_cn_card_pre_b K _
    omega

theorem sec4_cn_sync (n : ℕ) [NeZero n] : (cerny n).Synchronizing := by
  obtain ⟨u, _, hu⟩ := sec4_chain (cerny n) (fun K => K.Nonempty) n
    (fun K hK hKu => by
      obtain ⟨w, hwl, hcard⟩ := sec4_cn_enlarge K hK hKu
      exact ⟨w, hwl, hcard, Finset.card_pos.mp (by omega)⟩) (n - 1) {0} (Finset.singleton_nonempty 0)
    (by rw [Finset.card_singleton, Fintype.card_fin])
  exact ⟨u, sec4_reset_of_pre (cerny n) hu⟩

theorem sec4_half_weights : IsLetterWeights (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
  refine ⟨fun _ => by norm_num, ?_⟩
  rw [Fin.sum_univ_two]
  norm_num

theorem sec4_cn_qe (n : ℕ) [NeZero n] (hn : 2 ≤ n) : QuasiEulerian (cerny n) 1 := by
  obtain ⟨W, _⟩ := thm_4_1_cn_witness_core n hn _ sec4_half_weights
  exact ⟨W⟩

theorem intro_rt_cerny_core (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (cerny n).rt = (((n - 1) ^ 2 : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ (cerny_rt_ge n hn)
  have h := thm_4_1_core (cerny n) (sec4_cn_sync n) (by rw [Fintype.card_fin]; exact hn) (sec4_cn_qe n hn)
  rwa [Fintype.card_fin] at h

theorem thm_4_1_attained_core (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (cerny n).Synchronizing ∧ QuasiEulerian (cerny n) 1 ∧ (cerny n).rt = (((n - 1) ^ 2 : ℕ) : ℕ∞) :=
  ⟨sec4_cn_sync n, sec4_cn_qe n hn, intro_rt_cerny_core n hn⟩

theorem sec4_arith_attained {n : ℕ} (hn : 2 ≤ n) : (n - 1) ^ 2 = 1 + (n - 2) * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  ring

theorem rem_4_3_attained_core (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (cerny n).rt = ((1 + (n - 2) * n : ℕ) : ℕ∞) := by
  rw [intro_rt_cerny_core n hn, sec4_arith_attained hn]

/-! ### Remark 4.3: the shape of every chain of extensions of `C_n` (tex:551-556) -/

theorem sec4_cn_K0 (n : ℕ) [NeZero n] : (cerny n).pre {1} [0] = {0, 1} := by
  ext q
  simp only [mem_pre, act_singleton, Finset.mem_singleton, Finset.mem_insert]
  by_cases hq : q = 0
  · subst hq
    simp [sec4_cn_step_a0]
  · rw [sec4_cn_step_a hq]
    simp [hq]

theorem sec4_flatten_succ {α : Type*} (w : ℕ → List α) (j : ℕ) :
    ((List.range (j + 1)).reverse.map w).flatten = w j ++ ((List.range j).reverse.map w).flatten := by
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons,
    List.flatten_cons]

/-- For the weights `(1/2, 1/2)`, the vector `alphaOff 0 (1/2)` is stationary for `C_n` (Lemma 4.2, `t = p_b`). -/
theorem sec4_cn_stat (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (cerny n).IsStationary (fun _ => 1 / 2) (alphaOff 0 (1 / 2)) := by
  obtain ⟨W, hWE, _, hWp⟩ := thm_4_1_cn_witness_core n hn _ sec4_half_weights
  have hWX : W.X = {0} := by
    ext q
    simp [QEWitness.X, hWE]
  have hzyt := rem_4_3_cn_zyt_core n hn _ sec4_half_weights
  have hz : (cerny n).zLoop W.p 0 < 1 := by
    rw [hWp, hzyt.1]
    norm_num
  have hstat := lem_4_2_proved (cerny n) W 0 hWX hz
  have halpha : (cerny n).alphaDeg1 W.E W.p 0 = alphaOff 0 (1 / 2) := by
    funext q
    simp only [Automaton.alphaDeg1, alphaOff, hWE, hWp, hzyt.2.2.1]
  rwa [halpha, hWp] at hstat

theorem rem_4_3_chain_core (n : ℕ) [NeZero n] (hn : 2 ≤ n) (K : ℕ → Finset (Fin n)) (w : ℕ → List (Fin 2))
    (J : ℕ) (hK0 : K 0 = {0, 1})
    (hstep : ∀ j < J, K j ≠ Finset.univ ∧ K (j + 1) = (cerny n).pre (K j) (w j) ∧
      ((w j).length : ℕ∞) = (cerny n).ext (K j) ∧ (K j).card < (K (j + 1)).card)
    (hJ : K J = Finset.univ) :
    (cerny n).IsReset ((((List.range J).reverse.map w).flatten) ++ [0]) ∧ J = n - 2 ∧
      ∀ j < J, (w j).length = n ∧ (K (j + 1)).card = (K j).card + 1 := by
  -- the word read so far: `w_{j-1} ⋯ w_0`
  have hpre : ∀ j ≤ J, (cerny n).pre (K 0) ((List.range j).reverse.map w).flatten = K j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [sec4_flatten_succ, pre_append, ih (by omega)]
      exact (hstep j (by omega)).2.1.symm
  have hlen : ∀ j, (((List.range j).reverse.map w).flatten).length = ∑ i ∈ Finset.range j, (w i).length := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [sec4_flatten_succ, List.length_append, ih, Finset.sum_range_succ, Nat.add_comm]
  have hreset : (cerny n).IsReset ((((List.range J).reverse.map w).flatten) ++ [0]) :=
    sec4_reset_of_pre (cerny n) (r := 1) (by rw [pre_append, sec4_cn_K0, ← hK0, hpre J le_rfl, hJ])
  -- sizes: `|K_0| = 2`, each step adds at least one state
  have hcard0 : (K 0).card = 2 := by
    rw [hK0]
    exact Finset.card_pair (sec4_cn_one_ne_zero n hn).symm
  have hge : ∀ j ≤ J, 2 + j ≤ (K j).card := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih =>
      intro hj
      have h1 := (hstep j (by omega)).2.2.2
      have h2 := ih (by omega)
      omega
  have hJn : 2 + J ≤ n := by
    have h := hge J le_rfl
    rwa [hJ, Finset.card_univ, Fintype.card_fin] at h
  -- each extension has length at most `n` (Proposition 3.3 with `t = p_b = 1/2`)
  have hext : ∀ j < J, (w j).length ≤ n := by
    intro j hj
    obtain ⟨hu, -, hl, -⟩ := hstep j hj
    have hne : (K j).Nonempty := Finset.card_pos.mp (by have := hge j hj.le; omega)
    have h := (prop_3_3_proved (cerny n) (sec4_cn_sync n) (by rw [Fintype.card_fin]; exact hn) _
      sec4_half_weights 0 (1 / 2) (sec4_cn_stat n hn) (by norm_num) (by norm_num) (by norm_num) (K j) hne hu).1
    rw [← hl, Fintype.card_fin] at h
    exact_mod_cast h
  -- the lower bound `(n-1)^2 = 1 + (n-2) n` forces equality everywhere
  have hlow := cerny_reset_length_ge n hn _ hreset
  rw [List.length_append, List.length_singleton, hlen J, sec4_arith_attained hn] at hlow
  have hsum_le : ∑ i ∈ Finset.range J, (w i).length ≤ ∑ _i ∈ Finset.range J, n :=
    Finset.sum_le_sum (fun i hi => hext i (Finset.mem_range.mp hi))
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum_le
  have hmul : (n - 2) * n ≤ J * n := by linarith
  have hJeq : J = n - 2 := by
    have := Nat.le_of_mul_le_mul_right hmul (by omega : 0 < n)
    omega
  have hlen_all : ∀ j < J, (w j).length = n := by
    have heq : ∑ i ∈ Finset.range J, (w i).length = ∑ _i ∈ Finset.range J, n := by
      apply le_antisymm (Finset.sum_le_sum (fun i hi => hext i (Finset.mem_range.mp hi)))
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hJn' : J * n = (n - 2) * n := by rw [hJeq]
      linarith
    intro j hj
    exact (Finset.sum_eq_sum_iff_of_le (fun i hi => hext i (Finset.mem_range.mp hi))).mp heq j
      (Finset.mem_range.mpr hj)
  -- each step adds exactly one state (telescoping in `ℤ`)
  have htel : ∑ i ∈ Finset.range J, (((K (i + 1)).card : ℤ) - (K i).card) = (K J).card - (K 0).card :=
    Finset.sum_range_sub (fun i => ((K i).card : ℤ)) J
  rw [hJ, Finset.card_univ, Fintype.card_fin, hcard0] at htel
  have hd : ∀ i ∈ Finset.range J, (1 : ℤ) ≤ ((K (i + 1)).card : ℤ) - (K i).card := by
    intro i hi
    have := (hstep i (Finset.mem_range.mp hi)).2.2.2
    omega
  have hsum1 : ∑ _i ∈ Finset.range J, (1 : ℤ) = ∑ i ∈ Finset.range J, (((K (i + 1)).card : ℤ) - (K i).card) := by
    rw [htel, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    omega
  refine ⟨hreset, hJeq, fun j hj => ⟨hlen_all j hj, ?_⟩⟩
  have h := (Finset.sum_eq_sum_iff_of_le hd).mp hsum1 j (Finset.mem_range.mpr hj)
  omega

end CernyAttained

end CernyQE
