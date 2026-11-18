/-
CernyQE/Proofs/Sec5x.lean — Remark 5.4, Theorem 5.1 (automata that are not strongly connected) and Proposition 5.6.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Proofs.Basic
import CernyQE.Proofs.Rows2
import CernyQE.Proofs.Sec51
import CernyQE.Proofs.Stationary
import CernyQE.Proofs.Thm31

namespace CernyQE

open Classical Automaton Matrix

universe u v

set_option linter.unusedSectionVars false

namespace Sec5x

/-! ### Helpers for Section 5.1 -/

section Helpers51

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- `in_p(r) = ∑_b p_b |{q : q.b = r}|`, written with indicators. -/
theorem inW_eq_ind (p : S → ℝ) (r : Q) :
    A.inW p r = ∑ b, p b * ∑ q, (if A.step q b = r then (1 : ℝ) else 0) := by
  simp only [Automaton.inW]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [Automaton.pre, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Automaton.act]

/-- The converse weight count: every edge that ends in a closed set `T ⊆ E \ {s}` starts in `T` (the in-weights on
`T` add up to `|T|`, and the edges from `T` already carry the weight `|T|`). -/
theorem in_closed {d : ℕ} (W : QEWitness A d) (T : Finset Q) (hT : T ⊆ W.E.erase W.s) (hcl : A.IsClosed T) :
    ∀ q b, A.step q b ∈ T → q ∈ T := by
  have hp := W.weights
  let gap : S → Q → ℝ := fun b q => (if A.step q b ∈ T then 1 else 0) - (if q ∈ T then 1 else 0)
  have hgap0 : ∀ b q, 0 ≤ gap b q := by
    intro b q
    simp only [gap]
    by_cases h2 : q ∈ T
    · simp [h2, hcl q h2 b]
    · by_cases h1 : A.step q b ∈ T <;> simp [h1, h2]
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
  intro q b hqb
  have hb := hterm b (Finset.mem_univ b)
  have hsum0 : ∑ q, gap b q = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact absurd h (hp.1 b).ne'
    · exact h
  have hq0 := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hgap0 b q).mp hsum0 q (Finset.mem_univ q)
  by_contra hq
  simp [gap, hq, hqb] at hq0

/-- A path from outside `C` into `C` has an edge from outside `C` into `C`. -/
theorem exists_edge_into (C : Finset Q) :
    ∀ (w : List S) (q : Q), q ∉ C → A.act q w ∈ C → ∃ q' b, q' ∉ C ∧ A.step q' b ∈ C
  | [], _, hq, h => absurd h hq
  | b :: w, q, hq, h => by
    by_cases hb : A.step q b ∈ C
    · exact ⟨q, b, hq, hb⟩
    · exact exists_edge_into C w (A.step q b) hb h

/-- The preimages of a state under a letter are the same in `A|_C` and in `A` when they all lie in `C`. -/
theorem restrict_pre_card (C : Finset Q) (hC : A.IsClosed C) (r : C) (b : S)
    (hpred : ∀ q, A.step q b = r.1 → q ∈ C) :
    ((A.restrict C hC).pre {r} [b]).card = (A.pre {r.1} [b]).card := by
  rw [← Finset.card_map (Function.Embedding.subtype (· ∈ C))]
  congr 1
  ext q
  simp only [Finset.mem_map, Function.Embedding.coe_subtype, mem_pre, act_singleton, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact congrArg Subtype.val hx
  · intro hq
    exact ⟨⟨q, hpred q hq⟩, Subtype.ext hq, rfl⟩

/-- Case `s ∈ C` (tex:600-603): the set `T = R ∩ (E \ {s})` is empty, so `R ⊆ X`. -/
theorem R_sub_X (hA : A.Synchronizing) {d : ℕ} (W : QEWitness A d) (C : Finset Q) (hmin : A.IsMinClosed C)
    (hsC : W.s ∈ C) : Finset.univ \ C ⊆ W.X := by
  have : Nonempty Q := ⟨W.s⟩
  let T : Finset Q := (W.E.erase W.s).filter (fun q => q ∉ C)
  have hTsub : T ⊆ W.E.erase W.s := Finset.filter_subset _ _
  have hTC : ∀ q ∈ T, q ∉ C := fun q hq => (Finset.mem_filter.mp hq).2
  have hin : ∀ q b, A.step q b ∈ T → q ∈ T := by
    intro q b hqb
    have hqbE := Finset.mem_of_mem_erase (hTsub hqb)
    have hqbs := Finset.ne_of_mem_erase (hTsub hqb)
    have hqC : q ∉ C := fun hq => hTC _ hqb (hmin.2.1 q hq b)
    have hqE : q ∈ W.E := by
      by_contra hqE
      rcases W.edge_X q hqE b with h | h
      · exact h hqbE
      · exact hqbs h
    have hqs : q ≠ W.s := fun h => hqC (by rw [h]; exact hsC)
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hqs, hqE⟩, hqC⟩
  have hTe : ¬ T.Nonempty := by
    intro hne
    have hTcl := lem_5_2_proved A W T hTsub hne hin
    apply (sec5_unique_min_closed_proved A hA).1 C T hmin.1 hne hmin.2.1 hTcl
    exact Finset.disjoint_left.mpr fun q hqC hqT => hTC q hqT hqC
  intro q hq
  have hqC : q ∉ C := (Finset.mem_sdiff.mp hq).2
  show q ∈ Finset.univ \ W.E
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, fun hqE => hTe ⟨q, ?_⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h => hqC (by rw [h]; exact hsC), hqE⟩, hqC⟩

/-- Case `s ∉ C` (tex:620-624): `C ⊆ X`. -/
theorem C_sub_X {d : ℕ} (W : QEWitness A d) (C : Finset Q) (hmin : A.IsMinClosed C) (hsC : W.s ∉ C)
    (hreach : ∀ q, ∃ w, A.act q w ∈ C) (hRne : (Finset.univ \ C).Nonempty) : C ⊆ W.X := by
  have hC := hmin.2.1
  by_cases hXC : (W.X ∩ C).Nonempty
  · have hcl : A.IsClosed (W.X ∩ C) := by
      intro q hq b
      obtain ⟨hqX, hqC⟩ := Finset.mem_inter.mp hq
      have hqE : q ∉ W.E := (Finset.mem_sdiff.mp hqX).2
      have hbC := hC q hqC b
      refine Finset.mem_inter.mpr ⟨?_, hbC⟩
      rcases W.edge_X q hqE b with h | h
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩
      · exact absurd (by rw [← h]; exact hbC) hsC
    have heq := hmin.2.2 _ hXC hcl Finset.inter_subset_right
    intro q hq
    have hq' : q ∈ W.X ∩ C := by rw [heq]; exact hq
    exact (Finset.mem_inter.mp hq').1
  · exfalso
    have hCE : C ⊆ W.E.erase W.s := by
      intro q hq
      refine Finset.mem_erase.mpr ⟨fun h => hsC (by rw [← h]; exact hq), ?_⟩
      by_contra hqE
      exact hXC ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hqE⟩, hq⟩⟩
    have hin := in_closed A W C hCE hC
    obtain ⟨q0, hq0⟩ := hRne
    have hq0C : q0 ∉ C := (Finset.mem_sdiff.mp hq0).2
    obtain ⟨w, hw⟩ := hreach q0
    obtain ⟨q', b, hq', hb⟩ := exists_edge_into A C w q0 hq0C hw
    exact hq' (hin q' b hb)

/-- Case `s ∈ C` (tex:603-606, tex:626): `(E, s, p)` restricted to `C` is a witness of degree `d - |R|`. -/
theorem qe_restrict {d : ℕ} (W : QEWitness A d) (C : Finset Q) (hC : A.IsClosed C) (hsC : W.s ∈ C)
    (hRX : Finset.univ \ C ⊆ W.X) : QuasiEulerian (A.restrict C hC) (d - (Finset.univ \ C).card) := by
  have hEC : W.E ⊆ C := by
    intro q hqE
    by_contra hqC
    have h := hRX (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hqC⟩)
    exact (Finset.mem_sdiff.mp h).2 hqE
  have hpredE : ∀ q b, A.step q b ∈ W.E → A.step q b ≠ W.s → q ∈ W.E := by
    intro q b h1 h2
    by_contra hq
    rcases W.edge_X q hq b with h | h
    · exact h h1
    · exact h2 h
  let E' : Finset C := Finset.univ.filter (fun q => q.1 ∈ W.E)
  have hE'map : E'.map (Function.Embedding.subtype (· ∈ C)) = W.E := by
    ext q
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype, E']
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hq
      exact ⟨⟨q, hEC hq⟩, hq, rfl⟩
  have hE'card : E'.card = W.E.card := by rw [← hE'map, Finset.card_map]
  refine ⟨⟨E', ⟨W.s, hsC⟩, W.p, ?_, ?_, W.weights, ?_, ?_⟩⟩
  · have hXcard : (Finset.univ \ C).card ≤ W.X.card := Finset.card_le_card hRX
    have hX : W.X.card = Fintype.card Q - W.E.card := Finset.card_univ_sdiff W.E
    have hR : (Finset.univ \ C).card = Fintype.card Q - C.card := Finset.card_univ_sdiff C
    have hE1 : 1 ≤ W.E.card := Finset.card_pos.mpr ⟨W.s, W.s_mem⟩
    have hCle := Finset.card_le_univ C
    have hcC : Fintype.card C = C.card := Fintype.card_coe C
    have hEd := W.card_E
    omega
  · simp [E', W.s_mem]
  · intro q hq b
    have hqE : q.1 ∉ W.E := by simpa [E'] using hq
    rcases W.edge_X q.1 hqE b with h | h
    · left
      simpa [E', Automaton.restrict] using h
    · right
      exact Subtype.ext h
  · intro r hr hrs
    have hrE : r.1 ∈ W.E := by simpa [E'] using hr
    have hrs' : r.1 ≠ W.s := fun h => hrs (Subtype.ext h)
    have key : (A.restrict C hC).inW W.p r = A.inW W.p r.1 := by
      simp only [Automaton.inW]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [restrict_pre_card A C hC r b fun q hq =>
        hEC (hpredE q b (by rw [hq]; exact hrE) (by rw [hq]; exact hrs'))]
    rw [key]
    exact W.inW_one r.1 hrE hrs'

/-- An automaton with one state has the empty reset word. -/
theorem rt_le_zero (hA : A.Synchronizing) (h1 : Fintype.card Q ≤ 1) : A.rt ≤ ((0 : ℕ) : ℕ∞) := by
  obtain ⟨w, r, hr⟩ := hA
  have hreset : A.IsReset [] := ⟨r, fun q => Fintype.card_le_one_iff.mp h1 q r⟩
  exact (minLen_le_length hreset).trans (by simp)

/-- The Cerny bound for synchronizing automata with at most two states. -/
theorem small_rt (hA : A.Synchronizing) (h2 : Fintype.card Q ≤ 2) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  have hpos : 0 < Fintype.card Q := by
    obtain ⟨w, r, -⟩ := hA
    exact Fintype.card_pos_iff.mpr ⟨r⟩
  rcases (by omega : Fintype.card Q = 1 ∨ Fintype.card Q = 2) with h | h
  · have h0 := rt_le_zero A hA h.le
    rw [h]
    simpa using h0
  · rw [sec5_two_state_rt_proved A hA h, h]
    norm_num

/-- Degree zero: `1` is a positive stationary vector (all in-weights are one), and Theorem 3.1 applies. -/
theorem qe0_rt (hqe : QuasiEulerian A 0) (hA : A.Synchronizing) (h2 : 2 ≤ Fintype.card Q) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  obtain ⟨W⟩ := hqe
  have : Nonempty Q := ⟨W.s⟩
  have hE : W.E = Finset.univ := Finset.eq_univ_of_card _ (by rw [W.card_E]; simp)
  have hrest : ∀ r, r ≠ W.s → A.inW W.p r = 1 := fun r hr =>
    W.inW_one r (by rw [hE]; exact Finset.mem_univ r) hr
  have htot := sec2_inW_sum_proved A W.p W.weights
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ W.s)] at htot
  have hsum : ∑ q ∈ Finset.univ.erase W.s, A.inW W.p q = ((Finset.univ.erase W.s).card : ℝ) := by
    rw [Finset.sum_congr rfl fun q hq => hrest q (Finset.ne_of_mem_erase hq)]
    simp
  have hcard : ((Finset.univ.erase W.s).card : ℝ) + 1 = Fintype.card Q := by
    have h := Finset.card_erase_add_one (Finset.mem_univ W.s)
    rw [Finset.card_univ] at h
    exact_mod_cast h
  have hs : A.inW W.p W.s = 1 := by
    rw [hsum] at htot
    linarith
  have hst : A.IsStationary W.p (fun _ => 1) := (sec2_one_stationary_iff_proved A W.p W.weights).mpr
    fun q => if h : q = W.s then by rw [h]; exact hs else hrest q h
  exact thm_3_1_proved A hA h2 W.p W.weights _ hst (fun _ => one_pos) W.s (fun _ _ _ _ => rfl)

/-- Lemma 5.3 and `r^2 + (n-1-r)^2 ≤ (n-1)^2` (tex:613-614): the bound for `A|_C` gives the bound for `A`. -/
theorem combine (hA : A.Synchronizing) (C : Finset Q) (hne : C.Nonempty) (hC : A.IsClosed C)
    (hb : (A.restrict C hC).rt ≤ (((Fintype.card C - 1) ^ 2 : ℕ) : ℕ∞)) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  have h53 := lem_5_3_proved A hA C hne hC
  rw [Fintype.card_coe] at hb
  have hR : (Finset.univ \ C).card = Fintype.card Q - C.card := Finset.card_univ_sdiff C
  have hc1 : 1 ≤ C.card := Finset.card_pos.mpr hne
  have hcn : C.card ≤ Fintype.card Q := Finset.card_le_univ C
  have harith := arith_r_sq_proved (Fintype.card Q) (Finset.univ \ C).card (by omega)
  have heq : Fintype.card Q - 1 - (Finset.univ \ C).card = C.card - 1 := by omega
  rw [heq] at harith
  calc A.rt ≤ (((Finset.univ \ C).card ^ 2 : ℕ) : ℕ∞) + (A.restrict C hC).rt := h53
    _ ≤ (((Finset.univ \ C).card ^ 2 : ℕ) : ℕ∞) + (((C.card - 1) ^ 2 : ℕ) : ℕ∞) := add_le_add le_rfl hb
    _ = ((((Finset.univ \ C).card ^ 2 + (C.card - 1) ^ 2 : ℕ)) : ℕ∞) := (Nat.cast_add _ _).symm
    _ ≤ _ := by exact_mod_cast harith

end Helpers51

end Sec5x

/-! ### Section 5.1: the rows that do not need Section 4 -/

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- Remark 5.4, tex:624-627: any degree `d`, not strongly connected. -/
theorem rem_5_4_a_proved (hA : A.Synchronizing) {d : ℕ} (W : QEWitness A d) (hsc : ¬ A.StronglyConnected)
    (C : Finset Q) (hmin : A.IsMinClosed C) (hC : A.IsClosed C) :
    (C ⊆ W.X ∨ ((Finset.univ \ C) ⊆ W.X ∧ (A.restrict C hC).StronglyConnected ∧
        (QuasiEulerian (A.restrict C hC) (d - (Finset.univ \ C).card) ∨
          (A.restrict C hC).IsStationary W.p (fun _ => 1)))) ∧
      A.rt ≤ (((Finset.univ \ C).card ^ 2 : ℕ) : ℕ∞) + (A.restrict C hC).rt := by
  refine ⟨?_, lem_5_3_proved A hA C hmin.1 hC⟩
  obtain ⟨hscC, -, hreach, hRne⟩ := sec5_restrict_proved A hA C hmin hC
  by_cases hsC : W.s ∈ C
  · right
    have hRX := Sec5x.R_sub_X A hA W C hmin hsC
    exact ⟨hRX, hscC, Or.inl (Sec5x.qe_restrict A W C hC hsC hRX)⟩
  · left
    exact Sec5x.C_sub_X A W C hmin hsC hreach (hRne hsc)

end General

section Reduction

/-- Remark 5.4, tex:627-630: the Cerny bound for degree `d` automata that are not strongly connected follows from
Theorem 3.1, the bound for strongly connected automata of degree `1, …, d-1`, and the bound for automata with at most
`d` states. -/
theorem rem_5_4_reduction_proved (S : Type v) [Fintype S] (d : ℕ)
    (H1 : ∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), B.Synchronizing →
      B.StronglyConnected → (∃ d', 1 ≤ d' ∧ d' ≤ d - 1 ∧ QuasiEulerian B d') →
      B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞))
    (H2 : ∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), Fintype.card Q' ≤ d →
      B.Synchronizing → B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞))
    (Q : Type u) [Fintype Q] [DecidableEq Q] (A : Automaton Q S) (hA : A.Synchronizing)
    (hqe : QuasiEulerian A d) (hsc : ¬ A.StronglyConnected) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  obtain ⟨W⟩ := hqe
  have : Nonempty Q := ⟨W.s⟩
  obtain ⟨C, ⟨hmin, -⟩, -⟩ := (sec5_unique_min_closed_proved A hA).2.2
  have hC := hmin.2.1
  obtain ⟨-, hsyncC, -, hRne⟩ := sec5_restrict_proved A hA C hmin hC
  apply Sec5x.combine A hA C hmin.1 hC
  have hXd : W.X.card ≤ d := by
    have hX : W.X.card = Fintype.card Q - W.E.card := Finset.card_univ_sdiff W.E
    have hEd := W.card_E
    omega
  have hcardC : Fintype.card C = C.card := Fintype.card_coe C
  by_cases hsmall : Fintype.card C ≤ d
  · exact H2 C (A.restrict C hC) hsmall hsyncC
  · push Not at hsmall
    rcases (rem_5_4_a_proved A hA W hsc C hmin hC).1 with hCX | ⟨hRX, hscC, hqe' | hst⟩
    · exfalso
      have := Finset.card_le_card hCX
      omega
    · have hr1 : 1 ≤ (Finset.univ \ C).card := Finset.card_pos.mpr (hRne hsc)
      have hRd : (Finset.univ \ C).card ≤ d := (Finset.card_le_card hRX).trans hXd
      have h2 : 2 ≤ Fintype.card C := by omega
      by_cases hd0 : d - (Finset.univ \ C).card = 0
      · rw [hd0] at hqe'
        exact Sec5x.qe0_rt _ hqe' hsyncC h2
      · exact H1 C (A.restrict C hC) hsyncC hscC ⟨d - (Finset.univ \ C).card, by omega, by omega, hqe'⟩
    · have hr1 : 1 ≤ (Finset.univ \ C).card := Finset.card_pos.mpr (hRne hsc)
      have hRd : (Finset.univ \ C).card ≤ d := (Finset.card_le_card hRX).trans hXd
      have h2 : 2 ≤ Fintype.card C := by omega
      obtain ⟨c, hc⟩ := hmin.1
      exact thm_3_1_proved (A.restrict C hC) hsyncC h2 W.p W.weights _ hst (fun _ => one_pos) ⟨c, hc⟩
        (fun _ _ _ _ => rfl)

/-- Remark 5.4, tex:630, given Theorem 4.1 (`h41`): for `d ≤ 2` the hypotheses of `rem_5_4_reduction` hold. -/
theorem rem_5_4_d2_of (S : Type v) [Fintype S]
    (h41 : ∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), B.Synchronizing →
        2 ≤ Fintype.card Q' → QuasiEulerian B 1 → B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞))
    (d : ℕ) (hd : d ≤ 2) :
    (∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), B.Synchronizing →
      B.StronglyConnected → (∃ d', 1 ≤ d' ∧ d' ≤ d - 1 ∧ QuasiEulerian B d') →
      B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞)) ∧
    (∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), Fintype.card Q' ≤ d →
      B.Synchronizing → B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞)) := by
  refine ⟨fun Q' _ _ B hB _ hex => ?_, fun Q' _ _ B hcard hB => Sec5x.small_rt B hB (by omega)⟩
  obtain ⟨d', hd1, hd2, hqe⟩ := hex
  have hd' : d' = 1 := by omega
  rw [hd'] at hqe
  have h2 : 2 ≤ Fintype.card Q' := by
    obtain ⟨W⟩ := id hqe
    have hE := W.card_E
    have hE1 : 1 ≤ W.E.card := Finset.card_pos.mpr ⟨W.s, W.s_mem⟩
    omega
  exact h41 Q' B hB h2 hqe

end Reduction

/-- Theorem 5.1, tex:568-571, given Theorem 4.1 (`h41`). -/
theorem thm_5_1_of {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]
    (h41 : ∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), B.Synchronizing →
        2 ≤ Fintype.card Q' → QuasiEulerian B 1 → B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞))
    (A : Automaton Q S) (hA : A.Synchronizing) (_hn : 3 ≤ Fintype.card Q) (d : ℕ) (hd : d ≤ 2)
    (hqe : QuasiEulerian A d) (hsc : ¬ A.StronglyConnected) : A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  have h := rem_5_4_d2_of S h41 d hd
  rem_5_4_reduction_proved S d h.1 h.2 Q A hA hqe hsc

/-! ### Helpers for Section 5.3 (the block quotient) -/

namespace Sec5x

section Helpers53

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)
variable {x₁ x₂ : Q} (h12 : x₁ ≠ x₂)

/-- The block map of the partition into `{x₁, x₂}` and singletons: `x₂ ↦ x₁`, the other states are fixed. -/
def blockMap (q : Q) : {q : Q // q ≠ x₂} :=
  if h : q = x₂ then ⟨x₁, h12⟩ else ⟨q, h⟩

theorem blockMap_of_ne {q : Q} (hq : q ≠ x₂) : blockMap h12 q = ⟨q, hq⟩ := dite_eq_right hq

theorem blockMap_x₂ : blockMap h12 x₂ = ⟨x₁, h12⟩ := dite_eq_left rfl

theorem blockMap_val (D : {q : Q // q ≠ x₂}) : blockMap h12 D.1 = D := blockMap_of_ne h12 D.2

theorem blockMap_pair {z : Q} (hz : z = x₁ ∨ z = x₂) : blockMap h12 z = ⟨x₁, h12⟩ := by
  rcases hz with rfl | rfl
  · exact blockMap_of_ne h12 h12
  · exact blockMap_x₂ h12

theorem pair_mem {a b : Q} (h : ({a, b} : Finset Q) = {x₁, x₂}) :
    (a = x₁ ∨ a = x₂) ∧ (b = x₁ ∨ b = x₂) := by
  have ha : a ∈ ({x₁, x₂} : Finset Q) := by rw [← h]; simp
  have hb : b ∈ ({x₁, x₂} : Finset Q) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  exact ⟨ha, hb⟩

/-- The block map commutes with the letters (the partition is a congruence, tex:666). -/
theorem step_blockMap (hblock : A.IsBlockPair x₁ x₂) (q : Q) (b : S) :
    (A.blockQuot x₁ x₂ h12).step (blockMap h12 q) b = blockMap h12 (A.step q b) := by
  by_cases hq : q = x₂
  · rw [hq, blockMap_x₂]
    show blockMap h12 (A.step x₁ b) = blockMap h12 (A.step x₂ b)
    rcases hblock b with h | h
    · rw [h]
    · rw [blockMap_pair h12 (pair_mem h).1, blockMap_pair h12 (pair_mem h).2]
  · rw [blockMap_of_ne h12 hq]
    rfl

theorem act_blockMap (hblock : A.IsBlockPair x₁ x₂) :
    ∀ (w : List S) (q : Q), (A.blockQuot x₁ x₂ h12).act (blockMap h12 q) w = blockMap h12 (A.act q w)
  | [], _ => rfl
  | b :: w, q => by
    rw [act_cons, act_cons, step_blockMap A h12 hblock]
    exact act_blockMap hblock w (A.step q b)

/-- Every reset word of `A` resets the quotient (tex:667). -/
theorem quot_sync (hblock : A.IsBlockPair x₁ x₂) (hA : A.Synchronizing) :
    (A.blockQuot x₁ x₂ h12).Synchronizing := by
  obtain ⟨w, r, hr⟩ := hA
  refine ⟨w, blockMap h12 r, fun D => ?_⟩
  have h := act_blockMap A h12 hblock w D.1
  rw [blockMap_val] at h
  rw [h, hr]

/-- Some letter merges `x₁` and `x₂`, as otherwise `X` would be closed (tex:668). -/
theorem exists_merge {d : ℕ} (W : QEWitness A d) (hsc : A.StronglyConnected) (hX : W.X = {x₁, x₂})
    (hblock : A.IsBlockPair x₁ x₂) : ∃ c₀, A.step x₁ c₀ = A.step x₂ c₀ := by
  by_contra hne
  push Not at hne
  have hcl : A.IsClosed ({x₁, x₂} : Finset Q) := by
    intro q hq b
    rcases hblock b with h | h
    · exact absurd h (hne b)
    · have hq' : q = x₁ ∨ q = x₂ := by simpa using hq
      rw [← h]
      rcases hq' with hq1 | hq2
      · rw [hq1]
        simp
      · rw [hq2]
        simp
  rcases hsc _ hcl with h | h
  · exact absurd h (Finset.insert_ne_empty _ _)
  · have hs : W.s ∈ W.X := by rw [hX, h]; exact Finset.mem_univ _
    exact (Finset.mem_sdiff.mp hs).2 W.s_mem

/-- `rt(A) ≤ rt(A') + 1` (tex:668-669): a reset word of the quotient followed by a merging letter of `x₁, x₂`. -/
theorem rt_le_quot (hblock : A.IsBlockPair x₁ x₂) {c₀ : S} (hc₀ : A.step x₁ c₀ = A.step x₂ c₀) :
    A.rt ≤ (A.blockQuot x₁ x₂ h12).rt + 1 := by
  by_cases htop : (A.blockQuot x₁ x₂ h12).rt = ⊤
  · rw [htop, top_add]
    exact le_top
  obtain ⟨w, ⟨r', hr'⟩, hwl⟩ := exists_of_minLen_ne_top (P := (A.blockQuot x₁ x₂ h12).IsReset) htop
  have hkey : ∀ z, A.step z c₀ = A.step (blockMap h12 z).1 c₀ := by
    intro z
    by_cases hz : z = x₂
    · rw [hz, blockMap_x₂]
      exact hc₀.symm
    · rw [blockMap_of_ne h12 hz]
  have hreset : A.IsReset (w ++ [c₀]) := by
    refine ⟨A.step r'.1 c₀, fun q => ?_⟩
    rw [act_concat, hkey (A.act q w), ← act_blockMap A h12 hblock w q, hr']
  calc A.rt ≤ ((w ++ [c₀]).length : ℕ∞) := minLen_le_length hreset
    _ = (w.length : ℕ∞) + 1 := by simp
    _ = (A.blockQuot x₁ x₂ h12).rt + 1 := by rw [hwl]; rfl

theorem card_quot : Fintype.card {q : Q // q ≠ x₂} = Fintype.card Q - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

include h12 in
/-- The quotient has `n - 1 ≥ 2` states (`x₁`, `x₂` and `s` are distinct). -/
theorem card_quot_ge_two {d : ℕ} (W : QEWitness A d) (hX : W.X = {x₁, x₂}) :
    2 ≤ Fintype.card {q : Q // q ≠ x₂} := by
  have hx1 : x₁ ∉ W.E := by
    have h : x₁ ∈ W.X := by rw [hX]; simp
    exact (Finset.mem_sdiff.mp h).2
  have hx2 : x₂ ∉ W.E := by
    have h : x₂ ∈ W.X := by rw [hX]; simp
    exact (Finset.mem_sdiff.mp h).2
  have hs1 : W.s ≠ x₁ := fun h => hx1 (by rw [← h]; exact W.s_mem)
  have hs2 : W.s ≠ x₂ := fun h => hx2 (by rw [← h]; exact W.s_mem)
  have h := Fintype.one_lt_card_iff.mpr
    ⟨(⟨x₁, h12⟩ : {q : Q // q ≠ x₂}), ⟨W.s, hs2⟩, fun h => hs1 (congrArg Subtype.val h).symm⟩
  omega

/-- The lumped vector (tex:670): `α'_D = α(D)`, the sum of `α` over the block `D`. -/
noncomputable def lump (α : Q → ℝ) (D : {q : Q // q ≠ x₂}) : ℝ :=
  ∑ q, α q * (if blockMap h12 q = D then 1 else 0)

/-- The weighted matrix of the quotient: `M'(π q, D) = ∑_{q' ∈ D} M(q, q')`. -/
theorem quot_M (hblock : A.IsBlockPair x₁ x₂) (p : S → ℝ) (q : Q) (D : {q : Q // q ≠ x₂}) :
    (A.blockQuot x₁ x₂ h12).M p (blockMap h12 q) D =
      ∑ q', A.M p q q' * (if blockMap h12 q' = D then 1 else 0) := by
  simp only [Automaton.M_apply, step_blockMap A h12 hblock, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (A.step q b)]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

/-- The lumped vector of a stationary vector is stationary for the quotient (tex:670-674). -/
theorem lump_vecMul (hblock : A.IsBlockPair x₁ x₂) (p : S → ℝ) (α : Q → ℝ) (hα : vecMul α (A.M p) = α) :
    vecMul (lump h12 α) ((A.blockQuot x₁ x₂ h12).M p) = lump h12 α := by
  funext D
  have h1 : ∀ q, ∑ D', α q * (if blockMap h12 q = D' then 1 else 0) * (A.blockQuot x₁ x₂ h12).M p D' D =
      α q * ∑ q', A.M p q q' * (if blockMap h12 q' = D then 1 else 0) := by
    intro q
    rw [Finset.sum_eq_single (blockMap h12 q), ← quot_M A h12 hblock]
    · simp
    · intro D' _ hD'
      simp [Ne.symm hD']
    · simp
  calc vecMul (lump h12 α) ((A.blockQuot x₁ x₂ h12).M p) D
      = ∑ D', (∑ q, α q * (if blockMap h12 q = D' then 1 else 0)) * (A.blockQuot x₁ x₂ h12).M p D' D := rfl
    _ = ∑ q, ∑ D', α q * (if blockMap h12 q = D' then 1 else 0) * (A.blockQuot x₁ x₂ h12).M p D' D := by
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
    _ = ∑ q, α q * ∑ q', A.M p q q' * (if blockMap h12 q' = D then 1 else 0) :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ q', (∑ q, α q * A.M p q q') * (if blockMap h12 q' = D then 1 else 0) := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ q', α q' * (if blockMap h12 q' = D then 1 else 0) := by
        refine Finset.sum_congr rfl fun q' _ => ?_
        congr 1
        exact congrFun hα q'
    _ = lump h12 α D := rfl

theorem lump_pos (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (D : {q : Q // q ≠ x₂}) : 0 < lump h12 α D := by
  have hD : blockMap h12 D.1 = D := blockMap_val h12 D
  calc (0 : ℝ) < α D.1 * (if blockMap h12 D.1 = D then 1 else 0) := by
        rw [ite_eq_left hD, mul_one]
        exact hpos _
    _ ≤ lump h12 α D := Finset.single_le_sum (f := fun q => α q * (if blockMap h12 q = D then (1 : ℝ) else 0))
        (fun q _ => mul_nonneg (hpos q).le (by split_ifs <;> norm_num)) (Finset.mem_univ D.1)

/-- Off the block `{x₁, x₂}` the lumped vector of the vector of Lemma 5.5 is `1`. -/
theorem lump_one {d : ℕ} (W : QEWitness A d) (hX : W.X = {x₁, x₂}) (D : {q : Q // q ≠ x₂})
    (hD : D ≠ ⟨x₁, h12⟩) : lump h12 (A.alphaStat W.E W.p) D = 1 := by
  have hD1 : D.1 ≠ x₁ := fun h => hD (Subtype.ext h)
  have hDE : D.1 ∈ W.E := by
    by_contra hDE
    have h : D.1 ∈ W.X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hDE⟩
    rw [hX] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact hD1 h
    · exact D.2 h
  unfold lump
  rw [Finset.sum_eq_single D.1]
  · rw [ite_eq_left (blockMap_val h12 D), mul_one]
    have h : D.1 ∉ Finset.univ \ W.E := fun h => (Finset.mem_sdiff.mp h).2 hDE
    simp [Automaton.alphaStat, h]
  · intro q _ hq
    have hne : blockMap h12 q ≠ D := by
      intro h
      by_cases hq2 : q = x₂
      · rw [hq2, blockMap_x₂] at h
        exact hD h.symm
      · rw [blockMap_of_ne h12 hq2] at h
        exact hq (congrArg Subtype.val h)
    rw [ite_eq_right hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem arith_sq (n : ℕ) (hn : 2 ≤ n) : (n - 2) ^ 2 + 1 ≤ (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + m - 2 = m by omega, show 2 + m - 1 = m + 1 by omega]
  nlinarith

end Helpers53

end Sec5x

/-! ### Section 5.3: a congruence -/

section General2

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- tex:209-211 and tex:666-676: the quotient automaton is synchronizing, `rt(A) ≤ rt(A') + 1`, and it satisfies the
hypothesis of Theorem 3.1 (a positive stationary vector constant off one state, for the same weights). -/
theorem prop_5_6_quot_hyp_proved (hA : A.Synchronizing) (hsc : A.StronglyConnected) (W : QEWitness A 2)
    (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (hblock : A.IsBlockPair x₁ x₂) :
    (A.blockQuot x₁ x₂ h12).Synchronizing ∧ A.rt ≤ (A.blockQuot x₁ x₂ h12).rt + 1 ∧
      2 ≤ Fintype.card {q : Q // q ≠ x₂} ∧
      ∃ α' : {q : Q // q ≠ x₂} → ℝ, (A.blockQuot x₁ x₂ h12).IsStationary W.p α' ∧ (∀ q, 0 < α' q) ∧
        ∃ x', ∀ q q', q ≠ x' → q' ≠ x' → α' q = α' q' := by
  obtain ⟨c₀, hc₀⟩ := Sec5x.exists_merge A W hsc hX hblock
  obtain ⟨-, hst, hpos⟩ := lem_5_5_proved A hsc W
  refine ⟨Sec5x.quot_sync A h12 hblock hA, Sec5x.rt_le_quot A h12 hblock hc₀, Sec5x.card_quot_ge_two A h12 W hX,
    Sec5x.lump h12 (A.alphaStat W.E W.p), ⟨?_, Sec5x.lump_vecMul A h12 hblock W.p _ hst.2⟩,
    Sec5x.lump_pos h12 _ hpos, ⟨x₁, h12⟩, fun D D' hD hD' => ?_⟩
  · intro h0
    have h := Sec5x.lump_pos h12 _ hpos ⟨x₁, h12⟩
    rw [h0] at h
    simp at h
  · rw [Sec5x.lump_one A h12 W hX D hD, Sec5x.lump_one A h12 W hX D' hD']

/-- Proposition 5.6, tex:662: the strongly connected case. -/
theorem prop_5_6_sc_proved (hA : A.Synchronizing) (hsc : A.StronglyConnected) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (hblock : A.IsBlockPair x₁ x₂) :
    A.rt ≤ (((Fintype.card Q - 2) ^ 2 + 1 : ℕ) : ℕ∞) := by
  obtain ⟨hsync, hle, h2, α', hst, hpos, x', hconst⟩ := prop_5_6_quot_hyp_proved A hA hsc W x₁ x₂ hX h12 hblock
  have h31 := thm_3_1_proved _ hsync h2 W.p W.weights α' hst hpos x' hconst
  rw [Sec5x.card_quot] at h31
  have heq : Fintype.card Q - 1 - 1 = Fintype.card Q - 2 := by omega
  rw [heq] at h31
  calc A.rt ≤ (A.blockQuot x₁ x₂ h12).rt + 1 := hle
    _ ≤ (((Fintype.card Q - 2) ^ 2 : ℕ) : ℕ∞) + 1 := add_le_add h31 le_rfl
    _ = (((Fintype.card Q - 2) ^ 2 + 1 : ℕ) : ℕ∞) := (Nat.cast_succ _).symm

end General2

/-- Proposition 5.6, tex:659-662, given Theorem 4.1 (`h41`): the first bound. -/
theorem prop_5_6_of {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]
    (h41 : ∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), B.Synchronizing →
        2 ≤ Fintype.card Q' → QuasiEulerian B 1 → B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞))
    (A : Automaton Q S) (hA : A.Synchronizing) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (hblock : A.IsBlockPair x₁ x₂) : A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  have h2 := Sec5x.card_quot_ge_two A h12 W hX
  rw [Sec5x.card_quot] at h2
  by_cases hsc : A.StronglyConnected
  · refine (prop_5_6_sc_proved A hA hsc W x₁ x₂ hX h12 hblock).trans ?_
    exact_mod_cast Sec5x.arith_sq _ (by omega)
  · exact thm_5_1_of h41 A hA (by omega) 2 le_rfl ⟨W⟩ hsc

end CernyQE
