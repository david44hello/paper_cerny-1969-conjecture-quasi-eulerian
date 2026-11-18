/-
CernyQE/Proofs/Rows2.lean — the rows of Section 2 (and the row of the 0/1 count in the proof of Lemma 2.4), with the
exact binders and types of Paper/Statements.lean, each proved from the proof modules.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Proofs.Sec2

namespace CernyQE

open Classical Automaton Matrix

universe u v

theorem sec2_act_append_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (q : Q) (u w : List S) :
    A.act q (u ++ w) = A.act (A.act q u) w :=
  sec2_act_append_core A q u w

theorem sec2_pre_append_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (K : Finset Q) (u w : List S) :
    A.pre K (u ++ w) = A.pre (A.pre K w) u :=
  sec2_pre_append_core A K u w

theorem sec2_mem_pre_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (x : Q) (K : Finset Q) (w : List S) :
    x ∈ A.pre K w ↔ A.act x w ∈ K :=
  sec2_mem_pre_core A x K w

theorem sec2_ext_method_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ) (hK : ∀ j < J, K (j + 1) = A.pre (K j) (w j)) (hJ : K J = Finset.univ) :
    K J = A.pre (K 0) (((List.range J).reverse.map w).flatten) ∧
      (∀ q, A.act q (((List.range J).reverse.map w).flatten) ∈ K 0) ∧
      ((∃ r, K 0 = {r}) → A.IsReset (((List.range J).reverse.map w).flatten)) ∧
      (∀ (r : Q) (c : S), K 0 = A.pre {r} [c] → A.IsReset (((List.range J).reverse.map w).flatten ++ [c])) :=
  sec2_ext_method_core A K w J hK hJ

theorem sec2_Mw_mul_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (u w : List S) :
    A.Mw (u ++ w) = A.Mw u * A.Mw w :=
  sec2_Mw_mul_core A u w

theorem sec2_Mw_one_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (w : List S) :
    A.Mw w *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 :=
  sec2_Mw_one_core A w

theorem sec2_Mw_ind_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (w : List S) (K : Finset Q) :
    A.Mw w *ᵥ ind K = ind (A.pre K w) :=
  sec2_Mw_ind_core A w K

theorem sec2_wt_Mw_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (β : Q → ℝ) (w : List S) (K : Finset Q) :
    β ⬝ᵥ (A.Mw w *ᵥ ind K) = wt β (A.pre K w) :=
  sec2_wt_Mw_core A β w K

theorem sec2_M_stochastic_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (p : S → ℝ) (hp : IsLetterWeights p) :
    (∀ q q', 0 ≤ A.M p q q') ∧ ∀ q, ∑ q', A.M p q q' = 1 :=
  sec2_M_stochastic_core A p hp

theorem sec2_outweight_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (p : S → ℝ) (hp : IsLetterWeights p) (q : Q) :
    ∑ q', A.M p q q' = 1 :=
  sec2_outweight_core A p hp q

theorem eq_2_1_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (p : S → ℝ) (α : Q → ℝ) (hα : A.IsStationary p α) (T : Finset Q) :
    ∑ b, p b * wt α (A.pre T [b]) = α ⬝ᵥ (A.M p *ᵥ ind T) ∧ α ⬝ᵥ (A.M p *ᵥ ind T) = wt α T :=
  eq_2_1_core A p α hα T

theorem sec2_inW_sum_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (p : S → ℝ) (hp : IsLetterWeights p) :
    ∑ q, A.inW p q = (Fintype.card Q : ℝ) :=
  sec2_inW_sum_core A p hp

theorem sec2_one_stationary_iff_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) [Nonempty Q] (p : S → ℝ) (hp : IsLetterWeights p) :
    A.IsStationary p (fun _ => 1) ↔ ∀ q, A.inW p q = 1 :=
  sec2_one_stationary_iff_core A p hp

theorem lem_2_1_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (p : S → ℝ) (hp : IsLetterWeights p) (α : Q → ℝ) (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) :
    A.StronglyConnected :=
  lem_2_1_core A hA p α hp hα hpos

theorem lem_2_2_a_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (β : Q → ℝ) (K : Finset Q) (hQ : wt β Finset.univ ≠ 0) (hK0 : wt β K ≠ 0) (hK1 : wt β K ≠ wt β Finset.univ) :
    1 ≤ A.cost β K ∧ A.cost β K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞) :=
by
  obtain ⟨m, hm, h1, h2⟩ := lem_2_2_a_core A hA β K hQ hK0 hK1
  rw [hm]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem lem_2_2_b_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (β : Q → ℝ) (K : Finset Q) (hQ : wt β Finset.univ ≠ 0) (hK0 : wt β K ≠ 0) (hK1 : wt β K ≠ wt β Finset.univ) (m : ℕ) (hm : A.cost β K = m) (p : S → ℝ) (hp : IsLetterWeights p) (havg : ∀ v : List S, v.length = m - 1 →
      wt β (A.pre K v) ≤ ∑ b, p b * wt β (A.pre (A.pre K v) [b])) :
    ∃ w : List S, w.length = m ∧ A.Raises β K w :=
  lem_2_2_b_core A hA β K hQ hK0 hK1 m hm p hp havg

theorem lem_2_2_last_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (p : S → ℝ) (hp : IsLetterWeights p) (α : Q → ℝ) (hα : A.IsStationary p α) (hQ : wt α Finset.univ ≠ 0) (K : Finset Q) (hK0 : wt α K ≠ 0) (hK1 : wt α K ≠ wt α Finset.univ) :
    (∃ w : List S, w.length ≤ Fintype.card Q - 1 ∧ A.Raises α K w) ∧ minLen (A.Raises α K) = A.cost α K :=
  lem_2_2_last_core A hA p α hp hα hQ K hK0 hK1

theorem sec2_cost_bounds_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ) :
    (1 ≤ A.cost α K ∧ A.cost α K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞)) ∧
      ∀ p : S → ℝ, IsLetterWeights p → A.IsStationary p α →
        ∃ w : List S, (w.length : ℕ∞) = A.cost α K ∧ A.Raises α K w :=
by
  obtain ⟨⟨m, hm, h1, h2⟩, h3⟩ := sec2_cost_bounds_core A hA α hpos K hne hprop
  refine ⟨?_, h3⟩
  rw [hm]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem lem_2_3_in_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (x : Q) (K : Finset Q) (hfin : A.esc x K ≠ ⊤) (hx : x ∈ K) :
    A.esc x K ≤ K.card :=
  lem_2_3_in_core A x K hfin hx

theorem lem_2_3_out_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (x : Q) (K : Finset Q) (hfin : A.esc x K ≠ ⊤) (hx : x ∉ K) :
    A.esc x K ≤ ((Fintype.card Q - K.card : ℕ) : ℕ∞) :=
  lem_2_3_out_core A x K hfin hx

theorem lem_2_3_fin_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hsc : A.StronglyConnected) (x : Q) (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ) :
    A.esc x K ≠ ⊤ :=
  lem_2_3_fin_core A hsc x K hne hprop

theorem lem_2_4_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (j : ℕ) (hj : 2 ≤ j) (hjn : j ≤ Fintype.card Q) :
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      ((Fintype.card Q - j + 1 : ℕ) : ℕ∞) ≤ A.cost α T)).card ≤ 2 ^ j - 2 :=
  lem_2_4_core A hA hsc α hpos j hj hjn

theorem lem_2_4_two_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) :
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      A.cost α T = ((Fintype.card Q - 1 : ℕ) : ℕ∞))).card ≤ 2 :=
  lem_2_4_two_core A hA hsc α hpos

theorem lem_2_4_six_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) :
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      ((Fintype.card Q - 2 : ℕ) : ℕ∞) ≤ A.cost α T)).card ≤ 6 :=
  lem_2_4_six_core A hA hsc α hpos

theorem eq_2_2_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (α : Q → ℝ) (w : List S) :
    Matrix.vecMul α (A.Mw w) - α =
        ∑ i : Fin w.length, Matrix.vecMul (A.delta α (w.get i)) (A.Mw (w.drop (i.1 + 1))) ∧
      ∀ c : S, A.delta α c ⬝ᵥ (fun _ => (1 : ℝ)) = 0 :=
  eq_2_2_core A α w

theorem lem_2_4_i_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (α : Q → ℝ) (T : Finset Q) (k : ℕ) :
    ((k + 1 : ℕ) : ℕ∞) ≤ A.cost α T ↔ ∀ lam ∈ A.Dk α k, lam ⬝ᵥ ind T = 0 :=
  lem_2_4_i_core A α T k

theorem lem_2_4_ii_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (hA : A.Synchronizing) (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (k : ℕ) :
    min k (Fintype.card Q - 1) ≤ Module.finrank ℝ (A.Dk α k) :=
  lem_2_4_ii_core A hA hsc α hpos k

theorem rem_2_5_direct_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (α : Q → ℝ) (hQ : wt α Finset.univ ≠ 0) (k : ℕ) :
    A.Uk α (k + 1) = (ℝ ∙ α) ⊔ A.Dk α k ∧ Disjoint (ℝ ∙ α) (A.Dk α k) :=
  rem_2_5_direct_core A α hQ k

theorem lem_2_4_zeroOne_proved {ι : Type*} [Fintype ι] (V : Submodule ℝ (ι → ℝ)) :
    {ξ : ι → ℝ | ξ ∈ V ∧ ∀ i, ξ i = 0 ∨ ξ i = 1}.ncard ≤ 2 ^ Module.finrank ℝ V :=
  zeroOne_ncard_le V

end CernyQE
