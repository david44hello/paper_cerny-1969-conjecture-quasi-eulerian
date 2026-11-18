/-
The value ranges, sizes and costs of Table 3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Proofs.Prop513

namespace CernyQE

open Automaton Prop513

universe u v
variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- Table 3, tab_costs_float.tex:12-15 (included at tex:888). Lean u = printed x₂, v = printed x₁. With equal membership of u and v, alignment means s has that membership too. -/
theorem table_3_half_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) (K : Finset Q) (hne : K.Nonempty)
    (hprop : K ≠ Finset.univ) (hgt : 2 < wt (A.alphaStat W.E (fun _ => 1 / 2)) K) :
    let n := Fintype.card Q
    let α := A.alphaStat W.E (fun _ => 1 / 2)
    let m := A.cost α K
    (v ∉ K → u ∉ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N ∧ K.card = N ∧
      (W.s ∉ K → N ≤ n - 3 ∧ m ≤ ((n - N : ℕ) : ℕ∞)) ∧ (W.s ∈ K → m ≤ 2)) ∧
    (v ∈ K → u ∉ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N ∧ K.card = N - 1 ∧ m = 1) ∧
    (v ∉ K → u ∈ K → ∃ N : ℕ, 2 ≤ N ∧ N ≤ n - 1 ∧ wt α K = N + 1/2 ∧ K.card = N + 1 ∧ m = 1) ∧
    (v ∈ K → u ∈ K → ∃ N : ℕ, 2 ≤ N ∧ N ≤ n - 1 ∧ wt α K = N + 1/2 ∧ K.card = N ∧
      (W.s ∈ K → 3 ≤ N ∧ m ≤ (N : ℕ∞)) ∧ (W.s ∉ K → m ≤ 2)) := by
  dsimp only
  have hsize : K.card < Fintype.card Q := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hprop)
  obtain ⟨mix, off, inside, outside⟩ := cost_cases A a b hab hS hsc hn W u v hX huv (Or.inl hu) hv K hne hprop
  obtain ⟨_, both, _, _, missing⟩ := card_facts A W hX huv K
  have hform := sec54_alpha_formula_proved A W u v hX huv K
  rw [hu, hv] at hform
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hV hU
    rw [ein_not_mem hU, ein_not_mem hV] at hform
    have hcard : (2 : ℝ) < K.card := by linarith
    have hnat : 2 < K.card := by exact_mod_cast hcard
    refine ⟨K.card, by omega, by omega, by linarith, rfl, ?_, ?_⟩
    · intro hs
      have := missing hU hV hs
      exact ⟨by omega, outside hU hV hs⟩
    · exact fun hs => off (iff_of_false hU hV) (iff_of_true hs hV)
  · intro hV hU
    rw [ein_not_mem hU, ein_mem hV] at hform
    have hcard : (1 : ℝ) < K.card := by linarith
    have hnat : 1 < K.card := by exact_mod_cast hcard
    refine ⟨K.card + 1, by omega, by omega, ?_, by omega, mix (fun h => hU (h.mpr hV))⟩
    push_cast
    linarith
  · intro hV hU
    rw [ein_mem hU, ein_not_mem hV] at hform
    have hcard : (2 : ℝ) < K.card := by linarith
    have hnat : 2 < K.card := by exact_mod_cast hcard
    refine ⟨K.card - 1, by omega, by omega, ?_, by omega, mix (fun h => hV (h.mp hU))⟩
    rw [Nat.cast_sub (by omega : 1 ≤ K.card)]
    push_cast
    linarith
  · intro hV hU
    rw [ein_mem hU, ein_mem hV] at hform
    have hk := both hU hV
    have hthree (hs : W.s ∈ K) : 3 ≤ K.card := by
      obtain ⟨hus, hvs⟩ := ne_s A W hX
      have sub : ({u,v,W.s} : Finset Q) ⊆ K := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl <;> assumption
      have hc := Finset.card_le_card sub
      rwa [Prop513.card_three huv hus hvs] at hc
    refine ⟨K.card, hk, by omega, by linarith, rfl, ?_, ?_⟩
    · exact fun hs => ⟨hthree hs, inside hU hV hs⟩
    · exact fun hs => off (iff_of_true hU hV) (iff_of_false hs (not_not.mpr hV))

/-- Table 3, tab_costs_float.tex:17-20 (included at tex:888). Lean u = printed x₂, v = printed x₁. With equal membership of u and v, alignment means s has that membership too. -/
theorem table_3_three_halves_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) (K : Finset Q) (hne : K.Nonempty)
    (hprop : K ≠ Finset.univ) (hgt : 2 < wt (A.alphaStat W.E (fun _ => 1 / 2)) K) :
    let n := Fintype.card Q
    let α := A.alphaStat W.E (fun _ => 1 / 2)
    let m := A.cost α K
    (v ∉ K → u ∉ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N ∧ K.card = N ∧
      (W.s ∉ K → N ≤ n - 3 ∧ m ≤ ((n - N : ℕ) : ℕ∞)) ∧ (W.s ∈ K → m ≤ 2)) ∧
    (v ∈ K → u ∉ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N ∧ K.card = N - 1 ∧ m = 1) ∧
    (v ∉ K → u ∈ K → ∃ N : ℕ, 2 ≤ N ∧ N ≤ n ∧ wt α K = N + 1/2 ∧ K.card = N ∧ m = 1) ∧
    (v ∈ K → u ∈ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N + 1/2 ∧ K.card = N - 1 ∧
      (W.s ∈ K → 4 ≤ N ∧ m ≤ ((N - 1 : ℕ) : ℕ∞)) ∧ (W.s ∉ K → m ≤ 2)) := by
  dsimp only
  have hsize : K.card < Fintype.card Q := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hprop)
  obtain ⟨mix, off, inside, outside⟩ := cost_cases A a b hab hS hsc hn W u v hX huv (Or.inr hu) hv K hne hprop
  obtain ⟨_, both, _, _, missing⟩ := card_facts A W hX huv K
  have hform := sec54_alpha_formula_proved A W u v hX huv K
  rw [hu, hv] at hform
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hV hU
    rw [ein_not_mem hU, ein_not_mem hV] at hform
    have hcard : (2 : ℝ) < K.card := by linarith
    have hnat : 2 < K.card := by exact_mod_cast hcard
    refine ⟨K.card, by omega, by omega, by linarith, rfl, ?_, ?_⟩
    · intro hs
      have := missing hU hV hs
      exact ⟨by omega, outside hU hV hs⟩
    · exact fun hs => off (iff_of_false hU hV) (iff_of_true hs hV)
  · intro hV hU
    rw [ein_not_mem hU, ein_mem hV] at hform
    have hcard : (1 : ℝ) < K.card := by linarith
    have hnat : 1 < K.card := by exact_mod_cast hcard
    refine ⟨K.card + 1, by omega, by omega, ?_, by omega, mix (fun h => hU (h.mpr hV))⟩
    push_cast
    linarith
  · intro hV hU
    rw [ein_mem hU, ein_not_mem hV] at hform
    have hcard : (1 : ℝ) < K.card := by linarith
    have hnat : 1 < K.card := by exact_mod_cast hcard
    exact ⟨K.card, by omega, by omega, by linarith, rfl, mix (fun h => hV (h.mp hU))⟩
  · intro hV hU
    rw [ein_mem hU, ein_mem hV] at hform
    have hk := both hU hV
    have hthree (hs : W.s ∈ K) : 3 ≤ K.card := by
      obtain ⟨hus, hvs⟩ := ne_s A W hX
      have sub : ({u,v,W.s} : Finset Q) ⊆ K := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl <;> assumption
      have hc := Finset.card_le_card sub
      rwa [Prop513.card_three huv hus hvs] at hc
    refine ⟨K.card + 1, by omega, by omega, ?_, by omega, ?_, ?_⟩
    · push_cast
      linarith
    · intro hs
      have := hthree hs
      exact ⟨by omega, by simpa using inside hU hV hs⟩
    · exact fun hs => off (iff_of_true hU hV) (iff_of_false hs (not_not.mpr hV))

/-- Proposition 5.13, tex:896. A set of exceptional part (0,0) omits two distinct states. -/
theorem prop_5_13_missing_pair_proved {x₁ x₂ : Q} (h12 : x₁ ≠ x₂) (K : Finset Q)
    (h1 : x₁ ∉ K) (h2 : x₂ ∉ K) : K.card ≤ Fintype.card Q - 2 := by
  have h := Prop513.card_add_le K {x₁,x₂} (by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hh
    · exact h1
    · rw [Finset.mem_singleton.mp hh]
      exact h2)
  rw [Finset.card_pair h12] at h
  omega

end CernyQE
