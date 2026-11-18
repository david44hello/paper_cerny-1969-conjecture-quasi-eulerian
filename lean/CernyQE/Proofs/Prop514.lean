/-
CernyQE/Proofs/Prop514.lean — Proposition 5.14 (the integer classes) and Corollary 5.15 (the general integer bound).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Proofs.Basic
import CernyQE.Proofs.Rows2
import CernyQE.Proofs.Thm31
import CernyQE.Proofs.Stationary
import CernyQE.Proofs.BinaryBase
import CernyQE.Proofs.Census514

namespace CernyQE

open Classical Automaton Matrix

universe u v

namespace Prop514

/-! ### Arithmetic -/

/-- `J (n - 3) + c₁ + c₂ ≤ n^2 + 8 - 3n` for `J ≤ n`, `c₁ ≤ 6`, `c₂ ≤ 2` (tex:929-930). -/
theorem arith_main (n J c₁ c₂ : ℕ) (hn : 3 ≤ n) (hJ : J ≤ n) (h₁ : c₁ ≤ 6) (h₂ : c₂ ≤ 2) :
    J * (n - 3) + c₁ + c₂ ≤ n ^ 2 + 8 - 3 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [Nat.add_sub_cancel]
  have hJm : J * m ≤ (m + 3) * m := Nat.mul_le_mul_right m hJ
  have hsq : (m + 3) ^ 2 = (m + 3) * m + 3 * (m + 3) := by ring
  omega

/-- `n^2 + 8 - 3n ≤ (n - 1)^2` for `n ≥ 7` (tex:930). -/
theorem arith_seven (n : ℕ) (hn : 7 ≤ n) : n ^ 2 + 8 - 3 * n ≤ (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h1 : (m + 7 - 1) = m + 6 := by omega
  rw [h1]
  have hsq : (m + 7) ^ 2 = (m + 6) ^ 2 + 2 * m + 13 := by ring
  omega

/-- A cost of at most `n - 1` splits as `(n - 3) + [ℓ ≥ n - 2] + [ℓ ≥ n - 1]`. -/
theorem len_split (n l : ℕ) (hl : l ≤ n - 1) (hn : 3 ≤ n) :
    l ≤ (n - 3) + (if n - 2 ≤ l then 1 else 0) + (if n - 1 ≤ l then 1 else 0) := by
  split_ifs <;> omega

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- The case `n ≥ 7` of the proof of Proposition 5.14 (tex:920-930), for a positive integer stationary vector `u` with
`u(Q) - u_{q₀} ≤ n`: the process from `{q₀}` has at most `n` steps, at most two cost `n - 1` and at most six cost
`n - 2` or more (the tier lemma). -/
theorem rt_le_main (hA : A.Synchronizing) (hsc : A.StronglyConnected) (hn : 7 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (u : Q → ℕ) (hu : ∀ q, 0 < u q) (hstat : A.IsStationary p (fun q => (u q : ℝ)))
    (q₀ : Q) (hq₀ : ∑ q, u q ≤ Fintype.card Q + u q₀) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) := by
  have hpos : ∀ q, 0 < (fun q => (u q : ℝ)) q := fun q => by
    show (0 : ℝ) < (u q : ℝ)
    exact_mod_cast hu q
  obtain ⟨K, w, J, hK0, hP⟩ :=
    sec54_process_exists_proved A hA p hp _ hstat hpos {q₀} (Finset.singleton_nonempty q₀)
  have hne0 : (K 0).Nonempty := by
    rw [hK0]
    exact Finset.singleton_nonempty q₀
  obtain ⟨hmono, hinj, hnej, -, hsing, -⟩ := sec54_process_props_proved A _ hpos K w J hP hne0
  refine (hsing ⟨q₀, hK0⟩).trans (Nat.cast_le.mpr ?_)
  -- the values `u(K_j)` are natural numbers that rise strictly, from `u_{q₀}` to `u(Q)`: at most `n` steps
  have hV : ∀ T : Finset Q, wt (fun q => (u q : ℝ)) T = ((∑ q ∈ T, u q : ℕ) : ℝ) := by
    intro T
    simp [wt]
  have hlev : ∀ j ≤ J, u q₀ + j ≤ ∑ q ∈ K j, u q := by
    intro j
    induction j with
    | zero => intro _; simp [hK0]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hmono j (j + 1) (by omega) hj
      rw [hV, hV] at h2
      have h3 : ∑ q ∈ K j, u q < ∑ q ∈ K (j + 1), u q := by exact_mod_cast h2
      omega
  have hJ : J ≤ Fintype.card Q := by
    have h := hlev J le_rfl
    rw [hP.2] at h
    omega
  -- every step costs at most `n - 1`
  have hlen : ∀ j < J, (((w j).length : ℕ) : ℕ∞) = A.cost (fun q => (u q : ℝ)) (K j) :=
    fun j hj => (hP.1 j hj).2.2.1
  have hprop : ∀ j < J, K j ≠ Finset.univ := fun j hj => (hP.1 j hj).1
  have hle : ∀ j < J, (w j).length ≤ Fintype.card Q - 1 := by
    intro j hj
    have h := (sec2_cost_bounds_proved A hA _ hpos (K j) (hnej j hj.le) (hprop j hj)).1.2
    rw [← hlen j hj] at h
    exact_mod_cast h
  -- the visited sets are distinct, so the tier lemma bounds the expensive steps
  have hcount : ∀ (m : ℕ) (F : Finset (Finset Q)), (∀ j < J, m ≤ (w j).length → K j ∈ F) →
      ((Finset.range J).filter (fun j => m ≤ (w j).length)).card ≤ F.card := by
    intro m F hF
    apply Finset.card_le_card_of_injOn K
    · intro j hj
      have hj' := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
      exact hF j (Finset.mem_range.mp hj'.1) hj'.2
    · intro i hi j hj hij
      have hi' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
      have hj' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
      exact hinj i j hi'.le hj'.le hij
  have hc₂ : ((Finset.range J).filter (fun j => Fintype.card Q - 1 ≤ (w j).length)).card ≤ 2 := by
    refine (hcount _ _ ?_).trans (lem_2_4_two_proved A hA hsc _ hpos)
    intro j hj hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hnej j hj.le, hprop j hj, ?_⟩
    rw [← hlen j hj, le_antisymm (hle j hj) hm]
  have hc₆ : ((Finset.range J).filter (fun j => Fintype.card Q - 2 ≤ (w j).length)).card ≤ 6 := by
    refine (hcount _ _ ?_).trans (lem_2_4_six_proved A hA hsc _ hpos)
    intro j hj hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hnej j hj.le, hprop j hj, ?_⟩
    rw [← hlen j hj]
    exact_mod_cast hm
  have hsum : ∑ j ∈ Finset.range J, (w j).length ≤
      J * (Fintype.card Q - 3) + ((Finset.range J).filter (fun j => Fintype.card Q - 2 ≤ (w j).length)).card +
        ((Finset.range J).filter (fun j => Fintype.card Q - 1 ≤ (w j).length)).card := by
    calc ∑ j ∈ Finset.range J, (w j).length
        ≤ ∑ j ∈ Finset.range J, ((Fintype.card Q - 3) + (if Fintype.card Q - 2 ≤ (w j).length then 1 else 0) +
            (if Fintype.card Q - 1 ≤ (w j).length then 1 else 0)) :=
          Finset.sum_le_sum fun j hj => len_split _ _ (hle j (Finset.mem_range.mp hj)) (by omega)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
            Finset.card_filter, Finset.card_filter]
  exact hsum.trans (arith_main _ _ _ _ (by omega) hJ hc₆ hc₂)

omit [Fintype Q] [DecidableEq Q] in
/-- A real stationary vector with natural-number entries, as a natural-number vector. -/
theorem nat_vector (α : Q → ℝ) (hint : ∀ q, ∃ m : ℕ, α q = m) :
    ∃ u : Q → ℕ, (fun q => (u q : ℝ)) = α :=
  ⟨fun q => (hint q).choose, funext fun q => (hint q).choose_spec.symm⟩

/-- `α(Q) = |E| + α_{x₁} + α_{x₂}` for the vector of Lemma 5.5 when `Q \ E = {x₁, x₂}`. -/
theorem wt_alphaStat_univ (E : Finset Q) (p : S → ℝ) (x₁ x₂ : Q) (hX : Finset.univ \ E = {x₁, x₂})
    (h12 : x₁ ≠ x₂) :
    wt (A.alphaStat E p) Finset.univ = E.card + A.alphaStat E p x₁ + A.alphaStat E p x₂ := by
  have hE : ∑ q ∈ E, A.alphaStat E p q = E.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun q hq => ?_
    have h : q ∉ Finset.univ \ E := fun h => (Finset.mem_sdiff.mp h).2 hq
    simp [Automaton.alphaStat, h]
  have hsplit := Finset.sum_sdiff (Finset.subset_univ E) (f := A.alphaStat E p)
  rw [hX, Finset.sum_pair h12, hE] at hsplit
  rw [wt, ← hsplit]
  ring

/-- The vector of Lemma 5.5 has natural-number entries if its values on `Q \ E = {x₁, x₂}` do. -/
theorem alphaStat_nat (E : Finset Q) (p : S → ℝ) (x₁ x₂ : Q) (hX : Finset.univ \ E = {x₁, x₂}) (m₁ m₂ : ℕ)
    (h₁ : A.alphaStat E p x₁ = m₁) (h₂ : A.alphaStat E p x₂ = m₂) : ∀ q, ∃ m : ℕ, A.alphaStat E p q = m := by
  intro q
  by_cases hq : q ∈ Finset.univ \ E
  · rw [hX] at hq
    rcases Finset.mem_insert.mp hq with h | h
    · exact ⟨m₁, h ▸ h₁⟩
    · rw [Finset.mem_singleton] at h
      exact ⟨m₂, h ▸ h₂⟩
  · exact ⟨1, by simp [Automaton.alphaStat, hq]⟩

/-- The bound of Corollary 5.15 for a real positive stationary vector with natural-number entries. -/
theorem rt_le_of_real (hA : A.Synchronizing) (hsc : A.StronglyConnected) (hn : 7 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (α : Q → ℝ) (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q)
    (hint : ∀ q, ∃ m : ℕ, α q = m) (q₀ : Q) (hq₀ : wt α Finset.univ ≤ Fintype.card Q + α q₀) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) := by
  obtain ⟨u, rfl⟩ := nat_vector α hint
  refine rt_le_main A hA hsc hn p hp u (fun q => by have h := hpos q; dsimp only at h; exact_mod_cast h) hα q₀ ?_
  have h : ((∑ q, u q : ℕ) : ℝ) ≤ ((Fintype.card Q + u q₀ : ℕ) : ℝ) := by
    push_cast
    simpa [wt] using hq₀
  exact_mod_cast h

end General

end Prop514

open Prop514

section General2

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

theorem rem_5_15_general_proved (hA : A.Synchronizing) (hn : 7 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (u : Q → ℕ) (hu : ∀ q, 0 < u q) (hstat : A.IsStationary p (fun q => (u q : ℝ)))
    (hmax : ∃ q₀, ∑ q, u q ≤ Fintype.card Q + u q₀) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧ A.StronglyConnected := by
  have hpos : ∀ q, 0 < (fun q => (u q : ℝ)) q := fun q => by
    show (0 : ℝ) < (u q : ℝ)
    exact_mod_cast hu q
  have hsc := lem_2_1_proved A hA p hp _ hstat hpos
  obtain ⟨q₀, hq₀⟩ := hmax
  exact ⟨rt_le_main A hA hsc hn p hp u hu hstat q₀ hq₀, hsc⟩

theorem rem_5_15_2k_proved (hA : A.Synchronizing) (hsc : A.StronglyConnected) (hn : 7 ≤ Fintype.card Q)
    (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (k : ℕ) (_hk : 1 ≤ k)
    (hcl : (A.alphaStat W.E W.p x₁ = 2 ∧ A.alphaStat W.E W.p x₂ = k) ∨
      (A.alphaStat W.E W.p x₁ = k ∧ A.alphaStat W.E W.p x₂ = 2)) :
    (∀ q, ∃ m : ℕ, A.alphaStat W.E W.p q = m) ∧
      (∃ q₀, wt (A.alphaStat W.E W.p) Finset.univ ≤ Fintype.card Q + A.alphaStat W.E W.p q₀) ∧
      A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  have hX' : Finset.univ \ W.E = {x₁, x₂} := hX
  obtain ⟨-, hstat, hpos⟩ := lem_5_5_proved A hsc W
  have hint : ∀ q, ∃ m : ℕ, A.alphaStat W.E W.p q = m := by
    rcases hcl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact alphaStat_nat A W.E W.p x₁ x₂ hX' 2 k (by rw [h₁]; norm_num) h₂
    · exact alphaStat_nat A W.E W.p x₁ x₂ hX' k 2 h₁ (by rw [h₂]; norm_num)
  have hEc : (W.E.card : ℝ) = (Fintype.card Q : ℝ) - 2 := by
    rw [W.card_E, Nat.cast_sub (by omega)]
    norm_num
  have hwt := wt_alphaStat_univ A W.E W.p x₁ x₂ hX' h12
  have hmax : ∃ q₀, wt (A.alphaStat W.E W.p) Finset.univ ≤ Fintype.card Q + A.alphaStat W.E W.p q₀ := by
    rcases hcl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨x₂, by rw [hwt, hEc, h₁, h₂]; linarith⟩
    · exact ⟨x₁, by rw [hwt, hEc, h₁, h₂]; linarith⟩
  obtain ⟨q₀, hq₀⟩ := hmax
  refine ⟨hint, ⟨q₀, hq₀⟩, ?_⟩
  refine (rt_le_of_real A hA hsc hn W.p W.weights _ hstat hpos hint q₀ hq₀).trans
    (Nat.cast_le.mpr (arith_seven _ hn))

/-- Corollary 5.15, tex:946-950. Both bounds for each integer class {2,k}. -/
theorem cor_5_15_2k_bound_proved (hA : A.Synchronizing) (hsc : A.StronglyConnected) (hn : 7 ≤ Fintype.card Q)
    (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (k : ℕ) (hk : 1 ≤ k)
    (hcl : (A.alphaStat W.E W.p x₁ = 2 ∧ A.alphaStat W.E W.p x₂ = k) ∨
      (A.alphaStat W.E W.p x₁ = k ∧ A.alphaStat W.E W.p x₂ = 2)) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧
      Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨hint, ⟨q₀, hq₀⟩, _⟩ := rem_5_15_2k_proved A hA hsc hn W x₁ x₂ hX h12 k hk hcl
  obtain ⟨_, hstat, hpos⟩ := lem_5_5_proved A hsc W
  exact ⟨rt_le_of_real A hA hsc hn W.p W.weights _ hstat hpos hint q₀ hq₀, arith_seven _ hn⟩

/-- Corollary 5.15, tex:950. The proper levels lie between the starting maximum and the total minus one. Every step increases the value by at least one. -/
theorem cor_5_15_levels_proved (u : Q → ℕ) (hu : ∀ q, 0 < u q) (q₀ : Q)
    (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ) (hK : K 0 = {q₀})
    (hP : A.IsProcess (fun q => (u q : ℝ)) K w J) (hmax : (∑ q, u q) - u q₀ ≤ Fintype.card Q) :
    (∀ j < J, u q₀ ≤ ∑ q ∈ K j, u q ∧ (∑ q ∈ K j, u q) ≤ (∑ q, u q)-1) ∧
      J ≤ (∑ q, u q)-u q₀ ∧ (∑ q, u q)-u q₀ ≤ Fintype.card Q := by
  have hp : ∀ q, (0:ℝ) < u q := fun q => by exact_mod_cast hu q
  have hne : (K 0).Nonempty := hK ▸ Finset.singleton_nonempty q₀
  have hm := (sec54_process_props_proved A _ hp K w J hP hne).1
  have hV (T : Finset Q) : wt (fun q => (u q : ℝ)) T = ((∑ q ∈ T, u q : ℕ) : ℝ) := by simp [wt]
  have hi (i j : ℕ) (hij : i < j) (hj : j ≤ J) : (∑ q ∈ K i, u q) < ∑ q ∈ K j, u q := by
    have h := hm i j hij hj
    rw [hV,hV] at h
    exact_mod_cast h
  have hlev : ∀ j ≤ J, u q₀ + j ≤ ∑ q ∈ K j, u q := by
    intro j
    induction j with
    | zero => simp [hK]
    | succ j ih =>
      intro hj
      have := ih (by omega)
      have := hi j (j+1) (by omega) hj
      omega
  have hlast := hlev J le_rfl
  rw [hP.2] at hlast
  refine ⟨?_, by omega, hmax⟩
  intro j hj
  have := hlev j hj.le
  have hlt := hi j J hj le_rfl
  rw [hP.2] at hlt
  omega

/-- Corollary 5.15, tex:951. In class {2,k}, the maximum is max(2,k) and subtracting it from the total leaves at most n. -/
theorem cor_5_15_mass_proved (hn : 7 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁,x₂}) (h12 : x₁ ≠ x₂) (k : ℕ) (hk : 1 ≤ k)
    (hcl : (A.alphaStat W.E W.p x₁ = 2 ∧ A.alphaStat W.E W.p x₂ = k) ∨
      (A.alphaStat W.E W.p x₁ = k ∧ A.alphaStat W.E W.p x₂ = 2)) :
    let α := A.alphaStat W.E W.p
    ∃ q₀, (∀ q, α q ≤ α q₀) ∧ α q₀ = max 2 (k : ℝ) ∧
      wt α Finset.univ - α q₀ = Fintype.card Q + k - max 2 (k : ℝ) ∧
      wt α Finset.univ - α q₀ ≤ Fintype.card Q := by
  dsimp only
  have hX' : Finset.univ \ W.E = {x₁,x₂} := hX
  have hwt := Prop514.wt_alphaStat_univ A W.E W.p x₁ x₂ hX' h12
  have he : (W.E.card : ℝ) = Fintype.card Q - 2 := by
    rw [W.card_E, Nat.cast_sub (by omega)]
    norm_num
  have upper (q : Q) : A.alphaStat W.E W.p q ≤ max 2 (k:ℝ) := by
    by_cases hq : q ∈ Finset.univ \ W.E
    · rw [hX'] at hq
      rcases Finset.mem_insert.mp hq with rfl | hh
      · rcases hcl with h | h <;> rw [h.1] <;> simp
      · rw [Finset.mem_singleton.mp hh]
        rcases hcl with h | h <;> rw [h.2] <;> simp
    · simp [Automaton.alphaStat,hq]
      <;> exact (by norm_num : (1:ℝ) ≤ 2).trans (le_max_left _ _)
  have attain : ∃ q, A.alphaStat W.E W.p q = max 2 (k:ℝ) := by
    rcases hcl with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rcases le_total (2:ℝ) k with h | h
      · exact ⟨x₂, by rw [h2,max_eq_right h]⟩
      · exact ⟨x₁, by rw [h1,max_eq_left h]⟩
    · rcases le_total (2:ℝ) k with h | h
      · exact ⟨x₁, by rw [h1,max_eq_right h]⟩
      · exact ⟨x₂, by rw [h2,max_eq_left h]⟩
  obtain ⟨q₀,hq₀⟩ := attain
  refine ⟨q₀, fun q => hq₀.symm ▸ upper q, hq₀, ?_, ?_⟩
  all_goals rw [hwt,he,hq₀]
  all_goals rcases hcl with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> linarith [le_max_right (2:ℝ) k]

end General2

section Binary

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

theorem prop_5_14_big_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 7 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) := by
  obtain ⟨W', hE, -, hp⟩ := lem_5_7_a_proved A a b hab hS W
  obtain ⟨-, hstat, hpos⟩ := lem_5_5_proved A hsc W'
  rw [hE, hp] at hstat hpos
  have hX' : Finset.univ \ W.E = {x₁, x₂} := hX
  have hEc : (W.E.card : ℝ) = (Fintype.card Q : ℝ) - 2 := by
    rw [W.card_E, Nat.cast_sub (by omega)]
    norm_num
  have hwt := wt_alphaStat_univ A W.E (fun _ => 1 / 2) x₁ x₂ hX' h12
  rw [hEc] at hwt
  have hhalf : IsLetterWeights (fun _ : S => (1 : ℝ) / 2) := by
    rw [← hp]
    exact W'.weights
  set α := A.alphaStat W.E (fun _ => (1 : ℝ) / 2) with hα
  have key : ∀ m₁ m₂ : ℕ, α x₁ = m₁ → α x₂ = m₂ → ∀ q₀, wt α Finset.univ ≤ Fintype.card Q + α q₀ →
      A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) := fun m₁ m₂ h₁ h₂ q₀ hq₀ =>
    rt_le_of_real A hA hsc hn _ hhalf α hstat hpos (alphaStat_nat A W.E _ x₁ x₂ hX' m₁ m₂ h₁ h₂) q₀ hq₀
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcl
  rcases hcl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact key 2 2 (by rw [h₁]; norm_num) (by rw [h₂]; norm_num) x₁ (by rw [hwt, h₁, h₂]; linarith)
  · exact key 2 3 (by rw [h₁]; norm_num) (by rw [h₂]; norm_num) x₂ (by rw [hwt, h₁, h₂]; linarith)
  · exact key 3 2 (by rw [h₁]; norm_num) (by rw [h₂]; norm_num) x₁ (by rw [hwt, h₁, h₂]; linarith)
  · exact key 2 4 (by rw [h₁]; norm_num) (by rw [h₂]; norm_num) x₂ (by rw [hwt, h₁, h₂]; linarith)
  · exact key 4 2 (by rw [h₁]; norm_num) (by rw [h₂]; norm_num) x₁ (by rw [hwt, h₁, h₂]; linarith)

theorem prop_5_14_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  by_cases h6 : Fintype.card Q ≤ 6
  · exact prop_5_14_small_proved A a b hab hS hA hsc hn h6 W x₁ x₂ hX h12 hcl
  · have h7 : 7 ≤ Fintype.card Q := by omega
    exact (prop_5_14_big_proved A a b hab hS hA hsc h7 W x₁ x₂ hX h12 hcl).trans
      (Nat.cast_le.mpr (arith_seven _ h7))

end Binary

end CernyQE
