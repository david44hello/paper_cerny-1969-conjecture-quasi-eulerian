/-
Proofs/Rem34w.lean — Remark 3.4: the integer stationary vector for t = i/j in lowest terms, and its sum.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.01 - 20261105 — first.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Proofs.Rows2
import CernyQE.Proofs.Stationary

namespace CernyQE

open Classical Automaton Matrix

universe u v

namespace Rem34w

/-- The arithmetic of Remark 3.4 for `s = (n-1) j + i`. -/
theorem arith (n i j s : ℕ) (hn : 2 ≤ n) (hi : 0 < i) (hj : 0 < j) (hs : s = (n - 1) * j + i) :
    (s = n ↔ i = 1 ∧ j = 1) ∧
      (¬ (i = 1 ∧ j = 1) → n + 1 ≤ s ∧ (n : ℤ) ^ 2 - n + 1 ≤ (s : ℤ) ^ 2 - 3 * s + 3) ∧
      ((n : ℤ) - 1) ^ 2 < (n : ℤ) ^ 2 - n + 1 := by
  have hlow : (n - 1) * 1 ≤ (n - 1) * j := Nat.mul_le_mul_left _ hj
  have hiff : s = n ↔ i = 1 ∧ j = 1 := by
    constructor
    · intro h
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj1 : j = 1 := by omega
        subst hj1
        omega
      · have h2 : (n - 1) * 2 ≤ (n - 1) * j := Nat.mul_le_mul_left _ hj2
        omega
    · rintro ⟨rfl, rfl⟩
      omega
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  refine ⟨hiff, fun hne => ?_, by nlinarith⟩
  have hge : n + 1 ≤ s := by
    have hsn : s ≠ n := fun h => hne (hiff.1 h)
    omega
  refine ⟨hge, ?_⟩
  have h1 : (n : ℤ) + 1 ≤ s := by exact_mod_cast hge
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℤ) ≤ s + n - 2)]

end Rem34w

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

namespace Rem34w

/-- Under the hypotheses of Remark 3.4, `u = (j, …, j, i)` (with `i` at `x`), so `∑ u = (n-1) j + i`. -/
theorem sum_eq (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p) (x : Q)
    (i j : ℕ) (hj : 0 < j) (hcop : Nat.Coprime i j)
    (hα : A.IsStationary p (alphaOff x ((i : ℝ) / j))) (u : Q → ℕ) (hu : ∀ q, 0 < u q)
    (hgcd : Finset.univ.gcd u = 1) (hstat : A.IsStationary p (fun q => (u q : ℝ))) :
    ∑ q, u q = (Fintype.card Q - 1) * j + i := by
  have hsc := lem_2_1_proved A hA p hp _ hstat (fun q => by exact_mod_cast hu q)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Q) x
  have : Nonempty Q := ⟨x⟩
  obtain ⟨π, -, -, huniq⟩ := lem_5_5_unique_proved A hsc p hp
  obtain ⟨c1, hc1⟩ := huniq _ hα
  obtain ⟨c2, hc2⟩ := huniq _ hstat
  have hc1q : ∀ q, alphaOff x ((i : ℝ) / j) q = c1 * π q := fun q => congrFun hc1 q
  have hc2q : ∀ q, (u q : ℝ) = c2 * π q := fun q => congrFun hc2 q
  have hy1 : c1 * π y = 1 := by
    rw [← hc1q y]
    simp [alphaOff, hy]
  have hscale : ∀ q, (u q : ℝ) = (u y : ℝ) * alphaOff x ((i : ℝ) / j) q := by
    intro q
    rw [hc2q q, hc2q y, hc1q q]
    calc c2 * π q = c2 * π q * (c1 * π y) := by rw [hy1, mul_one]
      _ = c2 * π y * (c1 * π q) := by ring
  have hoff : ∀ q, q ≠ x → u q = u y := by
    intro q hq
    have hq' := hscale q
    rw [show alphaOff x ((i : ℝ) / j) q = 1 by simp [alphaOff, hq], mul_one] at hq'
    exact_mod_cast hq'
  have hx : u x * j = u y * i := by
    have hx' := hscale x
    rw [show alphaOff x ((i : ℝ) / j) x = (i : ℝ) / j by simp [alphaOff]] at hx'
    have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
    have hreal : (u x : ℝ) * j = u y * i := by
      rw [hx', mul_assoc, div_mul_cancel₀ _ hj']
    exact_mod_cast hreal
  obtain ⟨m, hm⟩ : j ∣ u y := by
    have hdiv : j ∣ u y * i := ⟨u x, by rw [← hx, mul_comm]⟩
    exact hcop.symm.dvd_of_dvd_mul_right hdiv
  have hxm : u x = m * i := by
    rw [hm] at hx
    have hx2 : u x * j = (m * i) * j := by rw [hx]; ring
    exact Nat.eq_of_mul_eq_mul_right hj hx2
  have hm1 : m = 1 := by
    have hdvd : m ∣ Finset.univ.gcd u := by
      apply Finset.dvd_gcd
      intro q _
      by_cases hq : q = x
      · rw [hq, hxm]
        exact Dvd.intro i rfl
      · rw [hoff q hq, hm]
        exact Dvd.intro_left j rfl
    rw [hgcd] at hdvd
    exact Nat.dvd_one.1 hdvd
  subst hm1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have hrest : ∑ q ∈ Finset.univ.erase x, u q = ∑ _q ∈ Finset.univ.erase x, j := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hoff q (Finset.ne_of_mem_erase hq), hm, mul_one]
  rw [hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, smul_eq_mul, hxm,
    one_mul]
  ring

end Rem34w

theorem rem_3_4_w_proved (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p) (x : Q)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hcop : Nat.Coprime i j)
    (hα : A.IsStationary p (alphaOff x ((i : ℝ) / j))) (u : Q → ℕ) (hu : ∀ q, 0 < u q)
    (hgcd : Finset.univ.gcd u = 1) (hstat : A.IsStationary p (fun q => (u q : ℝ))) :
    ∑ q, u q = (Fintype.card Q - 1) * j + i ∧ (∑ q, u q = Fintype.card Q ↔ i = 1 ∧ j = 1) ∧
      (¬ (i = 1 ∧ j = 1) → Fintype.card Q + 1 ≤ ∑ q, u q ∧
        (Fintype.card Q : ℤ) ^ 2 - Fintype.card Q + 1 ≤ ((∑ q, u q : ℕ) : ℤ) ^ 2 - 3 * (∑ q, u q : ℕ) + 3) ∧
      ((Fintype.card Q : ℤ) - 1) ^ 2 < (Fintype.card Q : ℤ) ^ 2 - Fintype.card Q + 1 := by
  have hsum := Rem34w.sum_eq A hA hn p hp x i j hj hcop hα u hu hgcd hstat
  exact ⟨hsum, Rem34w.arith _ i j _ hn hi hj hsum⟩

end General

end CernyQE
