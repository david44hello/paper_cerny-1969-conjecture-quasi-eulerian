/-
Proofs/Rem34L.lean — Remark 3.4: the least common multiple of the denominators of α/α(Q) for an integer t.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.01 - 20261105 — first.
-/
import Mathlib

namespace CernyQE

open Classical

universe u

theorem rem_3_4_L_proved {Q : Type u} [Fintype Q] [DecidableEq Q] (hn : 2 ≤ Fintype.card Q) (x : Q) (k : ℕ) (hk : 1 ≤ k) :
    Finset.univ.lcm (fun q : Q => (((if q = x then (k : ℚ) else 1)) / ((Fintype.card Q : ℚ) - 1 + k)).den) =
      Fintype.card Q - 1 + k := by
  set L : ℕ := Fintype.card Q - 1 + k with hLdef
  have hcast : (Fintype.card Q : ℚ) - 1 + k = (L : ℚ) := by
    rw [hLdef, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ Fintype.card Q), Nat.cast_one]
  have hLpos : 0 < L := by omega
  have hden_dvd : ∀ a : ℕ, ((a : ℚ) / L).den ∣ L := by
    intro a
    rw [Rat.natCast_div_eq_divInt]
    exact_mod_cast Rat.den_dvd (a : ℤ) (L : ℤ)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Q) x
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro q _
    rw [hcast]
    split_ifs
    · exact hden_dvd k
    · have h1 := hden_dvd 1
      rwa [Nat.cast_one] at h1
  · have hyden : ((if y = x then (k : ℚ) else 1) / ((Fintype.card Q : ℚ) - 1 + k)).den = L := by
      simp only [hy, ↓reduceIte]
      rw [hcast, one_div, Rat.inv_natCast_den_of_pos hLpos]
    rw [← hyden]
    exact Finset.dvd_lcm (Finset.mem_univ y)

end CernyQE
