/-
CernyQE/Proofs/Props511.lean — Propositions 5.11 and 5.12: every non-aligned pattern is good, and the bounds on rt.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary
import CernyQE.Proofs.Basic
import CernyQE.Proofs.Sec2
import CernyQE.Proofs.Rows2
import CernyQE.Proofs.Stationary
import CernyQE.Proofs.Thm31
import CernyQE.Proofs.Sec51
import CernyQE.Proofs.Census
import CernyQE.Proofs.BinaryBase

namespace CernyQE

universe u v

namespace Props511

/-! ### Finite facts on configurations -/

/-- The bit of a pattern at a target code (`0 = x₁`, `1 = x₂`, `2 = s`). -/
def bit (P : Bool × Bool × Bool) (k : Fin 3) : Bool :=
  if k = 0 then P.1 else if k = 1 then P.2.1 else P.2.2

/-- `[b]` as a rational number. -/
def bq (b : Bool) : ℚ := if b then 1 else 0

/-- The change `g₁ Δe₁ + g₂ Δe₂` under the letter coded `c` for a set with pattern `P`, read off the
configuration. -/
def chg (cf : Config) (P : Bool × Bool × Bool) (c : Fin 2) : ℚ :=
  (cf.t 0 - 1) * (bq (bit P (cf.tgt 0 c)) - bq P.1) + (cf.t 1 - 1) * (bq (bit P (cf.tgt 1 c)) - bq P.2.1)

/-- Every pattern that is not aligned has a letter whose change is not an integer. -/
def AllGood (cf : Config) : Prop :=
  ∀ P : Bool × Bool × Bool, P ≠ (true, true, true) → P ≠ (false, false, false) →
    ∃ c : Fin 2, (chg cf P c).den ≠ 1

instance (cf : Config) : Decidable (AllGood cf) := by unfold AllGood; infer_instance

theorem allGood_511 :
    ∀ cf ∈ (⟨2, 2, 2, 0, 1, 1⟩ : Config).renamings ∪ (⟨2, 2, 2, 0, 0, 1⟩ : Config).renamings, AllGood cf := by
  decide +kernel

theorem facts_512 :
    ∀ cf ∈ (⟨2, 1, 0, 2, 0, 1⟩ : Config).renamings ∪ (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings,
      AllGood cf ∧ ((cf.t 0 = 1/3 ∧ cf.t 1 = 2/3) ∨ (cf.t 0 = 2/3 ∧ cf.t 1 = 1/3) ∨
        (cf.t 0 = 2/3 ∧ cf.t 1 = 4/3) ∨ (cf.t 0 = 4/3 ∧ cf.t 1 = 2/3)) := by
  decide +kernel

/-! ### Counting the visited sets -/

/-- The facts on one visited set that the counts use: `L` is the length of its word (its cost), `c` its size,
`(e₁, e₂)` its `X`-part and `v` its value `α(K)`. -/
structure Visit (n : ℕ) (g₁ g₂ : ℝ) (L c : ℕ) (e₁ e₂ : Bool) (v : ℝ) : Prop where
  val : v = c + g₁ * (if e₁ then 1 else 0) + g₂ * (if e₂ then 1 else 0)
  pos : 1 ≤ c
  lt : c ≤ n - 1
  c00 : e₁ = false → e₂ = false → c ≤ n - 2
  c11 : e₁ = true → e₂ = true → 2 ≤ c
  L11 : e₁ = true → e₂ = true → L ≤ max (c - 1) 1
  L00 : e₁ = false → e₂ = false → L ≤ max (n - c - 1) 1
  Lmix : e₁ ≠ e₂ → L ≤ 1

/-- The values rise strictly and a key determines the value: so distinct visited sets have distinct keys, and the
lengths add up to at most the sum of the budgets over the keys. -/
theorem slot_sum {ι : Type*} [DecidableEq ι] (v : ℕ → ℝ) (L : ℕ → ℕ) (J : ℕ)
    (hmono : ∀ i j, i < j → j < J → v i < v j) (κ : ℕ → ι) (f : ι → ℝ)
    (hf : ∀ j < J, v j = f (κ j)) (T : Finset ι) (B : ι → ℕ)
    (hT : ∀ j < J, κ j ∈ T) (hB : ∀ j < J, L j ≤ B (κ j)) :
    ∑ j ∈ Finset.range J, L j ≤ ∑ τ ∈ T, B τ := by
  have hinj : Set.InjOn κ (Finset.range J) := by
    intro i hi j hj hij
    have hi' : i < J := by simpa using hi
    have hj' : j < J := by simpa using hj
    have hv : v i = v j := by rw [hf i hi', hf j hj', hij]
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hv (hmono i j h hj').ne
    · exact h
    · exact absurd hv.symm (hmono j i h hi').ne
  calc ∑ j ∈ Finset.range J, L j ≤ ∑ j ∈ Finset.range J, B (κ j) :=
        Finset.sum_le_sum fun j hj => hB j (Finset.mem_range.mp hj)
    _ = ∑ τ ∈ (Finset.range J).image κ, B τ := (Finset.sum_image hinj).symm
    _ ≤ ∑ τ ∈ T, B τ := Finset.sum_le_sum_of_subset (by
        intro τ hτ
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hτ
        exact hT j (Finset.mem_range.mp hj))

/-- A real number strictly between two consecutive integers is not an integer. -/
theorem not_int_of_between {r : ℝ} (z₀ : ℤ) (h1 : (z₀ : ℝ) < r) (h2 : r < z₀ + 1) : ∀ z : ℤ, r ≠ z := by
  intro z hz
  rw [hz] at h1 h2
  have e1 : z₀ < z := by exact_mod_cast h1
  have e2 : z < z₀ + 1 := by exact_mod_cast h2
  omega

/-! #### Proposition 5.11: the key is the size and the `X`-part -/

/-- The value `|K| + g₁ e₁ + g₂ e₂` of a size and an `X`-part. -/
noncomputable def f511 (g₁ g₂ : ℝ) (τ : ℕ × Bool × Bool) : ℝ :=
  τ.1 + g₁ * (if τ.2.1 then 1 else 0) + g₂ * (if τ.2.2 then 1 else 0)

/-- The budget of Proposition 5.11 for a size and an `X`-part. -/
def B511 (n : ℕ) (τ : ℕ × Bool × Bool) : ℕ :=
  if τ.2.1 then (if τ.2.2 then τ.1 - 1 else 1) else (if τ.2.2 then 1 else n - τ.1 - 1)

theorem sum_B511 (n : ℕ) :
    ∑ τ ∈ (Finset.Icc 2 (n - 1)) ×ˢ (Finset.univ : Finset (Bool × Bool)), B511 n τ = (n - 2) * n := by
  rw [Finset.sum_product]
  have h : ∀ k ∈ Finset.Icc 2 (n - 1), ∑ e ∈ (Finset.univ : Finset (Bool × Bool)), B511 n (k, e) = n := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    simp only [B511, ↓reduceIte, Bool.false_eq_true]
    omega
  rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.card_Icc, smul_eq_mul,
    show n - 1 + 1 - 2 = n - 2 by omega]

theorem visit_511 {n L c : ℕ} {e₁ e₂ : Bool} {v g₁ g₂ : ℝ} (hg₁ : g₁ ≤ 0) (hg₂ : g₂ ≤ 0)
    (hV : Visit n g₁ g₂ L c e₁ e₂ v) (hv : 1 < v) :
    v = f511 g₁ g₂ (c, e₁, e₂) ∧ (c, e₁, e₂) ∈ (Finset.Icc 2 (n - 1)) ×ˢ (Finset.univ : Finset (Bool × Bool)) ∧
      L ≤ B511 n (c, e₁, e₂) := by
  obtain ⟨hval, -, hlt, h00, -, hL11, hL00, hLmix⟩ := hV
  have hle : v ≤ c := by
    rw [hval]
    have h1 : g₁ * (if e₁ then 1 else 0) ≤ 0 := by split_ifs <;> linarith
    have h2 : g₂ * (if e₂ then 1 else 0) ≤ 0 := by split_ifs <;> linarith
    linarith
  have hc2 : 2 ≤ c := by
    have hc : (1 : ℝ) < c := hv.trans_le hle
    have : 1 < c := by exact_mod_cast hc
    omega
  refine ⟨hval, ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
    exact ⟨hc2, hlt⟩
  · cases e₁ <;> cases e₂ <;> simp only [B511, ↓reduceIte, Bool.false_eq_true]
    · have hL := hL00 rfl rfl
      have h := h00 rfl rfl
      rwa [max_eq_left (by omega)] at hL
    · exact hLmix (by decide)
    · exact hLmix (by decide)
    · have hL := hL11 rfl rfl
      rwa [max_eq_left (by omega)] at hL

theorem count_511 (n J : ℕ) (L c : ℕ → ℕ) (e₁ e₂ : ℕ → Bool) (v : ℕ → ℝ) (g₁ g₂ : ℝ)
    (hg₁ : g₁ ≤ 0) (hg₂ : g₂ ≤ 0) (hmono : ∀ i j, i < j → j < J → v i < v j)
    (hvis : ∀ j < J, Visit n g₁ g₂ (L j) (c j) (e₁ j) (e₂ j) (v j)) (hv : ∀ j < J, 1 < v j) :
    ∑ j ∈ Finset.range J, L j ≤ (n - 2) * n := by
  have h := fun j (hj : j < J) => visit_511 hg₁ hg₂ (hvis j hj) (hv j hj)
  rw [← sum_B511 n]
  exact slot_sum v L J hmono (fun j => (c j, e₁ j, e₂ j)) (f511 g₁ g₂) (fun j hj => (h j hj).1) _ (B511 n)
    (fun j hj => (h j hj).2.1) (fun j hj => (h j hj).2.2)

/-! #### Proposition 5.12: the key is the value -/

/-- The slots of Proposition 5.12: an integer value `N`, or a size and `e₁` for the `X`-parts `(1,0)`, `(0,1)`. -/
def slots (n : ℕ) : Finset (ℕ ⊕ (ℕ × Bool)) :=
  (Finset.Icc 1 (n - 2)).disjSum ((Finset.Icc 2 (n - 1)) ×ˢ (Finset.univ : Finset Bool))

/-- The key in the class `{1/3, 2/3}`: the integer value `|K| - e₁` for the `X`-parts `(1,1)`, `(0,0)`. -/
def keyA (c : ℕ) (e₁ e₂ : Bool) : ℕ ⊕ (ℕ × Bool) :=
  if e₁ = e₂ then Sum.inl (if e₁ then c - 1 else c) else Sum.inr (c, e₁)

/-- The value of a key in the class `{1/3, 2/3}`. -/
noncomputable def fA (g₁ g₂ : ℝ) : ℕ ⊕ (ℕ × Bool) → ℝ
  | Sum.inl N => N
  | Sum.inr τ => τ.1 + (if τ.2 then g₁ else g₂)

/-- The budget in the class `{1/3, 2/3}`: `n - 2` for the values `1` and `n - 2`, `n - 3` for the other integer
values, `1` for the others. -/
def BA (n : ℕ) : ℕ ⊕ (ℕ × Bool) → ℕ
  | Sum.inl N => n - 3 + (if N = 1 then 1 else 0) + (if N = n - 2 then 1 else 0)
  | Sum.inr _ => 1

/-- The key in the class `{2/3, 4/3}`: `|K| - 1` for the `X`-parts `(1,1)`, `(0,0)` (value `|K|`). -/
def keyB (c : ℕ) (e₁ e₂ : Bool) : ℕ ⊕ (ℕ × Bool) :=
  if e₁ = e₂ then Sum.inl (c - 1) else Sum.inr (c, e₁)

/-- The value of a key in the class `{2/3, 4/3}`. -/
noncomputable def fB (g₁ g₂ : ℝ) : ℕ ⊕ (ℕ × Bool) → ℝ
  | Sum.inl N => N + 1
  | Sum.inr τ => τ.1 + (if τ.2 then g₁ else g₂)

/-- The budget in the class `{2/3, 4/3}`: `max(j, (n-2) - j)` for the integer value `j + 1`, `1` for the others. -/
def BB (n : ℕ) : ℕ ⊕ (ℕ × Bool) → ℕ
  | Sum.inl N => max N (n - 2 - N)
  | Sum.inr _ => 1

theorem sum_mixed (n : ℕ) (B : ℕ ⊕ (ℕ × Bool) → ℕ) (hB : ∀ τ, B (Sum.inr τ) = 1) :
    ∑ τ ∈ (Finset.Icc 2 (n - 1)) ×ˢ (Finset.univ : Finset Bool), B (Sum.inr τ) = (n - 2) * 2 := by
  simp only [hB, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_product, Nat.card_Icc, Finset.card_univ,
    Fintype.card_bool]
  rw [show n - 1 + 1 - 2 = n - 2 by omega]

theorem sum_BA (n : ℕ) (hn : 4 ≤ n) : ∑ τ ∈ slots n, BA n τ = (n - 2) * (n - 3) + 2 + (n - 2) * 2 := by
  rw [slots, Finset.sum_disjSum, sum_mixed n (BA n) (fun _ => rfl)]
  have h1 : ∑ N ∈ Finset.Icc 1 (n - 2), BA n (Sum.inl N) = (n - 2) * (n - 3) + 2 := by
    simp only [BA]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq',
      Finset.sum_ite_eq', ite_eq_left (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩),
      ite_eq_left (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩), Nat.card_Icc, smul_eq_mul,
      show n - 2 + 1 - 1 = n - 2 by omega]
  rw [h1]

theorem sum_BB (n : ℕ) (hn : 4 ≤ n) : ∑ τ ∈ slots n, BB n τ ≤ (n - 2 - 1) ^ 2 + (n - 2) + (n - 2) * 2 := by
  rw [slots, Finset.sum_disjSum, sum_mixed n (BB n) (fun _ => rfl)]
  have h1 : ∑ N ∈ Finset.Icc 1 (n - 2), BB n (Sum.inl N) ≤ (n - 2 - 1) ^ 2 + (n - 2) := by
    simp only [BB]
    exact prop_5_12_sum_proved (n - 2) (by omega)
  omega

theorem visit_A {n L c : ℕ} {e₁ e₂ : Bool} {v g₁ g₂ : ℝ} (hn : 4 ≤ n) (hsum : g₁ + g₂ = -1)
    (hg₁ : g₁ ≤ -1 / 3) (hg₂ : g₂ ≤ -1 / 3) (hV : Visit n g₁ g₂ L c e₁ e₂ v) (hv : 1 ≤ v) :
    v = fA g₁ g₂ (keyA c e₁ e₂) ∧ keyA c e₁ e₂ ∈ slots n ∧ L ≤ BA n (keyA c e₁ e₂) := by
  obtain ⟨hval, hpos, hlt, h00, hc11, hL11, hL00, hLmix⟩ := hV
  cases e₁ <;> cases e₂ <;>
    simp only [keyA, fA, BA, slots, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Finset.inl_mem_disjSum,
      Finset.inr_mem_disjSum, Finset.mem_Icc, Finset.mem_product, Finset.mem_univ, and_true, mul_one, mul_zero,
      add_zero] at hval ⊢
  · -- `X`-part `(0,0)`: the value is `|K|`
    have h := h00 rfl rfl
    have hL := hL00 rfl rfl
    refine ⟨hval, ⟨hpos, h⟩, le_trans hL (max_le ?_ ?_)⟩ <;> split_ifs <;> omega
  · -- `X`-part `(0,1)`
    have hc : 2 ≤ c := by
      have h1 : (1 : ℝ) < c := by linarith
      have : 1 < c := by exact_mod_cast h1
      omega
    exact ⟨hval, ⟨hc, hlt⟩, hLmix (by decide)⟩
  · -- `X`-part `(1,0)`
    have hc : 2 ≤ c := by
      have h1 : (1 : ℝ) < c := by linarith
      have : 1 < c := by exact_mod_cast h1
      omega
    exact ⟨hval, ⟨hc, hlt⟩, hLmix (by decide)⟩
  · -- `X`-part `(1,1)`: the value is `|K| - 1`
    have h := hc11 rfl rfl
    have hL := hL11 rfl rfl
    refine ⟨?_, ⟨by omega, by omega⟩, le_trans hL (max_le ?_ ?_)⟩
    · rw [Nat.cast_sub (by omega : 1 ≤ c), hval]
      push_cast
      linarith
    all_goals split_ifs <;> omega

theorem visit_B {n L c : ℕ} {e₁ e₂ : Bool} {v g₁ g₂ : ℝ} (hsum : g₁ + g₂ = 0)
    (hg₁ : g₁ ≤ 1 / 3) (hg₂ : g₂ ≤ 1 / 3) (hV : Visit n g₁ g₂ L c e₁ e₂ v) (hv : 5 / 3 ≤ v) :
    v = fB g₁ g₂ (keyB c e₁ e₂) ∧ keyB c e₁ e₂ ∈ slots n ∧ L ≤ BB n (keyB c e₁ e₂) := by
  obtain ⟨hval, hpos, hlt, h00, hc11, hL11, hL00, hLmix⟩ := hV
  cases e₁ <;> cases e₂ <;>
    simp only [keyB, fB, BB, slots, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Finset.inl_mem_disjSum,
      Finset.inr_mem_disjSum, Finset.mem_Icc, Finset.mem_product, Finset.mem_univ, and_true, mul_one, mul_zero,
      add_zero] at hval ⊢
  · -- `X`-part `(0,0)`: the value is `|K|`
    have h := h00 rfl rfl
    have hL := hL00 rfl rfl
    have hc : 2 ≤ c := by
      have h1 : (1 : ℝ) < c := by linarith
      have : 1 < c := by exact_mod_cast h1
      omega
    refine ⟨?_, ⟨by omega, by omega⟩, le_trans hL (max_le (le_max_of_le_right (by omega))
      (le_max_of_le_left (by omega)))⟩
    rw [Nat.cast_sub (by omega : 1 ≤ c), hval]
    push_cast
    ring
  · -- `X`-part `(0,1)`
    have hc : 2 ≤ c := by
      have h1 : (1 : ℝ) < c := by linarith
      have : 1 < c := by exact_mod_cast h1
      omega
    exact ⟨hval, ⟨hc, hlt⟩, hLmix (by decide)⟩
  · -- `X`-part `(1,0)`
    have hc : 2 ≤ c := by
      have h1 : (1 : ℝ) < c := by linarith
      have : 1 < c := by exact_mod_cast h1
      omega
    exact ⟨hval, ⟨hc, hlt⟩, hLmix (by decide)⟩
  · -- `X`-part `(1,1)`: the value is `|K|`
    have h := hc11 rfl rfl
    have hL := hL11 rfl rfl
    refine ⟨?_, ⟨by omega, by omega⟩, le_trans hL (max_le (le_max_left _ _) (le_max_of_le_left (by omega)))⟩
    rw [Nat.cast_sub (by omega : 1 ≤ c), hval]
    push_cast
    linarith

theorem count_A (n J : ℕ) (hn : 4 ≤ n) (L c : ℕ → ℕ) (e₁ e₂ : ℕ → Bool) (v : ℕ → ℝ) (g₁ g₂ : ℝ)
    (hsum : g₁ + g₂ = -1) (hg₁ : g₁ ≤ -1 / 3) (hg₂ : g₂ ≤ -1 / 3) (hmono : ∀ i j, i < j → j < J → v i < v j)
    (hvis : ∀ j < J, Visit n g₁ g₂ (L j) (c j) (e₁ j) (e₂ j) (v j)) (hv : ∀ j < J, 1 ≤ v j) :
    ∑ j ∈ Finset.range J, L j ≤ (n - 2) * (n - 3) + 2 + (n - 2) * 2 := by
  have h := fun j (hj : j < J) => visit_A hn hsum hg₁ hg₂ (hvis j hj) (hv j hj)
  rw [← sum_BA n hn]
  exact slot_sum v L J hmono (fun j => keyA (c j) (e₁ j) (e₂ j)) (fA g₁ g₂) (fun j hj => (h j hj).1) (slots n)
    (BA n) (fun j hj => (h j hj).2.1) (fun j hj => (h j hj).2.2)

theorem count_B (n J : ℕ) (hn : 4 ≤ n) (L c : ℕ → ℕ) (e₁ e₂ : ℕ → Bool) (v : ℕ → ℝ) (g₁ g₂ : ℝ)
    (hsum : g₁ + g₂ = 0) (hg₁ : g₁ ≤ 1 / 3) (hg₂ : g₂ ≤ 1 / 3) (hmono : ∀ i j, i < j → j < J → v i < v j)
    (hvis : ∀ j < J, Visit n g₁ g₂ (L j) (c j) (e₁ j) (e₂ j) (v j)) (hv : ∀ j < J, 5 / 3 ≤ v j) :
    ∑ j ∈ Finset.range J, L j ≤ (n - 2 - 1) ^ 2 + (n - 2) + (n - 2) * 2 := by
  have h := fun j (hj : j < J) => visit_B hsum hg₁ hg₂ (hvis j hj) (hv j hj)
  refine le_trans ?_ (sum_BB n hn)
  exact slot_sum v L J hmono (fun j => keyB (c j) (e₁ j) (e₂ j)) (fB g₁ g₂) (fun j hj => (h j hj).1) (slots n)
    (BB n) (fun j hj => (h j hj).2.1) (fun j hj => (h j hj).2.2)

/-- A lower bound on the first value is a lower bound on all values. -/
theorem lower_all {v : ℕ → ℝ} {J : ℕ} {m : ℝ} (hmono : ∀ i j, i < j → j < J → v i < v j) (h0 : m ≤ v 0) :
    ∀ j < J, m ≤ v j := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | h
  · exact h0
  · exact h0.trans (hmono 0 j h hj).le

/-! #### Arithmetic -/

theorem arith_A {n : ℕ} (hn : 4 ≤ n) : (n - 2) * (n - 3) + 2 + (n - 2) * 2 + 1 ≤ n ^ 2 + 5 - 3 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
  have h : (m + 4) ^ 2 + 5 = (m + 2) * (m + 1) + 2 + (m + 2) * 2 + 1 + 3 * (m + 4) := by ring
  omega

theorem arith_B {n : ℕ} (hn : 4 ≤ n) : (n - 2 - 1) ^ 2 + (n - 2) + (n - 2) * 2 + 1 ≤ n ^ 2 + 5 - 3 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 2 - 1 = m + 1 by omega, show m + 4 - 2 = m + 2 by omega]
  have h : (m + 4) ^ 2 + 5 = (m + 1) ^ 2 + (m + 2) + (m + 2) * 2 + 1 + 1 + 3 * (m + 4) := by ring
  omega

theorem arith_B_exact {n : ℕ} (hn : 4 ≤ n) : (n - 2 - 1) ^ 2 + (n - 2) + (n - 2) * 2 + 1 = n ^ 2 + 4 - 3 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 2 - 1 = m + 1 by omega, show m + 4 - 2 = m + 2 by omega]
  have h : (m + 4) ^ 2 + 4 = (m + 1) ^ 2 + (m + 2) + (m + 2) * 2 + 1 + 3 * (m + 4) := by ring
  omega

theorem arith_512 {n : ℕ} (hn : 4 ≤ n) : n ^ 2 + 5 - 3 * n ≤ (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega]
  have h : (m + 4) ^ 2 + 5 + m = (m + 3) ^ 2 + 3 * (m + 4) := by ring
  omega

theorem arith_511 {n S : ℕ} (h : S ≤ (n - 2) * n) : S + 1 ≤ 1 + (n - 2) * n := by
  omega

/-! ### The automaton -/

open Classical Automaton Matrix

section Auto

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

omit [Fintype Q] [Fintype S] in
theorem tgt_configOf (a b : S) (E : Finset Q) (x₁ x₂ : Q) (i c : Fin 2) :
    (A.configOf a b E x₁ x₂).tgt i c = stateCode x₁ x₂ (A.step (![x₁, x₂] i) (![a, b] c)) := by
  fin_cases i <;> fin_cases c <;> rfl

theorem x_notMem_E (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) {x : Q}
    (hx : x ∈ ({x₁, x₂} : Finset Q)) : x ∉ W.E := by
  rw [← hX] at hx
  exact (Finset.mem_sdiff.mp hx).2

theorem mem_E_of_ne (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) {q : Q} (h1 : q ≠ x₁)
    (h2 : q ≠ x₂) : q ∈ W.E := by
  by_contra hq
  have h : q ∈ W.X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq⟩
  rw [hX] at h
  simp [h1, h2] at h

theorem x_ne_s (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) : x₁ ≠ W.s ∧ x₂ ≠ W.s :=
  ⟨fun h => x_notMem_E A W hX (by simp : x₁ ∈ ({x₁, x₂} : Finset Q)) (h ▸ W.s_mem),
    fun h => x_notMem_E A W hX (by simp : x₂ ∈ ({x₁, x₂} : Finset Q)) (h ▸ W.s_mem)⟩

/-- Every edge from `X` ends at `s` or in `X`. -/
theorem step_three (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (c : S) {x : Q}
    (hx : x ∈ ({x₁, x₂} : Finset Q)) : A.step x c = W.s ∨ A.step x c ∈ ({x₁, x₂} : Finset Q) := by
  rcases W.edge_X x (x_notMem_E A W hX hx) c with h | h
  · right
    rw [← hX]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩
  · exact Or.inl h

omit [Fintype S] in
theorem exists_pattern {x₁ x₂ s : Q} (h12 : x₁ ≠ x₂) (h1s : x₁ ≠ s) (h2s : x₂ ≠ s)
    (P : Bool × Bool × Bool) : ∃ K : Finset Q, pattern x₁ x₂ s K = P := by
  obtain ⟨b₁, b₂, b₃⟩ := P
  refine ⟨Finset.univ.filter (fun q => (q = x₁ ∧ b₁ = true) ∨ (q = x₂ ∧ b₂ = true) ∨ (q = s ∧ b₃ = true)), ?_⟩
  simp [pattern, h12, h12.symm, h1s, h2s, h1s.symm, h2s.symm]

omit [Fintype Q] [Fintype S] in
/-- Membership of a state of `{x₁, x₂, s}` is the bit of the pattern at its code. -/
theorem mem_iff_bit {x₁ x₂ s y : Q} (h12 : x₁ ≠ x₂) (h1s : x₁ ≠ s) (h2s : x₂ ≠ s) (K : Finset Q)
    (hy : y = s ∨ y ∈ ({x₁, x₂} : Finset Q)) :
    (y ∈ K ↔ bit (pattern x₁ x₂ s K) (stateCode x₁ x₂ y) = true) := by
  rcases hy with rfl | hy
  · simp [stateCode, h1s.symm, h2s.symm, bit, pattern]
  · rcases Finset.mem_insert.mp hy with rfl | hy
    · simp [stateCode, bit, pattern]
    · rw [Finset.mem_singleton] at hy
      subst hy
      simp [stateCode, h12.symm, bit, pattern]

omit [Fintype Q] [Fintype S] in
theorem ein_cases (x : Q) (K : Finset Q) : ein x K = 0 ∨ ein x K = 1 := by
  unfold ein
  split_ifs <;> simp

/-- A configuration all of whose non-aligned patterns are good gives good patterns of the automaton. -/
theorem good_of_allGood {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcf : AllGood (A.configOf a b W.E x₁ x₂)) (P : Bool × Bool × Bool) (hP : ¬ Aligned P) :
    Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P := by
  obtain ⟨h1s, h2s⟩ := x_ne_s A W hX
  obtain ⟨c, hc⟩ := hcf P (fun h => hP (Or.inl h)) (fun h => hP (Or.inr h))
  obtain ⟨K, hK⟩ := exists_pattern h12 h1s h2s P
  refine ⟨![a, b] c, K, hK, ?_⟩
  have ht := (lem_5_7_b_proved A a b hab hS W x₁ x₂ hX h12).2.2.2.2 hsc
  have ht0 : A.alphaStat W.E (fun _ => 1 / 2) x₁ = (((A.configOf a b W.E x₁ x₂).t 0 : ℚ) : ℝ) := ht 0
  have ht1 : A.alphaStat W.E (fun _ => 1 / 2) x₂ = (((A.configOf a b W.E x₁ x₂).t 1 : ℚ) : ℝ) := ht 1
  have hein : ∀ i : Fin 2, ein (![x₁, x₂] i) (A.pre K [![a, b] c]) =
      ((bq (bit P ((A.configOf a b W.E x₁ x₂).tgt i c)) : ℚ) : ℝ) := by
    intro i
    have hx : ![x₁, x₂] i ∈ ({x₁, x₂} : Finset Q) := by fin_cases i <;> simp
    have hiff := mem_iff_bit h12 h1s h2s K (step_three A W hX (![a, b] c) hx)
    rw [hK] at hiff
    rw [tgt_configOf]
    simp only [ein, mem_pre, act_singleton, bq]
    by_cases hm : A.step (![x₁, x₂] i) (![a, b] c) ∈ K
    · rw [ite_eq_left hm, ite_eq_left (hiff.mp hm)]
      norm_num
    · rw [ite_eq_right hm, ite_eq_right (fun h => hm (hiff.mpr h))]
      norm_num
  have h0 := hein 0
  have h1 := hein 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have he1 : ein x₁ K = ((bq P.1 : ℚ) : ℝ) := by
    rw [← hK]
    by_cases h : x₁ ∈ K <;> simp [ein, pattern, bq, h]
  have he2 : ein x₂ K = ((bq P.2.1 : ℚ) : ℝ) := by
    rw [← hK]
    by_cases h : x₂ ∈ K <;> simp [ein, pattern, bq, h]
  rw [ht0, ht1, h0, h1, he1, he2]
  rintro ⟨z, hz⟩
  apply hc
  have hq : chg (A.configOf a b W.E x₁ x₂) P c = z := by
    have hr : ((chg (A.configOf a b W.E x₁ x₂) P c : ℚ) : ℝ) = (z : ℝ) := by
      rw [← hz]
      simp only [chg]
      push_cast
      ring
    exact_mod_cast hr
  rw [hq]
  exact Rat.den_intCast z

/-- In the classes of Proposition 5.11 the configuration is a renaming of one of the two of the paper. -/
theorem cf_mem_511 {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ))) :
    A.configOf a b W.E x₁ x₂ ∈
      (⟨2, 2, 2, 0, 1, 1⟩ : Config).renamings ∪ (⟨2, 2, 2, 0, 0, 1⟩ : Config).renamings := by
  obtain ⟨hch, hv⟩ := sec54_config_valid_proved A a b hab hS hsc W x₁ x₂ hX h12
  have ht := (lem_5_7_b_proved A a b hab hS W x₁ x₂ hX h12).2.2.2.2 hsc
  have ht0 : A.alphaStat W.E (fun _ => 1 / 2) x₁ = (((A.configOf a b W.E x₁ x₂).t 0 : ℚ) : ℝ) := ht 0
  have ht1 : A.alphaStat W.E (fun _ => 1 / 2) x₂ = (((A.configOf a b W.E x₁ x₂).t 1 : ℚ) : ℝ) := ht 1
  rw [ht0, ht1] at hcl
  generalize A.configOf a b W.E x₁ x₂ = cf at hch hv hcl ⊢
  have hself : cf ∈ cf.renamings := by simp [Config.renamings]
  obtain ⟨k1, k2, -⟩ := prop_5_11_config_proved
  have hA : cf.cls = (1/2, 3/4) → cf.renamings = (⟨2, 2, 2, 0, 1, 1⟩ : Config).renamings := by
    intro hk
    have hm := Finset.mem_image_of_mem Config.renamings
      (Finset.mem_filter.mpr ⟨hch, hv, hk⟩ : cf ∈ choices.filter (fun c => c.Valid ∧ c.cls = (1/2, 3/4)))
    rw [k1, Finset.mem_singleton] at hm
    exact hm
  have hB : cf.cls = (1/4, 1/2) → cf.renamings = (⟨2, 2, 2, 0, 0, 1⟩ : Config).renamings := by
    intro hk
    have hm := Finset.mem_image_of_mem Config.renamings
      (Finset.mem_filter.mpr ⟨hch, hv, hk⟩ : cf ∈ choices.filter (fun c => c.Valid ∧ c.cls = (1/4, 1/2)))
    rw [k2, Finset.mem_singleton] at hm
    exact hm
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcl
  rcases hcl with ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩
  · have q0 : cf.t 0 = 1/2 := Rat.cast_injective (α := ℝ) (by rw [e0]; norm_num)
    have q1 : cf.t 1 = 3/4 := Rat.cast_injective (α := ℝ) (by rw [e1]; norm_num)
    have hr := hA (by simp only [Config.cls, q0, q1]; norm_num)
    exact Finset.mem_union_left _ (by rw [← hr]; exact hself)
  · have q0 : cf.t 0 = 3/4 := Rat.cast_injective (α := ℝ) (by rw [e0]; norm_num)
    have q1 : cf.t 1 = 1/2 := Rat.cast_injective (α := ℝ) (by rw [e1]; norm_num)
    have hr := hA (by simp only [Config.cls, q0, q1]; norm_num)
    exact Finset.mem_union_left _ (by rw [← hr]; exact hself)
  · have q0 : cf.t 0 = 1/4 := Rat.cast_injective (α := ℝ) (by rw [e0]; norm_num)
    have q1 : cf.t 1 = 1/2 := Rat.cast_injective (α := ℝ) (by rw [e1]; norm_num)
    have hr := hB (by simp only [Config.cls, q0, q1]; norm_num)
    exact Finset.mem_union_right _ (by rw [← hr]; exact hself)
  · have q0 : cf.t 0 = 1/2 := Rat.cast_injective (α := ℝ) (by rw [e0]; norm_num)
    have q1 : cf.t 1 = 1/4 := Rat.cast_injective (α := ℝ) (by rw [e1]; norm_num)
    have hr := hB (by simp only [Config.cls, q0, q1]; norm_num)
    exact Finset.mem_union_right _ (by rw [← hr]; exact hself)

/-- In the configurations of Proposition 5.12, `(t₁, t₂)` is one of four pairs. -/
theorem t_512 {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcf : A.configOf a b W.E x₁ x₂ ∈ (⟨2, 1, 0, 2, 0, 1⟩ : Config).renamings ∪
      (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings) :
    (A.alphaStat W.E (fun _ => 1 / 2) x₁ = 1/3 ∧ A.alphaStat W.E (fun _ => 1 / 2) x₂ = 2/3) ∨
      (A.alphaStat W.E (fun _ => 1 / 2) x₁ = 2/3 ∧ A.alphaStat W.E (fun _ => 1 / 2) x₂ = 1/3) ∨
      (A.alphaStat W.E (fun _ => 1 / 2) x₁ = 2/3 ∧ A.alphaStat W.E (fun _ => 1 / 2) x₂ = 4/3) ∨
      (A.alphaStat W.E (fun _ => 1 / 2) x₁ = 4/3 ∧ A.alphaStat W.E (fun _ => 1 / 2) x₂ = 2/3) := by
  have ht := (lem_5_7_b_proved A a b hab hS W x₁ x₂ hX h12).2.2.2.2 hsc
  have ht0 : A.alphaStat W.E (fun _ => 1 / 2) x₁ = (((A.configOf a b W.E x₁ x₂).t 0 : ℚ) : ℝ) := ht 0
  have ht1 : A.alphaStat W.E (fun _ => 1 / 2) x₂ = (((A.configOf a b W.E x₁ x₂).t 1 : ℚ) : ℝ) := ht 1
  rw [ht0, ht1]
  rcases (facts_512 _ hcf).2 with ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rw [e0, e1] <;> norm_num

/-- The weights `(1/2, 1/2)` and the positive stationary vector of Lemma 5.5 for them. -/
theorem half_facts {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) :
    IsLetterWeights (fun _ : S => (1 : ℝ) / 2) ∧
      A.IsStationary (fun _ => 1 / 2) (A.alphaStat W.E (fun _ => 1 / 2)) ∧
      ∀ q, 0 < A.alphaStat W.E (fun _ => 1 / 2) q := by
  obtain ⟨W', hE, -, hp⟩ := lem_5_7_a_proved A a b hab hS W
  obtain ⟨-, hst, hpos⟩ := lem_5_5_proved A hsc W'
  have hw := W'.weights
  rw [hE, hp] at hst hpos
  rw [hp] at hw
  exact ⟨hw, hst, hpos⟩

/-- The length of a word of length `m(K)` for a visited set `K`, by its pattern (Lemma 5.10 and good patterns). -/
theorem len_bound (hsc : A.StronglyConnected) (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hgood : ∀ P, ¬ Aligned P → Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1)
      (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P)
    (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ) (w : List S)
    (hw : (w.length : ℕ∞) = A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K) :
    (x₁ ∈ K → x₂ ∈ K → w.length ≤ max (K.card - 1) 1) ∧
      (x₁ ∉ K → x₂ ∉ K → w.length ≤ max (Fintype.card Q - K.card - 1) 1) ∧
      ((x₁ ∈ K ∧ x₂ ∉ K) ∨ (x₁ ∉ K ∧ x₂ ∈ K) → w.length ≤ 1) := by
  have hc1 : ∀ P, ¬ Aligned P → pattern x₁ x₂ W.s K = P → w.length ≤ 1 := by
    intro P hP hK
    have h := (sec54_good_cost1_proved A W x₁ x₂ hX h12 P).2 (hgood P hP) K hK
    rw [h] at hw
    have : w.length = 1 := by exact_mod_cast hw
    omega
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · by_cases hs : W.s ∈ K
    · have hP : pattern x₁ x₂ W.s K = (true, true, true) := by simp [pattern, h1, h2, hs]
      have h := (lem_5_10_a_proved A hsc W x₁ x₂ hX h12 K hne hprop hP).2.2
        (hgood (true, true, false) (by simp [Aligned]))
      rw [← hw] at h
      have : w.length ≤ K.card - 1 := by exact_mod_cast h
      exact le_max_of_le_left this
    · exact le_max_of_le_right (hc1 (true, true, false) (by simp [Aligned]) (by simp [pattern, h1, h2, hs]))
  · by_cases hs : W.s ∈ K
    · exact le_max_of_le_right (hc1 (false, false, true) (by simp [Aligned]) (by simp [pattern, h1, h2, hs]))
    · have hP : pattern x₁ x₂ W.s K = (false, false, false) := by simp [pattern, h1, h2, hs]
      have h := (lem_5_10_b_proved A hsc W x₁ x₂ hX h12 K hne hprop hP).2
        (hgood (false, false, true) (by simp [Aligned]))
      rw [← hw] at h
      have : w.length ≤ Fintype.card Q - K.card - 1 := by exact_mod_cast h
      exact le_max_of_le_left this
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hc1 _ (by simp [Aligned, pattern, h1, h2]) rfl
    · exact hc1 _ (by simp [Aligned, pattern, h1, h2]) rfl

/-- The facts on a visited set. -/
theorem visit_of (hsc : A.StronglyConnected) (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hgood : ∀ P, ¬ Aligned P → Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1)
      (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P)
    (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ) (w : List S)
    (hw : (w.length : ℕ∞) = A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K) :
    Visit (Fintype.card Q) (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1)
      w.length K.card (decide (x₁ ∈ K)) (decide (x₂ ∈ K)) (wt (A.alphaStat W.E (fun _ => 1 / 2)) K) := by
  obtain ⟨hb11, hb00, hbmix⟩ := len_bound A hsc W hX h12 hgood K hne hprop w hw
  refine ⟨?_, Finset.card_pos.mpr hne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sec54_alpha_formula_proved A W x₁ x₂ hX h12 K]
    simp [ein]
  · have := (Finset.card_lt_iff_ne_univ K).mpr hprop
    omega
  · intro h1 h2
    simp only [decide_eq_false_iff_not] at h1 h2
    have hsub : K ⊆ W.E := fun q hq => mem_E_of_ne A W hX (fun h => h1 (h ▸ hq)) (fun h => h2 (h ▸ hq))
    have := Finset.card_le_card hsub
    rw [W.card_E] at this
    exact this
  · intro h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    have hsub : ({x₁, x₂} : Finset Q) ⊆ K := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair h12] at this
  · intro h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    exact hb11 h1 h2
  · intro h1 h2
    simp only [decide_eq_false_iff_not] at h1 h2
    exact hb00 h1 h2
  · intro h
    apply hbmix
    by_cases h1 : x₁ ∈ K <;> by_cases h2 : x₂ ∈ K <;> simp_all

/-- Some edge goes from `X` to `s` (else `X` would be closed). -/
theorem exists_to_s (hsc : A.StronglyConnected) (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) :
    ∃ x ∈ ({x₁, x₂} : Finset Q), ∃ c : S, A.step x c = W.s := by
  by_contra h
  push Not at h
  have hcl : A.IsClosed ({x₁, x₂} : Finset Q) := by
    intro q hq c
    rcases step_three A W hX c hq with h' | h'
    · exact absurd h' (h q hq c)
    · exact h'
  obtain ⟨h1s, h2s⟩ := x_ne_s A W hX
  rcases hsc _ hcl with h0 | h0
  · exact absurd h0 (Finset.insert_ne_empty x₁ {x₂})
  · have hs : W.s ∈ ({x₁, x₂} : Finset Q) := h0 ▸ Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h' | h'
    · exact h1s h'.symm
    · exact h2s h'.symm

/-- `α({s} a⁻¹) + α({s} b⁻¹) = 2 α(s) = 2` (stationarity at `s`). -/
theorem sum_pre_s {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2)
    (hst : A.IsStationary (fun _ => 1 / 2) (A.alphaStat W.E (fun _ => 1 / 2))) :
    wt (A.alphaStat W.E (fun _ => 1 / 2)) (A.pre {W.s} [a]) +
      wt (A.alphaStat W.E (fun _ => 1 / 2)) (A.pre {W.s} [b]) = 2 := by
  obtain ⟨h1, h2⟩ := eq_2_1_proved A (fun _ => 1 / 2) _ hst {W.s}
  have hu : (Finset.univ : Finset S) = {a, b} := by
    ext c
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hS c
  rw [h2, hu, Finset.sum_pair hab] at h1
  have hs : wt (A.alphaStat W.E (fun _ => 1 / 2)) {W.s} = 1 := by
    rw [wt, Finset.sum_singleton]
    have : W.s ∉ Finset.univ \ W.E := fun h => (Finset.mem_sdiff.mp h).2 W.s_mem
    simp [Automaton.alphaStat, this]
  rw [hs] at h1
  linarith

/-- A value that contains `x₁` or `x₂` is not an integer when `g₁`, `g₂`, `g₁ + g₂` are not. -/
theorem not_int_wt {g₁ g₂ : ℝ} (h1 : ∀ z : ℤ, g₁ ≠ z) (h2 : ∀ z : ℤ, g₂ ≠ z) (h12 : ∀ z : ℤ, g₁ + g₂ ≠ z)
    (k : ℕ) (e₁ e₂ : ℝ) (he₁ : e₁ = 0 ∨ e₁ = 1) (he₂ : e₂ = 0 ∨ e₂ = 1) (hne : e₁ = 1 ∨ e₂ = 1) :
    ∀ z : ℤ, (k : ℝ) + g₁ * e₁ + g₂ * e₂ ≠ z := by
  intro z hz
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · rcases hne with h | h <;> norm_num at h
  · exact h2 (z - k) (by push_cast; linarith)
  · exact h1 (z - k) (by push_cast; linarith)
  · exact h12 (z - k) (by push_cast; linarith)

theorem not_int_of_mem (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hi₁ : ∀ z : ℤ, A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1 ≠ z)
    (hi₂ : ∀ z : ℤ, A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1 ≠ z)
    (hi₁₂ : ∀ z : ℤ, A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1 + (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) ≠ z) :
    ∀ K : Finset Q, (x₁ ∈ K ∨ x₂ ∈ K) → ∀ z : ℤ, wt (A.alphaStat W.E (fun _ => 1 / 2)) K ≠ z := by
  intro K hK
  rw [sec54_alpha_formula_proved A W x₁ x₂ hX h12 K]
  refine not_int_wt hi₁ hi₂ hi₁₂ K.card _ _ (ein_cases x₁ K) (ein_cases x₂ K) ?_
  rcases hK with h | h
  · left
    simp [ein, h]
  · right
    simp [ein, h]

/-- The start of Proposition 5.11: a letter `d` with `α({s} d⁻¹) > 1`. -/
theorem exists_start {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂})
    (hst : A.IsStationary (fun _ => 1 / 2) (A.alphaStat W.E (fun _ => 1 / 2)))
    (hnot : ∀ K : Finset Q, (x₁ ∈ K ∨ x₂ ∈ K) → ∀ z : ℤ, wt (A.alphaStat W.E (fun _ => 1 / 2)) K ≠ z) :
    ∃ d : S, 1 < wt (A.alphaStat W.E (fun _ => 1 / 2)) (A.pre {W.s} [d]) := by
  obtain ⟨x, hx, c, hc⟩ := exists_to_s A hsc W hX
  have hsum := sum_pre_s A hab hS W hst
  by_contra h
  push Not at h
  have ha := h a
  have hb := h b
  have hxc : x ∈ A.pre {W.s} [c] := by simp [hc]
  have hxK : x₁ ∈ A.pre {W.s} [c] ∨ x₂ ∈ A.pre {W.s} [c] := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hxc
    · exact Or.inr hxc
  rcases hS c with rfl | rfl
  · exact hnot _ hxK 1 (by push_cast; linarith)
  · exact hnot _ hxK 1 (by push_cast; linarith)

/-- The numbers `g₁, g₂` of Proposition 5.11. -/
theorem g_511 {t₁ t₂ : ℝ}
    (hcl : (t₁, t₂) ∈ ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ))) :
    t₁ - 1 ≤ 0 ∧ t₂ - 1 ≤ 0 ∧ (∀ z : ℤ, t₁ - 1 ≠ z) ∧ (∀ z : ℤ, t₂ - 1 ≠ z) ∧
      (∀ z : ℤ, t₁ - 1 + (t₂ - 1) ≠ z) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcl
  rcases hcl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine ⟨by norm_num, by norm_num, not_int_of_between (-1) (by norm_num) (by norm_num),
      not_int_of_between (-1) (by norm_num) (by norm_num), ?_⟩
  · exact not_int_of_between (-1) (by norm_num) (by norm_num)
  · exact not_int_of_between (-1) (by norm_num) (by norm_num)
  · exact not_int_of_between (-2) (by norm_num) (by norm_num)
  · exact not_int_of_between (-2) (by norm_num) (by norm_num)

omit [Fintype Q] [DecidableEq Q] in
theorem nonempty_of_wt_pos {α : Q → ℝ} {K : Finset Q} (h : 0 < wt α K) : K.Nonempty := by
  rcases K.eq_empty_or_nonempty with hK | hK
  · rw [hK, wt_empty] at h
    exact absurd h (lt_irrefl 0)
  · exact hK

/-- `|K| + m ≤ α(K)` when `m` is below `0`, `g₁`, `g₂` and `g₁ + g₂`. -/
theorem wt_lower {g₁ g₂ m : ℝ} (h0 : m ≤ 0) (h1 : m ≤ g₁) (h2 : m ≤ g₂) (h12 : m ≤ g₁ + g₂) (k : ℝ)
    (e₁ e₂ : ℝ) (he₁ : e₁ = 0 ∨ e₁ = 1) (he₂ : e₂ = 0 ∨ e₂ = 1) : k + m ≤ k + g₁ * e₁ + g₂ * e₂ := by
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;> linarith

end Auto

end Props511

open Classical Automaton Matrix

section Binary

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- Proposition 5.11, tex:817-819: in these classes every pattern that is not aligned is good. -/
theorem prop_5_11_good_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (_hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ)))
    (P : Bool × Bool × Bool) (hP : ¬ Aligned P) :
    Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P :=
  Props511.good_of_allGood A hab hS hsc W hX h12
    (Props511.allGood_511 _ (Props511.cf_mem_511 A hab hS hsc W hX h12 hcl)) P hP

/-- Proposition 5.11, tex:806-808. If the witness has class {1/2,3/4} or {1/4,1/2}, the bound is 1+(n−2)n. -/
theorem prop_5_11_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((1 + (Fintype.card Q - 2) * Fintype.card Q : ℕ) : ℕ∞) := by
  have hgood := prop_5_11_good_proved A a b hab hS hsc hn W x₁ x₂ hX h12 hcl
  obtain ⟨hp, hst, hpos⟩ := Props511.half_facts A hab hS hsc W
  obtain ⟨hg₁, hg₂, hi₁, hi₂, hi₁₂⟩ := Props511.g_511 hcl
  have hnot := Props511.not_int_of_mem A W hX h12 hi₁ hi₂ hi₁₂
  obtain ⟨d, hd⟩ := Props511.exists_start A hab hS hsc W hX hst hnot
  have hne0 : (A.pre {W.s} [d]).Nonempty := Props511.nonempty_of_wt_pos (by linarith)
  obtain ⟨K, w, J, hK0, hP⟩ := sec54_process_exists_proved A hA _ hp _ hst hpos _ hne0
  have hK0ne : (K 0).Nonempty := hK0 ▸ hne0
  obtain ⟨hmono, -, hnej, -, -, hmerge⟩ := sec54_process_props_proved A _ hpos K w J hP hK0ne
  refine (hmerge W.s d hK0).trans (Nat.cast_le.mpr ?_)
  have hmono' : ∀ i j, i < j → j < J →
      wt (A.alphaStat W.E (fun _ => 1 / 2)) (K i) < wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j) :=
    fun i j hij hj => hmono i j hij hj.le
  have hv : ∀ j < J, 1 < wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | h
    · rw [hK0]
      exact hd
    · have := hmono' 0 j h hj
      rw [hK0] at this
      linarith
  have hvis := fun j (hj : j < J) => Props511.visit_of A hsc W hX h12 hgood (K j) (hnej j hj.le)
    (hP.1 j hj).1 (w j) (hP.1 j hj).2.2.1
  have hsum : ∑ j ∈ Finset.range J, (w j).length ≤ (Fintype.card Q - 2) * Fintype.card Q :=
    Props511.count_511 (Fintype.card Q) J (fun j => (w j).length) (fun j => (K j).card)
      (fun j => decide (x₁ ∈ K j)) (fun j => decide (x₂ ∈ K j))
      (fun j => wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j)) _ _ hg₁ hg₂ hmono' hvis hv
  exact Props511.arith_511 hsum

/-- Proposition 5.12, tex:845-849: in these configurations every pattern that is not aligned is good. -/
theorem prop_5_12_good_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (_hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcf : A.configOf a b W.E x₁ x₂ ∈ (⟨2, 1, 0, 2, 0, 1⟩ : Config).renamings ∪
      (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings)
    (P : Bool × Bool × Bool) (hP : ¬ Aligned P) :
    Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P :=
  Props511.good_of_allGood A hab hS hsc W hX h12 (Props511.facts_512 _ hcf).1 P hP

/-- Proposition 5.12, tex:835-841. -/
theorem prop_5_12_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcf : A.configOf a b W.E x₁ x₂ ∈ (⟨2, 1, 0, 2, 0, 1⟩ : Config).renamings ∪
      (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧
      Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q ≤ (Fintype.card Q - 1) ^ 2 := by
  refine ⟨?_, Props511.arith_512 hn⟩
  have hgood := prop_5_12_good_proved A a b hab hS hsc hn W x₁ x₂ hX h12 hcf
  obtain ⟨hp, hst, hpos⟩ := Props511.half_facts A hab hS hsc W
  have hcls := Props511.t_512 A hab hS hsc W hX h12 hcf
  obtain ⟨c, q, hcq⟩ := thm_3_1_merging_proved A hA (by omega)
  have hne0 : (A.pre {q} [c]).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨K, w, J, hK0, hP⟩ := sec54_process_exists_proved A hA _ hp _ hst hpos _ hne0
  have hK0ne : (K 0).Nonempty := hK0 ▸ hne0
  obtain ⟨hmono, -, hnej, -, -, hmerge⟩ := sec54_process_props_proved A _ hpos K w J hP hK0ne
  refine (hmerge q c hK0).trans (Nat.cast_le.mpr ?_)
  have hmono' : ∀ i j, i < j → j < J →
      wt (A.alphaStat W.E (fun _ => 1 / 2)) (K i) < wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j) :=
    fun i j hij hj => hmono i j hij hj.le
  have hvis := fun j (hj : j < J) => Props511.visit_of A hsc W hX h12 hgood (K j) (hnej j hj.le)
    (hP.1 j hj).1 (w j) (hP.1 j hj).2.2.1
  -- the value of the start: `α(K₀) = |K₀| + g₁ e₁ + g₂ e₂` with `|K₀| ≥ 2`
  have hform0 := sec54_alpha_formula_proved A W x₁ x₂ hX h12 (K 0)
  have hc0 : (2 : ℝ) ≤ (K 0).card := by
    rw [hK0]
    exact_mod_cast hcq
  have he₁ := Props511.ein_cases x₁ (K 0)
  have he₂ := Props511.ein_cases x₂ (K 0)
  rcases hcls with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hv := Props511.lower_all hmono' (m := 1) (by
      rw [hform0]
      have := Props511.wt_lower (g₁ := A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1)
        (g₂ := A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) (m := -1) (by norm_num) (by rw [e1]; norm_num)
        (by rw [e2]; norm_num) (by rw [e1, e2]; norm_num) ((K 0).card : ℝ) _ _ he₁ he₂
      linarith)
    have hsum : ∑ j ∈ Finset.range J, (w j).length ≤
        (Fintype.card Q - 2) * (Fintype.card Q - 3) + 2 + (Fintype.card Q - 2) * 2 :=
      Props511.count_A (Fintype.card Q) J hn (fun j => (w j).length) (fun j => (K j).card)
        (fun j => decide (x₁ ∈ K j)) (fun j => decide (x₂ ∈ K j))
        (fun j => wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j)) _ _ (by rw [e1, e2]; norm_num)
        (by rw [e1]; norm_num) (by rw [e2]; norm_num) hmono' hvis hv
    have := Props511.arith_A hn
    omega
  · have hv := Props511.lower_all hmono' (m := 1) (by
      rw [hform0]
      have := Props511.wt_lower (g₁ := A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1)
        (g₂ := A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) (m := -1) (by norm_num) (by rw [e1]; norm_num)
        (by rw [e2]; norm_num) (by rw [e1, e2]; norm_num) ((K 0).card : ℝ) _ _ he₁ he₂
      linarith)
    have hsum : ∑ j ∈ Finset.range J, (w j).length ≤
        (Fintype.card Q - 2) * (Fintype.card Q - 3) + 2 + (Fintype.card Q - 2) * 2 :=
      Props511.count_A (Fintype.card Q) J hn (fun j => (w j).length) (fun j => (K j).card)
        (fun j => decide (x₁ ∈ K j)) (fun j => decide (x₂ ∈ K j))
        (fun j => wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j)) _ _ (by rw [e1, e2]; norm_num)
        (by rw [e1]; norm_num) (by rw [e2]; norm_num) hmono' hvis hv
    have := Props511.arith_A hn
    omega
  · have hv := Props511.lower_all hmono' (m := 5 / 3) (by
      rw [hform0]
      have := Props511.wt_lower (g₁ := A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1)
        (g₂ := A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) (m := -1 / 3) (by norm_num) (by rw [e1]; norm_num)
        (by rw [e2]; norm_num) (by rw [e1, e2]; norm_num) ((K 0).card : ℝ) _ _ he₁ he₂
      linarith)
    have hsum : ∑ j ∈ Finset.range J, (w j).length ≤
        (Fintype.card Q - 2 - 1) ^ 2 + (Fintype.card Q - 2) + (Fintype.card Q - 2) * 2 :=
      Props511.count_B (Fintype.card Q) J hn (fun j => (w j).length) (fun j => (K j).card)
        (fun j => decide (x₁ ∈ K j)) (fun j => decide (x₂ ∈ K j))
        (fun j => wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j)) _ _ (by rw [e1, e2]; norm_num)
        (by rw [e1]; norm_num) (by rw [e2]; norm_num) hmono' hvis hv
    have := Props511.arith_B hn
    omega
  · have hv := Props511.lower_all hmono' (m := 5 / 3) (by
      rw [hform0]
      have := Props511.wt_lower (g₁ := A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1)
        (g₂ := A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) (m := -1 / 3) (by norm_num) (by rw [e1]; norm_num)
        (by rw [e2]; norm_num) (by rw [e1, e2]; norm_num) ((K 0).card : ℝ) _ _ he₁ he₂
      linarith)
    have hsum : ∑ j ∈ Finset.range J, (w j).length ≤
        (Fintype.card Q - 2 - 1) ^ 2 + (Fintype.card Q - 2) + (Fintype.card Q - 2) * 2 :=
      Props511.count_B (Fintype.card Q) J hn (fun j => (w j).length) (fun j => (K j).card)
        (fun j => decide (x₁ ∈ K j)) (fun j => decide (x₂ ∈ K j))
        (fun j => wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j)) _ _ (by rw [e1, e2]; norm_num)
        (by rw [e1]; norm_num) (by rw [e2]; norm_num) hmono' hvis hv
    have := Props511.arith_B hn
    omega

/-- Proposition 5.12, tex:851-855. The sharper bound for the second configuration and its renamings. -/
theorem prop_5_12_sharp_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcf : A.configOf a b W.E x₁ x₂ ∈ (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 4 - 3 * Fintype.card Q : ℕ) : ℕ∞) := by
  have hboth := Finset.mem_union_right (⟨2, 1, 0, 2, 0, 1⟩ : Config).renamings hcf
  have hgood := prop_5_12_good_proved A a b hab hS hsc hn W x₁ x₂ hX h12 hboth
  obtain ⟨hp, hst, hpos⟩ := Props511.half_facts A hab hS hsc W
  have ht := (lem_5_7_b_proved A a b hab hS W x₁ x₂ hX h12).2.2.2.2 hsc
  have hpairs : ∀ cf ∈ (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings,
      (cf.t 0 = 2/3 ∧ cf.t 1 = 4/3) ∨ (cf.t 0 = 4/3 ∧ cf.t 1 = 2/3) := by decide +kernel
  have hcls :
      (A.alphaStat W.E (fun _ => 1 / 2) x₁ = 2/3 ∧ A.alphaStat W.E (fun _ => 1 / 2) x₂ = 4/3) ∨
      (A.alphaStat W.E (fun _ => 1 / 2) x₁ = 4/3 ∧ A.alphaStat W.E (fun _ => 1 / 2) x₂ = 2/3) := by
    have ht0 : A.alphaStat W.E (fun _ => 1 / 2) x₁ = (((A.configOf a b W.E x₁ x₂).t 0 : ℚ) : ℝ) := ht 0
    have ht1 : A.alphaStat W.E (fun _ => 1 / 2) x₂ = (((A.configOf a b W.E x₁ x₂).t 1 : ℚ) : ℝ) := ht 1
    rw [ht0, ht1]
    rcases hpairs _ hcf with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> norm_num
  obtain ⟨c, q, hcq⟩ := thm_3_1_merging_proved A hA (by omega)
  have hne0 : (A.pre {q} [c]).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨K, w, J, hK0, hP⟩ := sec54_process_exists_proved A hA _ hp _ hst hpos _ hne0
  have hK0ne : (K 0).Nonempty := hK0 ▸ hne0
  obtain ⟨hmono, -, hnej, -, -, hmerge⟩ := sec54_process_props_proved A _ hpos K w J hP hK0ne
  refine (hmerge q c hK0).trans (Nat.cast_le.mpr ?_)
  have hmono' : ∀ i j, i < j → j < J →
      wt (A.alphaStat W.E (fun _ => 1 / 2)) (K i) < wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j) :=
    fun i j hij hj => hmono i j hij hj.le
  have hvis := fun j (hj : j < J) => Props511.visit_of A hsc W hX h12 hgood (K j) (hnej j hj.le)
    (hP.1 j hj).1 (w j) (hP.1 j hj).2.2.1
  -- the value of the start: `α(K₀) = |K₀| + g₁ e₁ + g₂ e₂` with `|K₀| ≥ 2`
  have hform0 := sec54_alpha_formula_proved A W x₁ x₂ hX h12 (K 0)
  have hc0 : (2 : ℝ) ≤ (K 0).card := by
    rw [hK0]
    exact_mod_cast hcq
  have he₁ := Props511.ein_cases x₁ (K 0)
  have he₂ := Props511.ein_cases x₂ (K 0)
  let g₁ := A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1
  let g₂ := A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1
  have hg : g₁ + g₂ = 0 ∧ -(1/3) ≤ g₁ ∧ -(1/3) ≤ g₂ ∧ g₁ ≤ 1/3 ∧ g₂ ≤ 1/3 := by
    rcases hcls with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> norm_num [g₁, g₂, h1, h2]
  obtain ⟨hsumg, hlo1, hlo2, hhi1, hhi2⟩ := hg
  have hv := Props511.lower_all hmono' (m := 5 / 3) (by
      rw [hform0]
      have := Props511.wt_lower (g₁ := A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1)
        (g₂ := A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) (m := -(1 / 3)) (by norm_num) hlo1
        hlo2 (show -(1/3) ≤ g₁ + g₂ by rw [hsumg]; norm_num) ((K 0).card : ℝ) _ _ he₁ he₂
      linarith)
  have hsum : ∑ j ∈ Finset.range J, (w j).length ≤
        (Fintype.card Q - 2 - 1) ^ 2 + (Fintype.card Q - 2) + (Fintype.card Q - 2) * 2 :=
      Props511.count_B (Fintype.card Q) J hn (fun j => (w j).length) (fun j => (K j).card)
        (fun j => decide (x₁ ∈ K j)) (fun j => decide (x₂ ∈ K j))
        (fun j => wt (A.alphaStat W.E (fun _ => 1 / 2)) (K j)) _ _ hsumg hhi1 hhi2 hmono' hvis hv
  have := Props511.arith_B_exact hn
  omega

end Binary

end CernyQE
