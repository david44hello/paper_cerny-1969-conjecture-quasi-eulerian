/-
The noninteger levels in the second case of Proposition 5.12.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Printed
import CernyQE.Proofs.BinaryBase

namespace CernyQE

private theorem thirdValue_injective : Function.Injective thirdValue := by
  rintro ⟨k,b⟩ ⟨l,c⟩ h
  cases b <;> cases c <;> simp only [thirdValue, Bool.false_eq_true, ↓reduceIte] at h
  · have hkl : (k : ℝ) = l := by linarith
    congr 1
    exact_mod_cast hkl
  · have he : 3 * k = 3 * l + 2 := by exact_mod_cast (show (3:ℝ)*k = 3*l+2 by linarith)
    omega
  · have he : 3 * k + 2 = 3 * l := by exact_mod_cast (show (3:ℝ)*k+2 = 3*l by linarith)
    omega
  · have hkl : (k : ℝ) = l := by linarith
    congr 1
    exact_mod_cast hkl

private theorem thirdValue_nonint (k : ℕ) (b : Bool) : ¬ ∃ z : ℤ, thirdValue (k,b) = z := by
  rintro ⟨z,h⟩
  cases b <;> simp only [thirdValue, Bool.false_eq_true, ↓reduceIte] at h
  · have he : (3:ℤ)*k-1 = 3*z := by exact_mod_cast (show (3:ℝ)*k-1 = 3*z by linarith)
    omega
  · have he : (3:ℤ)*k+1 = 3*z := by exact_mod_cast (show (3:ℝ)*k+1 = 3*z by linarith)
    omega

private theorem subset_with_size {Q : Type*} [Fintype Q] [DecidableEq Q] {x y : Q} (hxy : x ≠ y)
    (k : ℕ) (h1 : 1 ≤ k) (hk : k ≤ Fintype.card Q - 1) :
    ∃ K : Finset Q, x ∈ K ∧ y ∉ K ∧ K.card = k := by
  obtain ⟨K, hx, hy, hc⟩ := Finset.exists_subsuperset_card_eq
    (s := {x}) (t := Finset.univ.erase y) (by simp [hxy]) (by simpa using h1)
    (by simpa using hk)
  exact ⟨K, hx (by simp), fun h => (Finset.notMem_erase y Finset.univ) (hy h), hc⟩

universe u v
variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- Proposition 5.12, tex:851-855. Name the exceptional states by weights 2/3 and 4/3. The noninteger levels are exactly k ± 1/3 for 2 ≤ k ≤ n−1. -/
theorem prop_5_12_levels_proved (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁,x₂}) (h12 : x₁ ≠ x₂)
    (h1 : A.alphaStat W.E (fun _ => 1/2) x₁ = 2/3) (h2 : A.alphaStat W.E (fun _ => 1/2) x₂ = 4/3) :
    let n := Fintype.card Q
    let α := A.alphaStat W.E (fun _ => 1/2)
    (∀ K : Finset Q, ¬ (x₁ ∈ K ↔ x₂ ∈ K) → K.card ≤ n - 1) ∧
      (∀ z : ℝ, z ∈ thirdLevels n ↔ 5/3 ≤ z ∧ z < n ∧ (¬ ∃ i : ℤ, z = i) ∧ ∃ K : Finset Q, wt α K = z) ∧
      (thirdLevels n).card = 2 * (n - 2) := by
  classical
  dsimp only
  have hsize (K : Finset Q) (hm : ¬ (x₁ ∈ K ↔ x₂ ∈ K)) : K.card ≤ Fintype.card Q - 1 := by
    have hp : K ≠ Finset.univ := by rintro rfl; simp at hm
    have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hp)
    simp only [Finset.card_univ] at this
    omega
  have form (K : Finset Q) := sec54_alpha_formula_proved A W x₁ x₂ hX h12 K
  simp only [h1,h2] at form
  refine ⟨hsize, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨⟨k,b⟩, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
      have hrlo : (2:ℝ) ≤ k := by exact_mod_cast lo
      have hrhi : (k:ℝ) + 1 ≤ Fintype.card Q := by exact_mod_cast (show k + 1 ≤ Fintype.card Q by omega)
      refine ⟨?_, ?_, thirdValue_nonint k b, ?_⟩
      · cases b <;> simp [thirdValue] <;> linarith
      · cases b <;> simp [thirdValue] <;> linarith
      · cases b with
        | false =>
          obtain ⟨K,hm,ha,hk⟩ := subset_with_size h12 k (by omega) hi
          refine ⟨K, ?_⟩
          rw [form K]
          simp [hk, ein, hm, ha, thirdValue] <;> ring
        | true =>
          obtain ⟨K,hm,ha,hk⟩ := subset_with_size h12.symm k (by omega) hi
          refine ⟨K, ?_⟩
          rw [form K]
          simp [hk, ein, hm, ha, thirdValue] <;> ring
    · rintro ⟨hzlo, _, hnon, K, rfl⟩
      have hform := form K
      by_cases hm : x₁ ∈ K <;> by_cases ha : x₂ ∈ K
      · exfalso
        apply hnon
        exact ⟨K.card, by rw [hform]; simp [ein, hm, ha] <;> ring⟩
      · have hk := hsize K (fun h => ha (h.mp hm))
        simp [ein, hm, ha] at hform
        have hr : (1:ℝ) < K.card := by linarith
        have hl : 1 < K.card := by exact_mod_cast hr
        apply Finset.mem_image.mpr
        exact ⟨(K.card,false), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hl, hk⟩, Finset.mem_univ _⟩,
          by simp [thirdValue,hform] <;> ring⟩
      · have hk := hsize K (fun h => hm (h.mpr ha))
        simp [ein, hm, ha] at hform
        have hr : (1:ℝ) < K.card := by linarith
        have hl : 1 < K.card := by exact_mod_cast hr
        apply Finset.mem_image.mpr
        exact ⟨(K.card,true), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hl, hk⟩, Finset.mem_univ _⟩,
          by simp [thirdValue,hform] <;> ring⟩
      · exfalso
        apply hnon
        exact ⟨K.card, by rw [hform]; simp [ein, hm, ha]⟩
  · unfold thirdLevels
    rw [Finset.card_image_of_injective _ thirdValue_injective, Finset.card_product, Nat.card_Icc]
    simp only [Finset.card_univ, Fintype.card_bool]
    omega

/-- Proposition 5.12, tex:857-863. The class {1/3,2/3} has at most 2(n−2) noninteger values in [1,n−1). -/
theorem prop_5_12_first_levels_proved (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁,x₂}) (h12 : x₁ ≠ x₂) (h1 : A.alphaStat W.E (fun _ => 1/2) x₁ = 1/3)
    (h2 : A.alphaStat W.E (fun _ => 1/2) x₂ = 2/3) :
    (nonintegerWeights (A.alphaStat W.E (fun _ => 1/2)) 1 ((Fintype.card Q : ℝ) - 1)).card ≤
      2 * (Fintype.card Q - 2) := by
  classical
  let n := Fintype.card Q
  let slots := (Finset.Icc 2 (n-1)) ×ˢ (Finset.univ : Finset Bool)
  let value (p : ℕ × Bool) : ℝ := if p.2 then (p.1 : ℝ) - 1/3 else (p.1 : ℝ) - 2/3
  have hs : nonintegerWeights (A.alphaStat W.E (fun _ => 1/2)) 1 ((n : ℝ) - 1) ⊆ slots.image value := by
    intro z hz
    obtain ⟨hm,lo,_,hz⟩ := Finset.mem_filter.mp hz
    obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp hm
    have form := sec54_alpha_formula_proved A W x₁ x₂ hX h12 K
    rw [h1,h2] at form
    by_cases hU : x₁ ∈ K <;> by_cases hV : x₂ ∈ K
    · exfalso
      apply hz
      refine ⟨(K.card : ℤ)-1, ?_⟩
      rw [form]
      simp [ein,hU,hV]
      <;> ring
    · have hp : K ≠ Finset.univ := by rintro rfl; simp at hV
      have hk := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hp)
      simp only [Finset.card_univ] at hk
      simp [ein,hU,hV] at form
      have hr : (1:ℝ) < K.card := by linarith
      have hl : 1 < K.card := by exact_mod_cast hr
      refine Finset.mem_image.mpr ⟨(K.card,false), Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hl, by dsimp [n]; omega⟩, Finset.mem_univ _⟩, ?_⟩
      simp [value,form] <;> ring
    · have hp : K ≠ Finset.univ := by rintro rfl; simp at hU
      have hk := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hp)
      simp only [Finset.card_univ] at hk
      simp [ein,hU,hV] at form
      have hr : (1:ℝ) < K.card := by linarith
      have hl : 1 < K.card := by exact_mod_cast hr
      refine Finset.mem_image.mpr ⟨(K.card,true), Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hl, by dsimp [n]; omega⟩, Finset.mem_univ _⟩, ?_⟩
      simp [value,form] <;> ring
    · exact (hz ⟨K.card, by rw [form]; simp [ein,hU,hV]⟩).elim
  apply (Finset.card_le_card hs).trans (Finset.card_image_le.trans ?_)
  simp only [slots, Finset.card_product, Nat.card_Icc, Finset.card_univ, Fintype.card_bool, n]
  omega

end CernyQE
