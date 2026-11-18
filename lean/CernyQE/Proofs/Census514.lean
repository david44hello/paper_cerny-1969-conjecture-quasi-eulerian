/-
CernyQE/Proofs/Census514.lean — Proposition 5.14 for 4 ≤ n ≤ 6: the renaming lemma, the joining theorem, the census.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Binary
import CernyQE.Proofs.ImageSearch
import CernyQE.Proofs.Census514.Lower
import CernyQE.Proofs.Census514.N4
import CernyQE.Proofs.Census514.N5_00
import CernyQE.Proofs.Census514.N6_00
import CernyQE.Proofs.Census514.N6_01
import CernyQE.Proofs.Census514.N6_02
import CernyQE.Proofs.Census514.N6_03
import CernyQE.Proofs.Census514.N6_04
import CernyQE.Proofs.Census514.N6_05
import CernyQE.Proofs.Census514.N6_06
import CernyQE.Proofs.Census514.N6_07
import CernyQE.Proofs.Census514.N6_08
import Mathlib

/-!
Let `A` be binary (letters `a ≠ b`) with a witness `W` of degree two, `X = {x₁, x₂}`.
* Witness facts: the edges from `X` end in `X ∪ {s}`; every `r ∈ E \ {s}` is entered by exactly two edges, all from
  `E` (in-weight one, Lemma 5.7); the edges from `E` into `s` number `2 - ν₁ - ν₂`.
* The vector `α` of Lemma 5.5 with the weights `(1/2, 1/2)` equals the configuration's `t` on `x₁, x₂` (the inverse of
  the `2 × 2` matrix `I - Z` by Cramer's rule; both sides are `0` when `det (I - Z) = 0`).
* Renaming: with `s ↦ 0`, `x₁ ↦ n-2`, `x₂ ↦ n-1` and `a ↦ 0`, `b ↦ 1`, the automaton becomes the table automaton of an
  edge assignment of the census family; a reset word of the table automaton maps back to a reset word of `A` of the
  same length (strong connectivity is not used: every synchronizing member of the family passes the check).
* Joining: the chunk theorems of `Census514/N*.lean` cover each of the nine configurations of `canonCfgs`; renaming
  `x₁ ↔ x₂` and `a ↔ b` reaches one of the nine from every configuration of the integer classes.
-/

namespace CernyQE

open Classical Automaton Matrix

universe u v

namespace Census514

open Finset ImageSearch

private theorem minLen_le_of' {S : Type*} {P : List S → Prop} {w : List S} (h : P w) : minLen P ≤ w.length :=
  iInf₂_le w h

/-! ### Two letters -/

section Letters

variable {S : Type v} [Fintype S] (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b)
include hab hS

theorem sum_letters {M : Type*} [AddCommMonoid M] (f : S → M) : ∑ c, f c = f a + f b := by
  have hu : (Finset.univ : Finset S) = {a, b} := by
    ext c
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hS c
  rw [hu, Finset.sum_pair hab]

end Letters

/-! ### Facts about a witness of degree two -/

section Witness

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-- The number of `c`-edges from `E` into `r`. -/
def fE (E : Finset Q) (c : S) (r : Q) : ℕ := (E.filter (fun q => A.step q c = r)).card

omit [Fintype Q] [Fintype S] in
theorem nuOf_eq (a b : S) (E : Finset Q) (x : Q) : A.nuOf a b E x = fE A E a x + fE A E b x := rfl

theorem mem_E_iff (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (q : Q) :
    q ∈ W.E ↔ q ≠ x₁ ∧ q ≠ x₂ := by
  have h : q ∈ W.X ↔ q = x₁ ∨ q = x₂ := by
    rw [hX]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have h' : q ∈ W.X ↔ q ∉ W.E := by
    simp only [QEWitness.X, Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [h'] at h
  tauto

theorem step_X (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (x : Q) (hx : x ∉ W.E) (c : S) :
    A.step x c = x₁ ∨ A.step x c = x₂ ∨ A.step x c = W.s := by
  rcases W.edge_X x hx c with h | h
  · rw [mem_E_iff A W hX] at h
    by_cases h1 : A.step x c = x₁
    · exact Or.inl h1
    · exact Or.inr (Or.inl (by by_contra h2; exact h ⟨h1, h2⟩))
  · exact Or.inr (Or.inr h)

theorem pre_eq_filter (W : QEWitness A 2) (r : Q) (hr : r ∈ W.E) (hrs : r ≠ W.s) (c : S) :
    A.pre {r} [c] = W.E.filter (fun q => A.step q c = r) := by
  ext q
  simp only [Automaton.pre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  change A.step q c = r ↔ q ∈ W.E ∧ A.step q c = r
  constructor
  · intro h
    refine ⟨?_, h⟩
    by_contra hq
    rcases W.edge_X q hq c with h' | h'
    · exact h' (by rw [h]; exact hr)
    · exact hrs (by rw [← h, h'])
  · exact fun h => h.2

omit [Fintype Q] [Fintype S] in
theorem sum_fE_le (E : Finset Q) (c : S) (R : Finset Q) : ∑ r ∈ R, fE A E c r ≤ E.card := by
  unfold fE
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  exact Finset.card_filter_le _ _

omit [Fintype S] in
theorem sum_fE_univ (E : Finset Q) (c : S) : ∑ r, fE A E c r = E.card := by
  unfold fE
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp only [Finset.mem_univ, Finset.filter_true]

/-- The arithmetic of Lemma 5.7(a): a state of type `(0, k)` has `k = 2`. -/
theorem type_zero {ι : Type*} (R : Finset ι) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1)
    (α β : ι → ℕ) (h : ∀ r ∈ R, p * (α r : ℝ) + q * (β r : ℝ) = 1) (hβ : ∑ r ∈ R, β r ≤ R.card + 1)
    (r₀ : ι) (hr₀ : r₀ ∈ R) (hα : α r₀ = 0) : β r₀ = 2 := by
  have h0 := h r₀ hr₀
  rw [hα, Nat.cast_zero, mul_zero, zero_add] at h0
  by_contra hne
  have hb3 : 3 ≤ β r₀ := by
    rcases Nat.lt_or_ge (β r₀) 3 with h3 | h3
    · interval_cases hb : β r₀
      · simp at h0
      · have : q = 1 := by simpa using h0
        linarith
      · exact absurd rfl hne
    · exact h3
  have hb3' : (3 : ℝ) ≤ β r₀ := by exact_mod_cast hb3
  have hall : ∀ r ∈ R, 1 ≤ β r := by
    intro r hr
    by_contra hlt
    have hb0 : β r = 0 := by omega
    have hr' := h r hr
    rw [hb0, Nat.cast_zero, mul_zero, add_zero] at hr'
    rcases Nat.lt_or_ge (α r) 2 with h2 | h2
    · interval_cases ha : α r
      · simp at hr'
      · have : p = 1 := by simpa using hr'
        linarith
    · have h2' : (2 : ℝ) ≤ α r := by exact_mod_cast h2
      nlinarith
  have hsum : R.card + 2 ≤ ∑ r ∈ R, β r := by
    rw [← Finset.add_sum_erase R β hr₀]
    have h1 : ∑ r ∈ R.erase r₀, 1 ≤ ∑ r ∈ R.erase r₀, β r :=
      Finset.sum_le_sum (fun r hr => hall r (Finset.mem_of_mem_erase hr))
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hr₀] at h1
    have hc : 1 ≤ R.card := Finset.card_pos.2 ⟨r₀, hr₀⟩
    omega
  omega

/-- Lemma 5.7: every state of `E \ {s}` is entered by exactly two edges, all from `E`. -/
theorem indeg (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (r : Q) (hr : r ∈ W.E)
    (hrs : r ≠ W.s) : fE A W.E a r + fE A W.E b r = 2 := by
  set R := W.E.erase W.s with hR
  have hRcard : R.card + 1 = W.E.card := by
    rw [hR, Finset.card_erase_of_mem W.s_mem]
    have := Finset.card_pos.2 ⟨W.s, W.s_mem⟩
    omega
  have hpa := W.weights.1 a
  have hpb := W.weights.1 b
  have hsum : W.p a + W.p b = 1 := by
    have := W.weights.2
    rwa [sum_letters a b hab hS] at this
  have hin : ∀ r ∈ R, W.p a * (fE A W.E a r : ℝ) + W.p b * (fE A W.E b r : ℝ) = 1 := by
    intro r' hr'
    have hr'E : r' ∈ W.E := Finset.mem_of_mem_erase hr'
    have hr's : r' ≠ W.s := Finset.ne_of_mem_erase hr'
    have := W.inW_one r' hr'E hr's
    unfold Automaton.inW at this
    rw [sum_letters a b hab hS, pre_eq_filter A W r' hr'E hr's a, pre_eq_filter A W r' hr'E hr's b] at this
    exact this
  have hrR : r ∈ R := Finset.mem_erase.2 ⟨hrs, hr⟩
  have hα : ∑ r ∈ R, fE A W.E a r ≤ R.card + 1 := hRcard ▸ sum_fE_le A W.E a R
  have hβ : ∑ r ∈ R, fE A W.E b r ≤ R.card + 1 := hRcard ▸ sum_fE_le A W.E b R
  by_cases ha : fE A W.E a r = 0
  · rw [ha, type_zero R (W.p a) (W.p b) hpa hpb hsum (fE A W.E a) (fE A W.E b) hin hβ r hrR ha]
  by_cases hb : fE A W.E b r = 0
  · have hin' : ∀ r ∈ R, W.p b * (fE A W.E b r : ℝ) + W.p a * (fE A W.E a r : ℝ) = 1 :=
      fun r' hr' => by linarith [hin r' hr']
    rw [hb, type_zero R (W.p b) (W.p a) hpb hpa (by linarith) (fE A W.E b) (fE A W.E a) hin' hα r hrR hb]
  have h1 := hin r hrR
  have ha1 : (1 : ℝ) ≤ fE A W.E a r := by exact_mod_cast Nat.one_le_iff_ne_zero.2 ha
  have hb1 : (1 : ℝ) ≤ fE A W.E b r := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
  have ha2 : fE A W.E a r ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ fE A W.E a r := by exact_mod_cast (show 2 ≤ fE A W.E a r by omega)
    nlinarith
  have hb2 : fE A W.E b r ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ fE A W.E b r := by exact_mod_cast (show 2 ≤ fE A W.E b r by omega)
    nlinarith
  omega

/-- The edges from `E` into `s`: `2 - ν₁ - ν₂` of them. -/
theorem count_s (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) {x₁ x₂ : Q}
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    fE A W.E a W.s + fE A W.E b W.s + A.nuOf a b W.E x₁ + A.nuOf a b W.E x₂ = 2 := by
  set f : Q → ℕ := fun r => fE A W.E a r + fE A W.E b r with hf
  have htot : ∑ r, f r = 2 * W.E.card := by
    rw [hf, Finset.sum_add_distrib, sum_fE_univ, sum_fE_univ]
    ring
  have hcompl : W.Eᶜ = {x₁, x₂} := by
    rw [← hX, QEWitness.X, Finset.compl_eq_univ_sdiff]
  rw [← Finset.sum_add_sum_compl W.E f, hcompl, Finset.sum_pair h12, ← Finset.add_sum_erase W.E f W.s_mem] at htot
  have hR : ∑ r ∈ W.E.erase W.s, f r = 2 * (W.E.card - 1) := by
    rw [Finset.sum_congr rfl (fun r hr => indeg A a b hab hS W r (Finset.mem_of_mem_erase hr)
      (Finset.ne_of_mem_erase hr)), Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem W.s_mem]
    ring
  rw [hR] at htot
  have hpos := Finset.card_pos.2 ⟨W.s, W.s_mem⟩
  rw [nuOf_eq, nuOf_eq]
  simp only [hf] at htot
  omega

end Witness

/-! ### The vector `α` with the weights `(1/2, 1/2)` is the configuration's `t` -/

section Alpha

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

omit [Fintype Q] [Fintype S] in
theorem stateCode_eq {x₁ x₂ : Q} (h12 : x₁ ≠ x₂) (y : Q) (j : Fin 2) :
    stateCode x₁ x₂ y = Fin.castSucc j ↔ y = ![x₁, x₂] j := by
  unfold stateCode
  fin_cases j
  · by_cases h1 : y = x₁
    · simp [h1]
    · by_cases h2 : y = x₂ <;> simp [h1, h2]
  · by_cases h1 : y = x₁
    · simp [h1, h12]
    · by_cases h2 : y = x₂ <;> simp [h1, h2, Ne.symm h12]

omit [Fintype Q] [Fintype S] in
theorem tgt_cfg (a b : S) (E : Finset Q) (x₁ x₂ : Q) (i : Fin 2) :
    (A.configOf a b E x₁ x₂).tgt i 0 = stateCode x₁ x₂ (A.step (![x₁, x₂] i) a) ∧
      (A.configOf a b E x₁ x₂).tgt i 1 = stateCode x₁ x₂ (A.step (![x₁, x₂] i) b) := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

omit [Fintype Q] in
theorem zPair_cfg (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (E : Finset Q) {x₁ x₂ : Q} (h12 : x₁ ≠ x₂)
    (i j : Fin 2) :
    (∑ _c ∈ Finset.univ.filter (fun c => A.step (![x₁, x₂] i) c = ![x₁, x₂] j), (1 / 2 : ℝ)) =
      ((A.configOf a b E x₁ x₂).Z i j : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_filter, sum_letters a b hab hS]
  unfold Config.Z
  rw [Finset.card_filter, Fin.sum_univ_two, (tgt_cfg A a b E x₁ x₂ i).1, (tgt_cfg A a b E x₁ x₂ i).2]
  simp only [stateCode_eq h12]
  push_cast
  split_ifs <;> norm_num

omit [Fintype Q] in
theorem yIn_cfg (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (E : Finset Q) (x₁ x₂ : Q) (i : Fin 2) :
    A.yIn E (fun _ => 1 / 2) (![x₁, x₂] i) = ((A.configOf a b E x₁ x₂).y i : ℝ) := by
  unfold Automaton.yIn
  rw [sum_letters a b hab hS]
  unfold Config.y Config.nu
  have hnu : ![(A.configOf a b E x₁ x₂).nu1, (A.configOf a b E x₁ x₂).nu2] i = A.nuOf a b E (![x₁, x₂] i) := by
    fin_cases i <;> rfl
  rw [hnu, nuOf_eq]
  unfold fE
  push_cast
  ring

/-- Lemma 5.5 with the weights `(1/2, 1/2)` for `X = {x₁, x₂}`: `α_{x_i} = t_i` of the configuration. -/
theorem alphaStat_cfg (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (E : Finset Q) {x₁ x₂ : Q}
    (hX : Finset.univ \ E = {x₁, x₂}) (h12 : x₁ ≠ x₂) (i : Fin 2) :
    A.alphaStat E (fun _ => 1 / 2) (![x₁, x₂] i) = ((A.configOf a b E x₁ x₂).t i : ℝ) := by
  set cf := A.configOf a b E x₁ x₂ with hcf
  have hmem : ∀ k : Fin 2, ![x₁, x₂] k ∈ Finset.univ \ E := by
    intro k
    rw [hX]
    fin_cases k <;> simp
  let φ : Fin 2 → ↥(Finset.univ \ E) := fun k => ⟨![x₁, x₂] k, hmem k⟩
  have hφinj : Function.Injective φ := by
    intro k l hkl
    have h := congrArg Subtype.val hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact absurd h h12
    · exact absurd h.symm h12
    · rfl
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' := hy
    rw [hX] at hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  let e : Fin 2 ≃ ↥(Finset.univ \ E) := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have he : ∀ k, ((e k : ↥(Finset.univ \ E)) : Q) = ![x₁, x₂] k := fun k => rfl
  have h1 : A.alphaStat E (fun _ => 1 / 2) (![x₁, x₂] i) = A.tvec E (fun _ => 1 / 2) (e i) := by
    unfold Automaton.alphaStat
    rw [dite_eq_left (hmem i)]
    rfl
  rw [h1]
  unfold Automaton.tvec
  set N := 1 - A.Zmat E (fun _ => 1 / 2) with hN
  have hsub : (N.submatrix e e)⁻¹ = N⁻¹.submatrix e e := Matrix.inv_submatrix_equiv N e e
  have hv : Matrix.vecMul (A.yvec E (fun _ => 1 / 2)) N⁻¹ (e i) =
      Matrix.vecMul (A.yvec E (fun _ => 1 / 2) ∘ e) (N.submatrix e e)⁻¹ i := by
    rw [hsub]
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Function.comp]
    exact (Equiv.sum_comp e (fun x => A.yvec E (fun _ => 1 / 2) x * N⁻¹ x (e i))).symm
  rw [hv]
  have hNe : N.submatrix e e = !![1 - (cf.Z 0 0 : ℝ), -(cf.Z 0 1 : ℝ); -(cf.Z 1 0 : ℝ), 1 - (cf.Z 1 1 : ℝ)] := by
    ext k l
    rw [Matrix.submatrix_apply, hN, Matrix.sub_apply, Matrix.one_apply]
    simp only [e.injective.eq_iff]
    have hz : A.Zmat E (fun _ => 1 / 2) (e k) (e l) = (cf.Z k l : ℝ) := by
      unfold Automaton.Zmat
      rw [he, he]
      exact zPair_cfg A a b hab hS E h12 k l
    rw [hz]
    fin_cases k <;> fin_cases l <;> simp
  have hy : A.yvec E (fun _ => 1 / 2) ∘ e = fun k => (cf.y k : ℝ) := by
    funext k
    simp only [Function.comp, Automaton.yvec]
    rw [he]
    exact yIn_cfg A a b hab hS E x₁ x₂ k
  rw [hNe, hy, Matrix.inv_def, Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of, Ring.inverse_eq_inv']
  fin_cases i
  · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul, Config.t, Config.det]
    push_cast
    ring
  · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul, Config.t, Config.det]
    push_cast
    ring

theorem alphaStat_cfg₁ (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (E : Finset Q) {x₁ x₂ : Q}
    (hX : Finset.univ \ E = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    A.alphaStat E (fun _ => 1 / 2) x₁ = ((A.configOf a b E x₁ x₂).t 0 : ℝ) :=
  alphaStat_cfg A a b hab hS E hX h12 0

theorem alphaStat_cfg₂ (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (E : Finset Q) {x₁ x₂ : Q}
    (hX : Finset.univ \ E = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    A.alphaStat E (fun _ => 1 / 2) x₂ = ((A.configOf a b E x₁ x₂).t 1 : ℝ) :=
  alphaStat_cfg A a b hab hS E hX h12 1

end Alpha

/-! ### Renaming the letters and the exceptional states of a configuration -/

section Swap

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] (A : Automaton Q S)

omit [Fintype Q] in
theorem configOf_swapL (a b : S) (E : Finset Q) (x₁ x₂ : Q) :
    A.configOf b a E x₁ x₂ = (A.configOf a b E x₁ x₂).swapL := by
  simp only [Automaton.configOf, Config.swapL, Automaton.nuOf, Config.mk.injEq, true_and]
  exact ⟨add_comm _ _, add_comm _ _⟩

omit [Fintype Q] in
theorem stateCode_swap {x₁ x₂ : Q} (h12 : x₁ ≠ x₂) (y : Q) :
    stateCode x₂ x₁ y = Config.swapCode (stateCode x₁ x₂ y) := by
  unfold stateCode Config.swapCode
  by_cases h1 : y = x₁
  · subst h1
    simp [h12]
  · by_cases h2 : y = x₂
    · subst h2
      simp [h1]
    · simp [h1, h2]

omit [Fintype Q] in
theorem configOf_swapX (a b : S) (E : Finset Q) {x₁ x₂ : Q} (h12 : x₁ ≠ x₂) :
    A.configOf a b E x₂ x₁ = (A.configOf a b E x₁ x₂).swapX := by
  simp only [Automaton.configOf, Config.swapX, stateCode_swap h12]

end Swap

/-! ### Placing `s`, `x₁`, `x₂` at `0`, `n-2`, `n-1` -/

theorem exists_equiv {Q : Type u} [Fintype Q] [DecidableEq Q] {n : ℕ} (hn : Fintype.card Q = n) (hn3 : 3 ≤ n)
    (s x₁ x₂ : Q) (h1 : s ≠ x₁) (h2 : s ≠ x₂) (h12 : x₁ ≠ x₂) :
    ∃ e : Q ≃ Fin n, (e s).val = 0 ∧ (e x₁).val = n - 2 ∧ (e x₂).val = n - 1 := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨n - 2, by omega⟩
  let i2 : Fin n := ⟨n - 1, by omega⟩
  have h01 : i0 ≠ i1 := by simp only [i0, i1, ne_eq, Fin.mk.injEq]; omega
  have h02 : i0 ≠ i2 := by simp only [i0, i2, ne_eq, Fin.mk.injEq]; omega
  have h12' : i1 ≠ i2 := by simp only [i1, i2, ne_eq, Fin.mk.injEq]; omega
  let e0 := Fintype.equivFinOfCardEq hn
  let e1 := e0.trans (Equiv.swap (e0 s) i0)
  have e1s : e1 s = i0 := by simp only [e1, Equiv.trans_apply, Equiv.swap_apply_left]
  let e2 := e1.trans (Equiv.swap (e1 x₁) i1)
  have e2s : e2 s = i0 := by
    simp only [e2, Equiv.trans_apply]
    rw [e1s]
    exact Equiv.swap_apply_of_ne_of_ne (by rw [← e1s]; exact e1.injective.ne h1) h01
  have e2x₁ : e2 x₁ = i1 := by simp only [e2, Equiv.trans_apply, Equiv.swap_apply_left]
  let e3 := e2.trans (Equiv.swap (e2 x₂) i2)
  have e3s : e3 s = i0 := by
    simp only [e3, Equiv.trans_apply]
    rw [e2s]
    exact Equiv.swap_apply_of_ne_of_ne (by rw [← e2s]; exact e2.injective.ne h2) h02
  have e3x₁ : e3 x₁ = i1 := by
    simp only [e3, Equiv.trans_apply]
    rw [e2x₁]
    exact Equiv.swap_apply_of_ne_of_ne (by rw [← e2x₁]; exact e2.injective.ne h12) h12'
  have e3x₂ : e3 x₂ = i2 := by simp only [e3, Equiv.trans_apply, Equiv.swap_apply_left]
  exact ⟨e3, by rw [e3s], by rw [e3x₁], by rw [e3x₂]⟩

/-! ### Lists -/

theorem count_map_range (f : ℕ → ℕ) (v : ℕ) :
    ∀ m : ℕ, ((List.range m).map f).count v = ((Finset.range m).filter (fun q => f q = v)).card
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.count_append, count_map_range f v m, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : f m = v
    · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [ite_eq_right h]
      simp [h]

theorem getD_map_range (f : ℕ → ℕ) {m q : ℕ} (hq : q < m) : ((List.range m).map f).getD q 0 = f q := by
  simp [List.getD_eq_getElem?_getD, hq]

/-! ### The renaming lemma -/

/-- The census family of the raw configuration `t` passes the check. -/
def FamOK (n M : ℕ) (t : List ℕ) : Prop :=
  ∀ σ : List ℕ, σ.length = 2 * (n - 2) → (∀ v ∈ σ, v < n) → (∀ v, σ.count v ≤ (cntOf n t).getD v 0) →
    memberOK n M (tblOf n t σ) = true

theorem famOK_of_chunks (n M : ℕ) (t : List ℕ) (hn : 3 ≤ n)
    (h : ∀ v₁, v₁ < n → ∀ v₂, v₂ < n → chunk n M t v₁ v₂ = true) : FamOK n M t :=
  fun σ hl hlt hc => leaf_of_chunks n M t hn h σ hl hlt hc

section Reduction

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]

/-- The renaming lemma: if the census family of the configuration passes the check, then `rt ≤ M`. -/
theorem reduce {n M : ℕ} (hn3 : 3 ≤ n) {t : List ℕ} (hfam : FamOK n M t) (A : Automaton Q S) (a b : S)
    (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (hcard : Fintype.card Q = n) (ht : t = rawOf (A.configOf a b W.E x₁ x₂))
    (hA : A.Synchronizing) : A.rt ≤ (M : ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have : NeZero (m + 2) := ⟨by omega⟩
  have hsE := W.s_mem
  rw [mem_E_iff A W hX] at hsE
  obtain ⟨e, he0, he1, he2⟩ := exists_equiv hcard hn3 W.s x₁ x₂ hsE.1 hsE.2 h12
  simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega] at he1 he2
  -- the letters, the states, and the edges of the renamed automaton
  let L : ℕ → S := fun c => if c = 0 then a else b
  let toQ : ℕ → Q := fun q => if h : q < m + 2 then e.symm ⟨q, h⟩ else W.s
  let g : ℕ → ℕ → ℕ := fun q c => (e (A.step (toQ q) (L c))).val
  have toQ_e : ∀ y, toQ (e y).val = y := by
    intro y
    simp only [toQ, dite_eq_left (e y).isLt, Fin.eta, Equiv.symm_apply_apply]
  have e_toQ : ∀ q, q < m + 2 → (e (toQ q)).val = q := by
    intro q hq
    simp only [toQ, dite_eq_left hq, Equiv.apply_symm_apply]
  have toQ0 : toQ 0 = W.s := by rw [← he0, toQ_e]
  have toQ1 : toQ m = x₁ := by rw [← he1, toQ_e]
  have toQ2 : toQ (m + 1) = x₂ := by rw [← he2, toQ_e]
  have memE : ∀ y, y ∈ W.E ↔ (e y).val < m := by
    intro y
    rw [mem_E_iff A W hX]
    have hlt := (e y).isLt
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : (e y).val ≠ m := fun h => h1 (by rw [← toQ_e y, h, toQ1])
      have h2' : (e y).val ≠ m + 1 := fun h => h2 (by rw [← toQ_e y, h, toQ2])
      omega
    · intro h
      refine ⟨fun h1 => ?_, fun h2 => ?_⟩
      · rw [h1, he1] at h
        omega
      · rw [h2, he2] at h
        omega
  have g_lt : ∀ q c, g q c < m + 2 := fun q c => (e (A.step (toQ q) (L c))).isLt
  -- the edge assignment and the table
  let σ : List ℕ := (List.range m).map (fun q => g q 0) ++ (List.range m).map (fun q => g q 1)
  have hcode : ∀ y, (y = x₁ ∨ y = x₂ ∨ y = W.s) → code (m + 2) (stateCode x₁ x₂ y).val = (e y).val := by
    rintro y (rfl | rfl | rfl)
    · simp [stateCode, code, he1]
    · simp [stateCode, code, he2, Ne.symm h12]
    · simp [stateCode, code, he0, hsE.1, hsE.2]
  have hx1 : x₁ ∉ W.E := fun h => ((mem_E_iff A W hX x₁).1 h).1 rfl
  have hx2 : x₂ ∉ W.E := fun h => ((mem_E_iff A W hX x₂).1 h).2 rfl
  have htbl : tblOf (m + 2) t σ = (List.range (m + 2)).map (fun q => g q 0) ++
      (List.range (m + 2)).map (fun q => g q 1) := by
    have hl : ((List.range m).map (fun q => g q 0)).length = m := by simp
    have hga1 : code (m + 2) (t.getD 0 0) = g m 0 := by
      rw [ht]
      simp only [rawOf, List.getD_cons_zero, Automaton.configOf, g, toQ1, L]
      exact hcode _ (step_X A W hX x₁ hx1 a)
    have hga2 : code (m + 2) (t.getD 2 0) = g (m + 1) 0 := by
      rw [ht]
      simp only [rawOf, List.getD_cons_succ, List.getD_cons_zero, Automaton.configOf, g, toQ2, L]
      exact hcode _ (step_X A W hX x₂ hx2 a)
    have hgb1 : code (m + 2) (t.getD 1 0) = g m 1 := by
      rw [ht]
      simp only [rawOf, List.getD_cons_succ, List.getD_cons_zero, Automaton.configOf, g, toQ1, L,
        ite_eq_right one_ne_zero]
      exact hcode _ (step_X A W hX x₁ hx1 b)
    have hgb2 : code (m + 2) (t.getD 3 0) = g (m + 1) 1 := by
      rw [ht]
      simp only [rawOf, List.getD_cons_succ, List.getD_cons_zero, Automaton.configOf, g, toQ2, L,
        ite_eq_right one_ne_zero]
      exact hcode _ (step_X A W hX x₂ hx2 b)
    unfold tblOf
    rw [Nat.add_sub_cancel, List.take_left' hl, List.drop_left' hl, hga1, hga2, hgb1, hgb2,
      List.range_succ, List.range_succ, List.map_append, List.map_append, List.map_append, List.map_append]
    simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
  -- the renamed automaton is the table automaton
  set B := tabAut (m + 2) (tblOf (m + 2) t σ) with hB
  have hstep : ∀ (q : Fin (m + 2)) (c : Fin 2), B.step q c = e (A.step (e.symm q) (L c.val)) := by
    intro q c
    apply Fin.ext
    rw [hB, tabAut_step_val]
    unfold stp
    rw [htbl]
    have hq := q.isLt
    have hc := c.isLt
    have hlen : ((List.range (m + 2)).map (fun q => g q 0)).length = m + 2 := by simp
    rcases c with ⟨_ | _ | c, hc'⟩
    · simp only [zero_mul, zero_add]
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hq), getD_map_range _ hq,
        Nat.mod_eq_of_lt (g_lt _ _)]
      simp only [g, toQ, dite_eq_left hq, Fin.eta]
    · simp only [zero_add, one_mul]
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
        getD_map_range _ hq, Nat.mod_eq_of_lt (g_lt _ _)]
      simp only [g, toQ, dite_eq_left hq, Fin.eta]
    · omega
  have hact : ∀ (w : List (Fin 2)) (q : Fin (m + 2)),
      B.act q w = e (A.act (e.symm q) (w.map (fun c => L c.val))) := by
    intro w
    induction w with
    | nil => intro q; simp [Automaton.act]
    | cons c w ih =>
      intro q
      change B.act (B.step q c) w = e (A.act (A.step (e.symm q) (L c.val)) (w.map (fun c => L c.val)))
      rw [ih, hstep, Equiv.symm_apply_apply]
  -- the renamed automaton is synchronizing
  have hBsync : B.Synchronizing := by
    obtain ⟨u, r, hu⟩ := hA
    let LL : S → Fin 2 := fun c => if c = a then 0 else 1
    have hLL : (u.map LL).map (fun c => L c.val) = u := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id u]
      apply List.map_congr_left
      intro c _
      simp only [Function.comp, LL, L]
      by_cases hc : c = a
      · simp [hc]
      · rw [ite_eq_right hc]
        simp only [Fin.isValue, id]
        exact ((hS c).resolve_left hc).symm
    exact ⟨u.map LL, e r, fun q => by rw [hact, hLL, hu]⟩
  -- the edge assignment is in the census family
  have hσlen : σ.length = 2 * (m + 2 - 2) := by simp [σ]; omega
  have hσlt : ∀ v ∈ σ, v < m + 2 := by
    intro v hv
    simp only [σ, List.mem_append, List.mem_map, List.mem_range] at hv
    rcases hv with ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩ <;> exact g_lt _ _
  have htrans : ∀ (c v : ℕ), v < m + 2 →
      ((Finset.range m).filter (fun q => g q c = v)).card = fE A W.E (L c) (toQ v) := by
    intro c v hv
    unfold fE
    apply Finset.card_nbij' toQ (fun y => (e y).val)
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hq ⊢
      refine ⟨(memE _).2 (by rw [e_toQ q (by omega)]; exact hq.1), ?_⟩
      rw [← hq.2, toQ_e]
    · intro y hy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hy ⊢
      refine ⟨(memE y).1 hy.1, ?_⟩
      simp only [g, toQ_e, hy.2, e_toQ v hv]
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hq
      exact e_toQ q (by omega)
    · intro y _
      exact toQ_e y
  have hσcount : ∀ v, σ.count v ≤ (cntOf (m + 2) t).getD v 0 := by
    intro v
    by_cases hv : v < m + 2
    · have hc : σ.count v = fE A W.E a (toQ v) + fE A W.E b (toQ v) := by
        simp only [σ, List.count_append, count_map_range, htrans 0 v hv, htrans 1 v hv, L, ite_eq_left rfl,
          ite_eq_right one_ne_zero]
      rw [hc]
      unfold cntOf
      rw [getD_map_range _ hv, ht]
      simp only [rawOf, List.getD_cons_succ, List.getD_cons_zero, Automaton.configOf]
      have hcs := count_s A a b hab hS W hX h12
      by_cases h0 : v = 0
      · subst h0
        rw [ite_eq_left rfl, toQ0]
        omega
      · rw [ite_eq_right h0]
        by_cases h1 : v = m + 2 - 2
        · rw [ite_eq_left h1]
          rw [Nat.add_sub_cancel] at h1
          subst h1
          rw [toQ1, nuOf_eq]
        · rw [ite_eq_right h1]
          by_cases h2 : v = m + 2 - 1
          · rw [ite_eq_left h2]
            rw [show m + 2 - 1 = m + 1 by omega] at h2
            subst h2
            rw [toQ2, nuOf_eq]
          · rw [ite_eq_right h2]
            have hvE : toQ v ∈ W.E := (memE _).2 (by rw [e_toQ v hv]; omega)
            have hvs : toQ v ≠ W.s := fun h => by
              have := e_toQ v hv
              rw [h, he0] at this
              omega
            rw [indeg A a b hab hS W (toQ v) hvE hvs]
    · have : σ.count v = 0 := List.count_eq_zero.2 (fun hm => hv (hσlt v hm))
      omega
  -- the check gives a short reset word of the table automaton, hence of `A`
  obtain ⟨w, hw, hwl⟩ := memberOK_sound (m + 2) M _ (hfam σ hσlen hσlt hσcount) hBsync
  obtain ⟨rB, hrB⟩ := hw
  have hAw : A.IsReset (w.map (fun c => L c.val)) := by
    refine ⟨e.symm rB, fun q => ?_⟩
    have := hact w (e q)
    rw [hrB, Equiv.symm_apply_apply] at this
    rw [this, Equiv.symm_apply_apply]
  calc A.rt ≤ ((w.map (fun c => L c.val)).length : ℕ∞) := minLen_le_of' hAw
    _ ≤ (M : ℕ∞) := by rw [List.length_map]; exact_mod_cast hwl

end Reduction

/-! ### The joining theorem: the chunks of each configuration -/

theorem famOK4 : ∀ t ∈ canonCfgs, FamOK 4 8 t := by
  intro t ht
  simp only [canonCfgs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c0
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c1
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c2
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c3
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c4
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c5
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c6
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c7
  · exact famOK_of_chunks 4 8 _ (by norm_num) N4_c8

theorem famOK5 : ∀ t ∈ canonCfgs, FamOK 5 13 t := by
  intro t ht
  simp only [canonCfgs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c0
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c1
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c2
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c3
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c4
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c5
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c6
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c7
  · exact famOK_of_chunks 5 13 _ (by norm_num) N5_c8

theorem famOK6 : ∀ t ∈ canonCfgs, FamOK 6 19 t := by
  intro t ht
  simp only [canonCfgs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c0
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c1
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c2
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c3
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c4
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c5
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c6
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c7
  · exact famOK_of_chunks 6 19 _ (by norm_num) N6_c8

/-! ### The census bound -/

section Census

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]

/-- The bound for a canonical configuration, for `4 ≤ n ≤ 6`. -/
theorem rt_le_of_canon (A : Automaton Q S) (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b)
    (hA : A.Synchronizing) (hn4 : 4 ≤ Fintype.card Q) (hn6 : Fintype.card Q ≤ 6) (W : QEWitness A 2)
    (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (hc : rawOf (A.configOf a b W.E x₁ x₂) ∈ canonCfgs) :
    A.rt ≤ ((if Fintype.card Q = 4 then 8 else if Fintype.card Q = 5 then 13 else 19 : ℕ) : ℕ∞) := by
  have hn : Fintype.card Q = 4 ∨ Fintype.card Q = 5 ∨ Fintype.card Q = 6 := by omega
  rcases hn with h | h | h
  · rw [ite_eq_left h]
    exact reduce (by norm_num) (famOK4 _ hc) A a b hab hS W x₁ x₂ hX h12 h rfl hA
  · rw [ite_eq_right (by omega), ite_eq_left h]
    exact reduce (by norm_num) (famOK5 _ hc) A a b hab hS W x₁ x₂ hX h12 h rfl hA
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact reduce (by norm_num) (famOK6 _ hc) A a b hab hS W x₁ x₂ hX h12 h rfl hA

/-- The census bound in the integer classes, for `4 ≤ n ≤ 6`: `rt ≤ 8, 13, 19`. -/
theorem rt_le_census (A : Automaton Q S) (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b)
    (hA : A.Synchronizing) (hn4 : 4 ≤ Fintype.card Q) (hn6 : Fintype.card Q ≤ 6) (W : QEWitness A 2)
    (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((if Fintype.card Q = 4 then 8 else if Fintype.card Q = 5 then 13 else 19 : ℕ) : ℕ∞) := by
  have hX' : Finset.univ \ W.E = {x₁, x₂} := hX
  rw [alphaStat_cfg₁ A a b hab hS W.E hX' h12, alphaStat_cfg₂ A a b hab hS W.E hX' h12] at hcl
  set cf := A.configOf a b W.E x₁ x₂ with hcf
  have hν : cf.nu1 + cf.nu2 ≤ 2 := by
    have := count_s A a b hab hS W hX h12
    simp only [hcf, Automaton.configOf]
    omega
  have hint : IntClass cf := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcl
    unfold IntClass
    norm_cast at hcl
  have hcan : CanonOK cf :=
    canon_table cf.x1a cf.x1b cf.x2a cf.x2b ⟨cf.nu1, by omega⟩ ⟨cf.nu2, by omega⟩ hν hint
  rcases hcan with h | h | h | h
  · exact rt_le_of_canon A a b hab hS hA hn4 hn6 W x₁ x₂ hX h12 h
  · rw [hcf, ← configOf_swapX A a b W.E h12] at h
    exact rt_le_of_canon A a b hab hS hA hn4 hn6 W x₂ x₁ (by rw [hX, Finset.pair_comm]) (Ne.symm h12) h
  · rw [hcf, ← configOf_swapL A a b W.E x₁ x₂] at h
    exact rt_le_of_canon A b a (Ne.symm hab) (fun c => (hS c).symm) hA hn4 hn6 W x₁ x₂ hX h12 h
  · rw [hcf, ← configOf_swapX A a b W.E h12, ← configOf_swapL A a b W.E x₂ x₁] at h
    exact rt_le_of_canon A b a (Ne.symm hab) (fun c => (hS c).symm) hA hn4 hn6 W x₂ x₁
      (by rw [hX, Finset.pair_comm]) (Ne.symm h12) h

end Census

/-! ### The automata that attain the bounds -/

/-- The witness `E = {0, …, n-3}`, `s = 0`, `p = (1/2, 1/2)` of a table automaton. -/
noncomputable def lowW (n : ℕ) [NeZero n] (tbl : List ℕ) (hcard : (lowE n).card = n - 2) (hs : (0 : Fin n) ∈ lowE n)
    (hedge : ∀ q : Fin n, q ∉ lowE n → ∀ c : Fin 2,
      (tabAut n tbl).step q c ∉ lowE n ∨ (tabAut n tbl).step q c = 0)
    (hdeg : ∀ r : Fin n, r ∈ lowE n → r ≠ 0 →
      ((tabAut n tbl).pre {r} [0]).card + ((tabAut n tbl).pre {r} [1]).card = 2) :
    QEWitness (tabAut n tbl) 2 where
  E := lowE n
  s := 0
  p := fun _ => 1 / 2
  card_E := by rw [Fintype.card_fin]; exact hcard
  s_mem := hs
  weights := ⟨fun _ => by norm_num, by rw [Fin.sum_univ_two]; norm_num⟩
  edge_X := hedge
  inW_one := fun r hr hrs => by
    unfold Automaton.inW
    rw [Fin.sum_univ_two]
    have h := hdeg r hr hrs
    have h' : (((tabAut n tbl).pre {r} [0]).card : ℝ) + (((tabAut n tbl).pre {r} [1]).card : ℝ) = 2 := by
      exact_mod_cast h
    linarith

theorem fin2_ne : (0 : Fin 2) ≠ 1 := by decide

theorem low4_s : (0 : Fin 4) ∈ lowE 4 := by decide
theorem low5_s : (0 : Fin 5) ∈ lowE 5 := by decide
theorem low6_s : (0 : Fin 6) ∈ lowE 6 := by decide

theorem fin2_cases (c : Fin 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

end Census514

open Census514 ImageSearch

/-- Supplement to Proposition 5.14, tex:932, 939-940: for `n = 4, 5, 6` the largest reset thresholds in the three integer classes are
`8`, `13` and `19` (an upper bound for every such automaton, attained by one). -/
theorem prop_5_14_max_proved (n : ℕ) (hn : n = 4 ∨ n = 5 ∨ n = 6) :
    (∀ (Q : Type u) [Fintype Q] [DecidableEq Q] (A : Automaton Q (Fin 2)), Fintype.card Q = n →
      A.Synchronizing → A.StronglyConnected → ∀ (W : QEWitness A 2) (x₁ x₂ : Q), W.X = {x₁, x₂} → x₁ ≠ x₂ →
      (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
        ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ)) →
      A.rt ≤ ((if n = 4 then 8 else if n = 5 then 13 else 19 : ℕ) : ℕ∞)) ∧
    ∃ (A : Automaton (Fin n) (Fin 2)) (W : QEWitness A 2) (x₁ x₂ : Fin n), W.X = {x₁, x₂} ∧ x₁ ≠ x₂ ∧
      A.Synchronizing ∧ A.StronglyConnected ∧
      (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
        ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ)) ∧
      A.rt = ((if n = 4 then 8 else if n = 5 then 13 else 19 : ℕ) : ℕ∞) := by
  refine ⟨fun Q _ _ A hcard hA _ W x₁ x₂ hX h12 hcl => ?_, ?_⟩
  · have h := rt_le_census A 0 1 fin2_ne fin2_cases hA (by omega) (by omega) W x₁ x₂ hX h12 hcl
    rwa [hcard] at h
  · rcases hn with rfl | rfl | rfl
    · refine ⟨tabAut 4 lowTbl4, lowW 4 lowTbl4 low4_cardE low4_s low4_edgeX low4_indeg, 2, 3, low4_X,
        by decide, sync_of_imgs _ 8 low4_upper, low4_sc, ?_, ?_⟩
      · show ((tabAut 4 lowTbl4).alphaStat (lowE 4) (fun _ => 1 / 2) 2,
          (tabAut 4 lowTbl4).alphaStat (lowE 4) (fun _ => 1 / 2) 3) ∈
            ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))
        rw [alphaStat_cfg₁ _ 0 1 fin2_ne fin2_cases (lowE 4) low4_X (by decide),
          alphaStat_cfg₂ _ 0 1 fin2_ne fin2_cases (lowE 4) low4_X (by decide), low4_cfg, low_t4.1, low_t4.2]
        norm_num
      · rw [rt_eq_succ _ 7 low4_upper low4_lower]
        rfl
    · refine ⟨tabAut 5 lowTbl5, lowW 5 lowTbl5 low5_cardE low5_s low5_edgeX low5_indeg, 3, 4, low5_X,
        by decide, sync_of_imgs _ 13 low5_upper, low5_sc, ?_, ?_⟩
      · show ((tabAut 5 lowTbl5).alphaStat (lowE 5) (fun _ => 1 / 2) 3,
          (tabAut 5 lowTbl5).alphaStat (lowE 5) (fun _ => 1 / 2) 4) ∈
            ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))
        rw [alphaStat_cfg₁ _ 0 1 fin2_ne fin2_cases (lowE 5) low5_X (by decide),
          alphaStat_cfg₂ _ 0 1 fin2_ne fin2_cases (lowE 5) low5_X (by decide), low5_cfg, low_t5.1, low_t5.2]
        norm_num
      · rw [rt_eq_succ _ 12 low5_upper low5_lower]
        rfl
    · refine ⟨tabAut 6 lowTbl6, lowW 6 lowTbl6 low6_cardE low6_s low6_edgeX low6_indeg, 4, 5, low6_X,
        by decide, sync_of_imgs _ 19 low6_upper, low6_sc, ?_, ?_⟩
      · show ((tabAut 6 lowTbl6).alphaStat (lowE 6) (fun _ => 1 / 2) 4,
          (tabAut 6 lowTbl6).alphaStat (lowE 6) (fun _ => 1 / 2) 5) ∈
            ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))
        rw [alphaStat_cfg₁ _ 0 1 fin2_ne fin2_cases (lowE 6) low6_X (by decide),
          alphaStat_cfg₂ _ 0 1 fin2_ne fin2_cases (lowE 6) low6_X (by decide), low6_cfg, low_t6.1, low_t6.2]
        norm_num
      · rw [rt_eq_succ _ 18 low6_upper low6_lower]
        rfl

/-- Proposition 5.14 for `4 ≤ n ≤ 6` (the census): `rt ≤ (n-1)^2` in the three integer classes. -/
theorem prop_5_14_small_proved {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S]
    (A : Automaton Q S) (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (_hsc : A.StronglyConnected) (hn4 : 4 ≤ Fintype.card Q) (hn6 : Fintype.card Q ≤ 6) (W : QEWitness A 2)
    (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  refine (rt_le_census A a b hab hS hA hn4 hn6 W x₁ x₂ hX h12 hcl).trans ?_
  have hn : Fintype.card Q = 4 ∨ Fintype.card Q = 5 ∨ Fintype.card Q = 6 := by omega
  rcases hn with h | h | h <;> rw [h] <;> norm_num

end CernyQE
