/-
CernyQE/Proofs/BinaryBase.lean — the foundations of the binary case of degree two: the weights (1/2, 1/2), the configuration of a witness, patterns, good patterns and the joint orbit lemma.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary
import CernyQE.Proofs.Basic
import CernyQE.Proofs.Sec2
import CernyQE.Proofs.Stationary

namespace CernyQE

open Classical Automaton Matrix

universe u v

section Binary

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-! ### Two letters -/

private theorem univ_eq_pair {a b : S} (hS : ∀ c, c = a ∨ c = b) : (Finset.univ : Finset S) = {a, b} := by
  ext c
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact hS c

private theorem sum_letters {M : Type*} [AddCommMonoid M] {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b)
    (f : S → M) : ∑ c, f c = f a + f b := by
  rw [univ_eq_pair hS, Finset.sum_pair hab]

private theorem card_filter_letters {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (P : S → Prop)
    [DecidablePred P] : ((Finset.univ.filter P).card : ℝ) = (if P a then 1 else 0) + (if P b then 1 else 0) := by
  rw [Finset.natCast_card_filter, sum_letters hab hS]

private theorem card_filter_fin2 (P : Fin 2 → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℝ) = (if P 0 then 1 else 0) + (if P 1 then 1 else 0) := by
  rw [Finset.natCast_card_filter, Fin.sum_univ_two]

/-! ### Preimages and counting -/

omit [Fintype S] in
private theorem pre_single (r : Q) (c : S) : A.pre {r} [c] = Finset.univ.filter (fun q => A.step q c = r) := by
  ext q
  simp

omit [Fintype Q] [Fintype S] in
private theorem card_filter_mem (D T : Finset Q) (c : S) :
    (D.filter (fun q => A.step q c ∈ T)).card = ∑ r ∈ T, (D.filter (fun q => A.step q c = r)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q => A.step q c) (s := D.filter (fun q => A.step q c ∈ T))
    (t := T) (fun q hq => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2)]
  refine Finset.sum_congr rfl fun r hr => ?_
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hq, _⟩, h⟩
    exact ⟨hq, h⟩
  · rintro ⟨hq, h⟩
    exact ⟨⟨hq, h ▸ hr⟩, h⟩

/-- A state whose `c`-successor lies in `E \ {s}` lies in `E` (Definition 1.1 (a)). -/
private theorem mem_E_of_step {d : ℕ} (W : QEWitness A d) {q : Q} {c : S} (h : A.step q c ∈ W.E)
    (hs : A.step q c ≠ W.s) : q ∈ W.E := by
  by_contra hq
  rcases W.edge_X q hq c with h' | h'
  · exact h' h
  · exact hs h'

/-- Every edge from `X` ends in `X ∪ {s}`. -/
private theorem step_X {d : ℕ} (W : QEWitness A d) {x : Q} (hx : x ∉ W.E) (c : S) :
    A.step x c ∈ insert W.s W.X := by
  rcases W.edge_X x hx c with h | h
  · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩)
  · rw [h]
    exact Finset.mem_insert_self _ _

private theorem not_mem_E {d : ℕ} (W : QEWitness A d) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) {q : Q}
    (hq : q ∈ ({x₁, x₂} : Finset Q)) : q ∉ W.E := by
  rw [← hX] at hq
  exact (Finset.mem_sdiff.mp hq).2

private theorem mem_E_of_ne {d : ℕ} (W : QEWitness A d) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) {q : Q}
    (h1 : q ≠ x₁) (h2 : q ≠ x₂) : q ∈ W.E := by
  by_contra hq
  have h : q ∈ W.X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq⟩
  rw [hX] at h
  simp [h1, h2] at h

/-- The number of `c`-edges from `E` into `E \ {s}` is the sum of the `c`-in-degrees on `E \ {s}`. -/
private theorem card_into_E' {d : ℕ} (W : QEWitness A d) (c : S) :
    (W.E.filter (fun q => A.step q c ∈ W.E.erase W.s)).card =
      ∑ r ∈ W.E.erase W.s, (A.pre {r} [c]).card := by
  have h : W.E.filter (fun q => A.step q c ∈ W.E.erase W.s) =
      Finset.univ.filter (fun q => A.step q c ∈ W.E.erase W.s) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro hq
    obtain ⟨hne, hE⟩ := Finset.mem_erase.mp hq
    exact mem_E_of_step A W hE hne
  rw [h, card_filter_mem]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pre_single]

/-- The `c`-edges from `E` end in `X ∪ {s}` or in `E \ {s}`. -/
private theorem card_T_add {d : ℕ} (W : QEWitness A d) (c : S) :
    (W.E.filter (fun q => A.step q c ∈ insert W.s W.X)).card +
      (W.E.filter (fun q => A.step q c ∈ W.E.erase W.s)).card = W.E.card := by
  rw [← Finset.card_filter_add_card_filter_not (s := W.E) (fun q => A.step q c ∈ insert W.s W.X)]
  congr 2
  ext q
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase, QEWitness.X, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  tauto

/-! ### In-degrees (Lemma 5.7 (a)) -/

private theorem inW_pair {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (p : S → ℝ) (r : Q) :
    A.inW p r = p a * (A.pre {r} [a]).card + p b * (A.pre {r} [b]).card := by
  rw [Automaton.inW, sum_letters hab hS]

/-- The solutions of `p_a i_a + p_b i_b = 1` in natural numbers, for `0 < p_a, p_b` with `p_a + p_b = 1`. -/
private theorem type_cases {pa pb : ℝ} (ha : 0 < pa) (hb : 0 < pb) (hsum : pa + pb = 1) {i j : ℕ}
    (h : pa * i + pb * j = 1) :
    i + j = 2 ∨ (3 ≤ i ∧ j = 0 ∧ pa * i = 1) ∨ (3 ≤ j ∧ i = 0 ∧ pb * j = 1) := by
  rcases Nat.eq_zero_or_pos i with hi | hi <;> rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hi hj
    norm_num at h
  · subst hi
    simp only [Nat.cast_zero, mul_zero, zero_add] at h
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · interval_cases j
      · exfalso
        norm_num at h
        linarith
      · left; rfl
    · right; right; exact ⟨hj3, rfl, h⟩
  · subst hj
    simp only [Nat.cast_zero, mul_zero, add_zero] at h
    rcases Nat.lt_or_ge i 3 with hi3 | hi3
    · interval_cases i
      · exfalso
        norm_num at h
        linarith
      · left; rfl
    · right; left; exact ⟨hi3, rfl, h⟩
  · left
    have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hi1 : i = 1 := by
      by_contra hne
      have h2 : (2 : ℝ) ≤ i := by exact_mod_cast (show 2 ≤ i by omega)
      nlinarith
    have hj1 : j = 1 := by
      by_contra hne
      have h2 : (2 : ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
      nlinarith
    omega

/-- No state of `E \ {s}` has type `(k, 0)` with `k ≥ 3` (count the `c`-edges into `E \ {s}`). -/
private theorem no_bad_type {d : ℕ} (W : QEWitness A d) {c e : S} (hce : c ≠ e) (hS : ∀ x, x = c ∨ x = e)
    (r₀ : Q) (hr₀ : r₀ ∈ W.E.erase W.s) (h3 : 3 ≤ (A.pre {r₀} [c]).card)
    (hpc : W.p c * (A.pre {r₀} [c]).card = 1) : False := by
  have hw := W.weights
  have hpc0 := hw.1 c
  have hpe0 := hw.1 e
  have hsum : W.p c + W.p e = 1 := by rw [← sum_letters hce hS W.p]; exact hw.2
  have hk : (3 : ℝ) ≤ (A.pre {r₀} [c]).card := by exact_mod_cast h3
  have hpc3 : W.p c * 3 ≤ 1 := by nlinarith
  -- every state of `E \ {s}` has a `c`-edge
  have hall : ∀ r ∈ W.E.erase W.s, 1 ≤ (A.pre {r} [c]).card := by
    intro r hr
    obtain ⟨hrs, hrE⟩ := Finset.mem_erase.mp hr
    have h1 := W.inW_one r hrE hrs
    rw [inW_pair A hce hS] at h1
    rcases type_cases hpc0 hpe0 hsum h1 with h | ⟨h3', _, _⟩ | ⟨h3', h0', hpe⟩
    · by_contra hlt
      have hc0 : (A.pre {r} [c]).card = 0 := by omega
      have he2 : (A.pre {r} [e]).card = 2 := by omega
      rw [hc0, he2] at h1
      norm_num at h1
      linarith
    · omega
    · exfalso
      have hk' : (3 : ℝ) ≤ (A.pre {r} [e]).card := by exact_mod_cast h3'
      nlinarith
  -- count the `c`-edges into `E \ {s}`
  have hle : ∑ r ∈ W.E.erase W.s, (A.pre {r} [c]).card ≤ W.E.card := by
    rw [← card_into_E']
    exact Finset.card_filter_le _ _
  have hge : (W.E.erase W.s).card + 2 ≤ ∑ r ∈ W.E.erase W.s, (A.pre {r} [c]).card := by
    rw [← Finset.add_sum_erase _ _ hr₀]
    have hrest : ((W.E.erase W.s).erase r₀).card ≤ ∑ r ∈ (W.E.erase W.s).erase r₀, (A.pre {r} [c]).card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun r hr => hall r (Finset.mem_of_mem_erase hr)
    have hcard := Finset.card_erase_of_mem hr₀
    have hpos : 1 ≤ (W.E.erase W.s).card := Finset.card_pos.mpr ⟨r₀, hr₀⟩
    omega
  have hcardE := Finset.card_erase_of_mem W.s_mem
  have hEpos : 1 ≤ W.E.card := Finset.card_pos.mpr ⟨W.s, W.s_mem⟩
  omega

/-- Lemma 5.7(a), tex:700-705. Count the edges labelled c into the n−3 ordinary states when N of them receive k edges and the rest receive one. -/
theorem lem_5_7_edge_count_proved (W : QEWitness A 2) (c : S) (B : Finset Q) (k : ℕ)
    (hB : B ⊆ W.E.erase W.s) (hbig : ∀ r ∈ B, (A.pre {r} [c]).card = k)
    (hsmall : ∀ r ∈ W.E.erase W.s, r ∉ B → (A.pre {r} [c]).card = 1) :
    let n := Fintype.card Q
    let N := B.card
    let total := (n-3-N) + N*k
    (W.E.erase W.s).card = n-3 ∧ (∑ r ∈ W.E.erase W.s, (A.pre {r} [c]).card) = total ∧
      total + 2 ≤ n ∧ (1 ≤ N → 3 ≤ k → total + 2 = n-1 + N*(k-1) ∧ n+1 ≤ total+2) := by
  dsimp only
  have he := W.card_E
  have hpos := Finset.card_pos.mpr ⟨W.s,W.s_mem⟩
  have hstates := Finset.card_erase_of_mem W.s_mem
  have hcard : (W.E.erase W.s).card = Fintype.card Q - 3 := by omega
  have hn := Finset.card_le_card hB
  have hsum := Finset.sum_sdiff hB (f := fun r => (A.pre {r} [c]).card)
  have hdiff : (∑ r ∈ (W.E.erase W.s) \ B, (A.pre {r} [c]).card) = ((W.E.erase W.s) \ B).card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl (fun r hr => hsmall r (Finset.mem_sdiff.mp hr).1 (Finset.mem_sdiff.mp hr).2)
  have hsb : (∑ r ∈ B, (A.pre {r} [c]).card) = B.card*k := by
    rw [Finset.sum_congr rfl hbig, Finset.sum_const, smul_eq_mul]
  rw [hdiff,hsb,Finset.card_sdiff_of_subset hB,hcard] at hsum
  have hl : (∑ r ∈ W.E.erase W.s, (A.pre {r} [c]).card) ≤ W.E.card := by
    rw [← card_into_E']
    exact Finset.card_filter_le _ _
  refine ⟨hcard, hsum.symm, by omega, ?_⟩
  intro hN hk
  have hmul : B.card * (k-1) + B.card = B.card*k := by
    rw [← Nat.mul_succ, show (k-1).succ = k by omega]
  have hmin : 2 ≤ B.card * (k-1) := by
    simpa using Nat.mul_le_mul hN (show 2 ≤ k-1 by omega)
  omega

/-- Every state of `E \ {s}` has in-degree two (binary alphabet). -/
private theorem indeg_two {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) {d : ℕ} (W : QEWitness A d)
    (r : Q) (hr : r ∈ W.E) (hrs : r ≠ W.s) : (A.pre {r} [a]).card + (A.pre {r} [b]).card = 2 := by
  have hw := W.weights
  have hsum : W.p a + W.p b = 1 := by rw [← sum_letters hab hS W.p]; exact hw.2
  have h1 := W.inW_one r hr hrs
  rw [inW_pair A hab hS] at h1
  have hr' : r ∈ W.E.erase W.s := Finset.mem_erase.mpr ⟨hrs, hr⟩
  rcases type_cases (hw.1 a) (hw.1 b) hsum h1 with h | ⟨h3, -, hpc⟩ | ⟨h3, -, hpc⟩
  · exact h
  · exact (no_bad_type A W hab hS r hr' h3 hpc).elim
  · exact (no_bad_type A W hab.symm (fun x => (hS x).symm) r hr' h3 hpc).elim

/-- Lemma 5.7(a), tex:687: the weights `(1/2, 1/2)` are admissible for `(E, s)`. -/
theorem lem_5_7_a_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) :
    ∃ W' : QEWitness A 2, W'.E = W.E ∧ W'.s = W.s ∧ W'.p = fun _ => 1 / 2 := by
  refine ⟨⟨W.E, W.s, fun _ => 1 / 2, W.card_E, W.s_mem, ?_, W.edge_X, ?_⟩, rfl, rfl, rfl⟩
  · refine ⟨fun _ => by norm_num, ?_⟩
    rw [sum_letters hab hS]
    norm_num
  · intro r hr hrs
    rw [inW_pair A hab hS]
    have h := indeg_two A hab hS W r hr hrs
    have h' : ((A.pre {r} [a]).card : ℝ) + (A.pre {r} [b]).card = 2 := by exact_mod_cast h
    linarith

/-- Lemma 5.7, tex:705-708 (also used in the proof of Proposition 5.14): every state of `E \ {s}` is entered by exactly two edges, all from `E`. -/
theorem prop_5_14_entry_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (r : Q)
    (hr : r ∈ W.E) (hrs : r ≠ W.s) :
    (A.pre {r} [a]).card + (A.pre {r} [b]).card = 2 ∧ A.pre {r} [a] ⊆ W.E ∧ A.pre {r} [b] ⊆ W.E := by
  refine ⟨indeg_two A hab hS W r hr hrs, ?_, ?_⟩
  · intro q hq
    simp only [mem_pre, act_singleton, Finset.mem_singleton] at hq
    exact mem_E_of_step A W (by rw [hq]; exact hr) (by rw [hq]; exact hrs)
  · intro q hq
    simp only [mem_pre, act_singleton, Finset.mem_singleton] at hq
    exact mem_E_of_step A W (by rw [hq]; exact hr) (by rw [hq]; exact hrs)

/-! ### The configuration of a witness (Lemma 5.7 (b)) -/

omit [Fintype Q] [Fintype S] in
private theorem card_prod_filter {a b : S} (hab : a ≠ b) (D T : Finset Q) :
    ((D ×ˢ ({a, b} : Finset S)).filter (fun e => A.step e.1 e.2 ∈ T)).card =
      (D.filter (fun q => A.step q a ∈ T)).card + (D.filter (fun q => A.step q b ∈ T)).card := by
  rw [Finset.card_filter, Finset.sum_product, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_pair hab]

/-- Exactly two edges lead from `E` into `X ∪ {s}`. -/
private theorem boundary_two {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) {d : ℕ} (W : QEWitness A d) :
    (W.E.filter (fun q => A.step q a ∈ insert W.s W.X)).card +
      (W.E.filter (fun q => A.step q b ∈ insert W.s W.X)).card = 2 := by
  have h1 := card_T_add A W a
  have h2 := card_T_add A W b
  rw [card_into_E'] at h1 h2
  have h3 : ∑ r ∈ W.E.erase W.s, (A.pre {r} [a]).card + ∑ r ∈ W.E.erase W.s, (A.pre {r} [b]).card =
      2 * (W.E.erase W.s).card := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun r hr => indeg_two A hab hS W r (Finset.mem_of_mem_erase hr)
        (Finset.ne_of_mem_erase hr)]
    simp [mul_comm]
  have h4 := Finset.card_erase_of_mem W.s_mem
  have h5 : 1 ≤ W.E.card := Finset.card_pos.mpr ⟨W.s, W.s_mem⟩
  omega

omit [Fintype Q] [Fintype S] in
private theorem stateCode_eq_iff {x₁ x₂ : Q} (h12 : x₁ ≠ x₂) (q : Q) (j : Fin 2) :
    stateCode x₁ x₂ q = Fin.castSucc j ↔ q = ![x₁, x₂] j := by
  unfold stateCode
  fin_cases j
  · by_cases h1 : q = x₁
    · simp [h1]
    · by_cases h2 : q = x₂
      · simp [h2]
      · simp [h1, h2]
  · by_cases h1 : q = x₁
    · subst h1
      simp [h12]
    · by_cases h2 : q = x₂
      · subst h2
        simp [h1]
      · simp [h1, h2]

omit [Fintype Q] [Fintype S] in
private theorem tgt_configOf (a b : S) (E : Finset Q) (x₁ x₂ : Q) (i c : Fin 2) :
    (A.configOf a b E x₁ x₂).tgt i c = stateCode x₁ x₂ (A.step (![x₁, x₂] i) (![a, b] c)) := by
  fin_cases i <;> fin_cases c <;> rfl

omit [Fintype Q] in
private theorem zPair_half (x x' : Q) :
    A.zPair (fun _ => 1 / 2) x x' = 1 / 2 * ((Finset.univ.filter (fun c => A.step x c = x')).card : ℝ) := by
  simp [Automaton.zPair, Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [Fintype Q] [Fintype S] in
private theorem Z_configOf (a b : S) (E : Finset Q) {x₁ x₂ : Q} (h12 : x₁ ≠ x₂) (i j : Fin 2) :
    (((A.configOf a b E x₁ x₂).Z i j : ℚ) : ℝ) =
      1 / 2 * ((if A.step (![x₁, x₂] i) a = ![x₁, x₂] j then 1 else 0) +
        (if A.step (![x₁, x₂] i) b = ![x₁, x₂] j then 1 else 0)) := by
  simp only [Config.Z]
  push_cast
  rw [card_filter_fin2, tgt_configOf, tgt_configOf]
  simp only [stateCode_eq_iff h12, Matrix.cons_val_zero, Matrix.cons_val_one]

omit [Fintype Q] in
private theorem Z_entry {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (E : Finset Q) {x₁ x₂ : Q}
    (h12 : x₁ ≠ x₂) (i j : Fin 2) :
    A.zPair (fun _ => 1 / 2) (![x₁, x₂] i) (![x₁, x₂] j) = ((A.configOf a b E x₁ x₂).Z i j : ℝ) := by
  rw [zPair_half, card_filter_letters hab hS, Z_configOf A a b E h12]

omit [Fintype Q] in
private theorem yIn_half {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (E : Finset Q) (x : Q) :
    A.yIn E (fun _ => 1 / 2) x = ((((A.nuOf a b E x : ℕ) : ℚ) / 2 : ℚ) : ℝ) := by
  rw [Automaton.yIn, sum_letters hab hS, Automaton.nuOf]
  push_cast
  ring

omit [Fintype Q] [Fintype S] in
private theorem y_configOf (a b : S) (E : Finset Q) (x₁ x₂ : Q) (i : Fin 2) :
    (A.configOf a b E x₁ x₂).y i = ((A.nuOf a b E (![x₁, x₂] i) : ℕ) : ℚ) / 2 := by
  fin_cases i <;> rfl

omit [Fintype Q] in
private theorem y_entry {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (E : Finset Q) (x₁ x₂ : Q)
    (i : Fin 2) : A.yIn E (fun _ => 1 / 2) (![x₁, x₂] i) = ((A.configOf a b E x₁ x₂).y i : ℝ) := by
  rw [yIn_half A hab hS, y_configOf]

private theorem nu_le_two {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) {x₁ x₂ : Q}
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    (A.configOf a b W.E x₁ x₂).nu1 + (A.configOf a b W.E x₁ x₂).nu2 ≤ 2 := by
  have hsub : ({x₁, x₂} : Finset Q) ⊆ insert W.s W.X := by
    rw [hX]
    exact Finset.subset_insert _ _
  have hc : ∀ c : S, (W.E.filter (fun q => A.step q c = x₁)).card + (W.E.filter (fun q => A.step q c = x₂)).card ≤
      (W.E.filter (fun q => A.step q c ∈ insert W.s W.X)).card := by
    intro c
    have h := Finset.sum_le_sum_of_subset (f := fun r => (W.E.filter (fun q => A.step q c = r)).card) hsub
    rw [Finset.sum_pair h12] at h
    rw [card_filter_mem]
    exact h
  have h := boundary_two A hab hS W
  have ha := hc a
  have hb := hc b
  simp only [Automaton.configOf, Automaton.nuOf]
  omega

/-- The exceptional states as `Fin 2`. -/
private theorem memX {d : ℕ} (W : QEWitness A d) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (i : Fin 2) :
    ![x₁, x₂] i ∈ (Finset.univ \ W.E : Finset Q) := by
  have h : (Finset.univ \ W.E : Finset Q) = {x₁, x₂} := hX
  rw [h]
  fin_cases i <;> simp

/-- The equivalence `Fin 2 ≃ X`. -/
private noncomputable def xEquiv {d : ℕ} (W : QEWitness A d) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    Fin 2 ≃ (Finset.univ \ W.E : Finset Q) :=
  Equiv.ofBijective (fun i => ⟨![x₁, x₂] i, memX A W hX i⟩) (by
    constructor
    · intro i j h
      have h' : ![x₁, x₂] i = ![x₁, x₂] j := congrArg Subtype.val h
      fin_cases i <;> fin_cases j <;> simp_all [h12.symm]
    · rintro ⟨x, hx⟩
      have h : (Finset.univ \ W.E : Finset Q) = {x₁, x₂} := hX
      rw [h] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)

private theorem xEquiv_val {d : ℕ} (W : QEWitness A d) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (i : Fin 2) : (xEquiv A W hX h12 i).1 = ![x₁, x₂] i := rfl

/-- `I - Z` for the weights `(1/2, 1/2)` is invertible, and the vector of Lemma 5.5 is positive. -/
private theorem half_stat {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) :
    IsUnit (1 - A.Zmat W.E (fun _ => 1 / 2)) ∧ ∀ q, 0 < A.alphaStat W.E (fun _ => 1 / 2) q := by
  obtain ⟨W', hE, -, hp⟩ := lem_5_7_a_proved A a b hab hS W
  obtain ⟨hU, -, hpos⟩ := lem_5_5_proved A hsc W'
  rw [hE, hp] at hU hpos
  exact ⟨hU, hpos⟩

/-- Cramer's rule for the `2 × 2` system `t (I - Z) = y`. -/
private theorem cramer {t0 t1 y0 y1 z00 z01 z10 z11 : ℝ} (hdet : (1 - z00) * (1 - z11) - z01 * z10 ≠ 0)
    (h0 : t0 * (1 - z00) + t1 * (0 - z10) = y0) (h1 : t0 * (0 - z01) + t1 * (1 - z11) = y1) :
    t0 = (y0 * (1 - z11) + y1 * z10) / ((1 - z00) * (1 - z11) - z01 * z10) ∧
      t1 = (y1 * (1 - z00) + y0 * z01) / ((1 - z00) * (1 - z11) - z01 * z10) := by
  constructor
  · rw [eq_div_iff hdet]
    linear_combination (1 - z11) * h0 + z10 * h1
  · rw [eq_div_iff hdet]
    linear_combination z01 * h0 + (1 - z00) * h1

/-- For a strongly connected automaton: `det (I - Z) ≠ 0` and `t` is the configuration's. -/
private theorem det_and_t {a b : S} (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    (A.configOf a b W.E x₁ x₂).det ≠ 0 ∧ ∀ i : Fin 2,
      A.alphaStat W.E (fun _ => 1 / 2) (![x₁, x₂] i) = ((A.configOf a b W.E x₁ x₂).t i : ℝ) := by
  set cf := A.configOf a b W.E x₁ x₂ with hcf
  set p : S → ℝ := fun _ => 1 / 2 with hp
  set e := xEquiv A W hX h12 with he
  set Mx := 1 - A.Zmat W.E p with hMx
  have hU : IsUnit Mx := (half_stat A hab hS hsc W).1
  have hZ : ∀ i j : Fin 2, A.Zmat W.E p (e i) (e j) = (cf.Z i j : ℝ) := fun i j => Z_entry A hab hS W.E h12 i j
  have hne : e 0 ≠ e 1 := fun h => absurd (e.injective h) (by decide)
  have hM00 : Mx (e 0) (e 0) = 1 - (cf.Z 0 0 : ℝ) := by
    rw [hMx, Matrix.sub_apply, Matrix.one_apply_eq, hZ]
  have hM11 : Mx (e 1) (e 1) = 1 - (cf.Z 1 1 : ℝ) := by
    rw [hMx, Matrix.sub_apply, Matrix.one_apply_eq, hZ]
  have hM01 : Mx (e 0) (e 1) = 0 - (cf.Z 0 1 : ℝ) := by
    rw [hMx, Matrix.sub_apply, Matrix.one_apply_ne hne, hZ]
  have hM10 : Mx (e 1) (e 0) = 0 - (cf.Z 1 0 : ℝ) := by
    rw [hMx, Matrix.sub_apply, Matrix.one_apply_ne (Ne.symm hne), hZ]
  -- the determinant
  have hdetM : Mx.det = (cf.det : ℝ) := by
    rw [← Matrix.det_submatrix_equiv_self e Mx, Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, hM00, hM11, hM01, hM10, Config.det]
    push_cast
    ring
  have hdet : (cf.det : ℝ) ≠ 0 := by
    rw [← hdetM]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero
  -- the linear system `t (I - Z) = y`
  set t := A.tvec W.E p with ht
  have hsys : vecMul t Mx = A.yvec W.E p := by
    rw [ht, Automaton.tvec, Matrix.vecMul_vecMul,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.vecMul_one]
  have hrow : ∀ j : Fin 2, t (e 0) * Mx (e 0) (e j) + t (e 1) * Mx (e 1) (e j) = (cf.y j : ℝ) := by
    intro j
    have h := congrFun hsys (e j)
    simp only [vecMul, dotProduct] at h
    rw [← e.sum_comp, Fin.sum_univ_two] at h
    rw [h]
    exact y_entry A hab hS W.E x₁ x₂ j
  have h0 := hrow 0
  have h1 := hrow 1
  rw [hM00, hM10] at h0
  rw [hM01, hM11] at h1
  have hdet' : (1 - (cf.Z 0 0 : ℝ)) * (1 - (cf.Z 1 1 : ℝ)) - (cf.Z 0 1 : ℝ) * (cf.Z 1 0 : ℝ) ≠ 0 := by
    have : (cf.det : ℝ) = (1 - (cf.Z 0 0 : ℝ)) * (1 - (cf.Z 1 1 : ℝ)) - (cf.Z 0 1 : ℝ) * (cf.Z 1 0 : ℝ) := by
      simp only [Config.det]
      push_cast
      ring
    rw [← this]
    exact hdet
  obtain ⟨ht0, ht1⟩ := cramer hdet' h0 h1
  have hal : ∀ i : Fin 2, A.alphaStat W.E p (![x₁, x₂] i) = t (e i) := by
    intro i
    rw [Automaton.alphaStat, dite_eq_left (memX A W hX i)]
    rfl
  refine ⟨fun h => hdet (by rw [h]; simp), fun i => ?_⟩
  rw [hal]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [ht0]
    simp only [Config.t, Config.det, Matrix.cons_val_zero]
    push_cast
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [ht1]
    simp only [Config.t, Config.det, Matrix.cons_val_one]
    push_cast
    ring

/-- Lemma 5.7(b), tex:688-691. -/
theorem lem_5_7_b_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    ((W.E ×ˢ ({a, b} : Finset S)).filter (fun e => A.step e.1 e.2 ∈ insert W.s W.X)).card = 2 ∧
      (∀ i j : Fin 2, A.zPair (fun _ => 1 / 2) (![x₁, x₂] i) (![x₁, x₂] j) =
        ((A.configOf a b W.E x₁ x₂).Z i j : ℝ)) ∧
      (∀ i : Fin 2, A.yIn W.E (fun _ => 1 / 2) (![x₁, x₂] i) = ((A.configOf a b W.E x₁ x₂).y i : ℝ)) ∧
      (A.configOf a b W.E x₁ x₂).nu1 + (A.configOf a b W.E x₁ x₂).nu2 ≤ 2 ∧
      (A.StronglyConnected → ∀ i : Fin 2,
        A.alphaStat W.E (fun _ => 1 / 2) (![x₁, x₂] i) = ((A.configOf a b W.E x₁ x₂).t i : ℝ)) := by
  refine ⟨?_, fun i j => Z_entry A hab hS W.E h12 i j, fun i => y_entry A hab hS W.E x₁ x₂ i,
    nu_le_two A hab hS W hX h12, fun hsc => (det_and_t A hab hS hsc W hX h12).2⟩
  rw [card_prod_filter A hab]
  exact boundary_two A hab hS W

/-- tex:713-714: `(ν₁, ν₂) = (0, 0)` makes `E` closed, so the automaton is not strongly connected. -/
theorem sec54_nu_ne_00_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (h0 : (A.configOf a b W.E x₁ x₂).nu1 = 0)
    (h0' : (A.configOf a b W.E x₁ x₂).nu2 = 0) : A.IsClosed W.E ∧ ¬ A.StronglyConnected := by
  have hnu : ∀ x : Q, A.nuOf a b W.E x = 0 → ∀ q ∈ W.E, ∀ c, A.step q c ≠ x := by
    intro x hx q hq c hqc
    simp only [Automaton.nuOf] at hx
    have ha : (W.E.filter (fun q => A.step q a = x)).card = 0 := by omega
    have hb : (W.E.filter (fun q => A.step q b = x)).card = 0 := by omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at ha hb
    rcases hS c with h | h
    · subst h
      exact ha hq hqc
    · subst h
      exact hb hq hqc
  have hcl : A.IsClosed W.E := by
    intro q hq c
    by_contra hc
    by_cases h1 : A.step q c = x₁
    · exact hnu x₁ h0 q hq c h1
    · by_cases h2 : A.step q c = x₂
      · exact hnu x₂ h0' q hq c h2
      · exact hc (mem_E_of_ne A W hX h1 h2)
  refine ⟨hcl, fun hsc => ?_⟩
  rcases hsc W.E hcl with h | h
  · have hs := W.s_mem
    rw [h] at hs
    exact Finset.notMem_empty _ hs
  · have hx := not_mem_E A W hX (show x₁ ∈ ({x₁, x₂} : Finset Q) by simp)
    rw [h] at hx
    exact hx (Finset.mem_univ _)

private theorem mem_choices' (c : Config) (h1 : c.nu1 + c.nu2 ≤ 2) (h2 : ¬ (c.nu1 = 0 ∧ c.nu2 = 0)) :
    c ∈ choices := by
  simp only [choices, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(c.x1a, c.x1b, c.x2a, c.x2b, ⟨c.nu1, by omega⟩, ⟨c.nu2, by omega⟩), ⟨h1, ?_⟩, rfl⟩
  rintro ⟨h1', h2'⟩
  exact h2 ⟨congrArg Fin.val h1', congrArg Fin.val h2'⟩

/-- tex:721-722: the configuration of a witness of degree two of a strongly connected binary automaton is valid. -/
theorem sec54_config_valid_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    A.configOf a b W.E x₁ x₂ ∈ choices ∧ (A.configOf a b W.E x₁ x₂).Valid := by
  obtain ⟨hdet, ht⟩ := det_and_t A hab hS hsc W hX h12
  have hpos := (half_stat A hab hS hsc W).2
  refine ⟨mem_choices' _ (nu_le_two A hab hS W hX h12) (fun h => ?_), hdet, ?_, ?_⟩
  · exact (sec54_nu_ne_00_proved A a b hab hS W x₁ x₂ hX h12 h.1 h.2).2 hsc
  · have h := hpos x₁
    have h' : A.alphaStat W.E (fun _ => (1 : ℝ) / 2) x₁ = ((A.configOf a b W.E x₁ x₂).t 0 : ℝ) := ht 0
    rw [h'] at h
    exact_mod_cast h
  · have h := hpos x₂
    have h' : A.alphaStat W.E (fun _ => (1 : ℝ) / 2) x₂ = ((A.configOf a b W.E x₁ x₂).t 1 : ℝ) := ht 1
    rw [h'] at h
    exact_mod_cast h

/-! ### Patterns (tex:769-787) -/

private theorem alphaStat_E' (E : Finset Q) (p : S → ℝ) {q : Q} (hq : q ∈ E) : A.alphaStat E p q = 1 := by
  have h : q ∉ Finset.univ \ E := fun h => (Finset.mem_sdiff.mp h).2 hq
  simp [Automaton.alphaStat, h]

/-- tex:769-771: `α(K) = |K| + g₁ e₁(K) + g₂ e₂(K)`. -/
theorem sec54_alpha_formula_proved (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (K : Finset Q) :
    wt (A.alphaStat W.E (fun _ => 1 / 2)) K = K.card + (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) * ein x₁ K +
      (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) * ein x₂ K := by
  set al := A.alphaStat W.E (fun _ => (1 : ℝ) / 2) with hal
  have hpt : ∀ q, al q = 1 + (al x₁ - 1) * (if q = x₁ then 1 else 0) + (al x₂ - 1) * (if q = x₂ then 1 else 0) := by
    intro q
    by_cases h1 : q = x₁
    · subst h1
      simp [h12]
    · by_cases h2 : q = x₂
      · subst h2
        simp [h1]
      · rw [ite_eq_right h1, ite_eq_right h2, mul_zero, mul_zero, add_zero, add_zero]
        exact alphaStat_E' A W.E _ (mem_E_of_ne A W hX h1 h2)
  rw [wt, Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp [ein]

omit [Fintype Q] [Fintype S] in
private theorem pattern_iff {x₁ x₂ s : Q} {K K' : Finset Q} (h : pattern x₁ x₂ s K = pattern x₁ x₂ s K') :
    (x₁ ∈ K ↔ x₁ ∈ K') ∧ (x₂ ∈ K ↔ x₂ ∈ K') ∧ (s ∈ K ↔ s ∈ K') := by
  simp only [pattern, Prod.mk.injEq, decide_eq_decide] at h
  exact h

omit [Fintype Q] [Fintype S] in
private theorem mem_iff_of_three {x₁ x₂ s y : Q} {K K' : Finset Q} (h : pattern x₁ x₂ s K = pattern x₁ x₂ s K')
    (hy : y ∈ insert s ({x₁, x₂} : Finset Q)) : (y ∈ K ↔ y ∈ K') := by
  obtain ⟨h1, h2, h3⟩ := pattern_iff h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> assumption

omit [Fintype S] in
private theorem ein_pre (x : Q) (K : Finset Q) (c : S) :
    ein x (A.pre K [c]) = if A.step x c ∈ K then 1 else 0 := by
  simp [ein]

private theorem step_three {d : ℕ} (W : QEWitness A d) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (c : S) {x : Q}
    (hx : x ∈ ({x₁, x₂} : Finset Q)) : A.step x c ∈ insert W.s ({x₁, x₂} : Finset Q) := by
  rw [← hX]
  exact step_X A W (not_mem_E A W hX hx) c

/-- tex:783-784: the change of `(e₁, e₂)` under a letter depends only on the pattern. -/
theorem sec54_change_depends_on_pattern_proved (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (c : S) (K K' : Finset Q) (hP : pattern x₁ x₂ W.s K = pattern x₁ x₂ W.s K') :
    (∀ x ∈ ({x₁, x₂} : Finset Q), (x ∈ A.pre K [c] ↔ A.step x c ∈ K) ∧ A.step x c ∈ insert W.s W.X) ∧
      ein x₁ (A.pre K [c]) - ein x₁ K = ein x₁ (A.pre K' [c]) - ein x₁ K' ∧
      ein x₂ (A.pre K [c]) - ein x₂ K = ein x₂ (A.pre K' [c]) - ein x₂ K' := by
  obtain ⟨h1, h2, -⟩ := pattern_iff hP
  have hT : ∀ x ∈ ({x₁, x₂} : Finset Q), (A.step x c ∈ K ↔ A.step x c ∈ K') :=
    fun x hx => mem_iff_of_three hP (step_three A W hX c hx)
  refine ⟨fun x hx => ⟨by simp, step_X A W (not_mem_E A W hX hx) c⟩, ?_, ?_⟩
  · simp only [ein, mem_pre, act_singleton, h1, hT x₁ (by simp)]
  · simp only [ein, mem_pre, act_singleton, h2, hT x₂ (by simp)]

/-- tex:786-787: aligned patterns are never good. -/
theorem sec54_aligned_not_good_proved (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (g₁ g₂ : ℝ) (P : Bool × Bool × Bool) (hP : Aligned P) : ¬ Good A x₁ x₂ W.s g₁ g₂ P := by
  rintro ⟨c, K, hK, hnot⟩
  apply hnot
  refine ⟨0, ?_⟩
  have hs1 := step_three A W hX c (show x₁ ∈ ({x₁, x₂} : Finset Q) by simp)
  have hs2 := step_three A W hX c (show x₂ ∈ ({x₁, x₂} : Finset Q) by simp)
  rcases hP with rfl | rfl
  · simp only [pattern, Prod.mk.injEq, decide_eq_true_eq] at hK
    obtain ⟨k1, k2, k3⟩ := hK
    have hsub : insert W.s ({x₁, x₂} : Finset Q) ⊆ K := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    simp [ein, k1, k2, hsub hs1, hsub hs2]
  · simp only [pattern, Prod.mk.injEq, decide_eq_false_iff_not] at hK
    obtain ⟨k1, k2, k3⟩ := hK
    have hdis : ∀ y ∈ insert W.s ({x₁, x₂} : Finset Q), y ∉ K := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    simp [ein, k1, k2, hdis _ hs1, hdis _ hs2]

omit [Fintype S] in
private theorem good_compl_imp (x₁ x₂ s : Q) (g₁ g₂ : ℝ) (P : Bool × Bool × Bool) :
    Good A x₁ x₂ s g₁ g₂ P → Good A x₁ x₂ s g₁ g₂ (!P.1, !P.2.1, !P.2.2) := by
  rintro ⟨c, K, hK, hnot⟩
  refine ⟨c, Kᶜ, ?_, ?_⟩
  · rw [← hK]
    simp [pattern]
  · rintro ⟨z, hz⟩
    apply hnot
    refine ⟨-z, ?_⟩
    have hc : ∀ x, ein x (A.pre Kᶜ [c]) = 1 - ein x (A.pre K [c]) := by
      intro x
      by_cases h : A.step x c ∈ K <;> simp [ein, h]
    have hc' : ∀ x, ein x Kᶜ = 1 - ein x K := by
      intro x
      by_cases h : x ∈ K <;> simp [ein, h]
    rw [hc, hc, hc', hc'] at hz
    push_cast
    linarith

/-- tex:802-803: a pattern is good iff the complementary pattern is. -/
theorem lem_5_10_compl_good_proved (x₁ x₂ s : Q) (g₁ g₂ : ℝ) (b₁ b₂ b₃ : Bool) :
    Good A x₁ x₂ s g₁ g₂ (b₁, b₂, b₃) ↔ Good A x₁ x₂ s g₁ g₂ (!b₁, !b₂, !b₃) := by
  constructor
  · exact good_compl_imp A x₁ x₂ s g₁ g₂ (b₁, b₂, b₃)
  · intro h
    have h' := good_compl_imp A x₁ x₂ s g₁ g₂ (!b₁, !b₂, !b₃) h
    simpa using h'

omit [Fintype S] in
private theorem exists_pattern {x₁ x₂ s : Q} (h12 : x₁ ≠ x₂) (h1s : x₁ ≠ s) (h2s : x₂ ≠ s)
    (P : Bool × Bool × Bool) : ∃ K : Finset Q, pattern x₁ x₂ s K = P := by
  obtain ⟨b₁, b₂, b₃⟩ := P
  refine ⟨Finset.univ.filter (fun q => (q = x₁ ∧ b₁ = true) ∨ (q = x₂ ∧ b₂ = true) ∨ (q = s ∧ b₃ = true)), ?_⟩
  simp [pattern, h12, h12.symm, h1s, h2s, h1s.symm, h2s.symm]

private theorem good_all (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (g₁ g₂ : ℝ) (P : Bool × Bool × Bool) (hG : Good A x₁ x₂ W.s g₁ g₂ P) :
    ∃ c : S, ∀ K : Finset Q, pattern x₁ x₂ W.s K = P → ¬ ∃ z : ℤ,
      g₁ * (ein x₁ (A.pre K [c]) - ein x₁ K) + g₂ * (ein x₂ (A.pre K [c]) - ein x₂ K) = z := by
  obtain ⟨c, K₀, hK₀, hnot⟩ := hG
  refine ⟨c, fun K hK => ?_⟩
  obtain ⟨-, e1, e2⟩ := sec54_change_depends_on_pattern_proved A W x₁ x₂ hX h12 c K K₀ (hK.trans hK₀.symm)
  rw [e1, e2]
  exact hnot

/-- A letter that changes `g₁ e₁ + g₂ e₂` by a non-integer changes `α`. -/
private theorem wt_ne_of_not_int (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (K : Finset Q) (c : S)
    (h : ¬ ∃ z : ℤ, (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) * (ein x₁ (A.pre K [c]) - ein x₁ K) +
      (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) * (ein x₂ (A.pre K [c]) - ein x₂ K) = z) :
    wt (A.alphaStat W.E (fun _ => 1 / 2)) (A.pre K [c]) ≠ wt (A.alphaStat W.E (fun _ => 1 / 2)) K := by
  intro heq
  apply h
  refine ⟨(K.card : ℤ) - ((A.pre K [c]).card : ℤ), ?_⟩
  rw [sec54_alpha_formula_proved A W x₁ x₂ hX h12, sec54_alpha_formula_proved A W x₁ x₂ hX h12] at heq
  push_cast
  linarith

/-- tex:784-786: "some (equivalently, every) set K with this pattern", and a good pattern gives `m(K) = 1`. -/
theorem sec54_good_cost1_proved (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (P : Bool × Bool × Bool) :
    (Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P ↔
      ∃ c : S, ∀ K : Finset Q, pattern x₁ x₂ W.s K = P → ¬ ∃ z : ℤ,
        (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) * (ein x₁ (A.pre K [c]) - ein x₁ K) +
          (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) * (ein x₂ (A.pre K [c]) - ein x₂ K) = z) ∧
      (Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P →
        ∀ K : Finset Q, pattern x₁ x₂ W.s K = P → A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K = 1) := by
  have h1s : x₁ ≠ W.s := fun h => not_mem_E A W hX (show x₁ ∈ ({x₁, x₂} : Finset Q) by simp) (h ▸ W.s_mem)
  have h2s : x₂ ≠ W.s := fun h => not_mem_E A W hX (show x₂ ∈ ({x₁, x₂} : Finset Q) by simp) (h ▸ W.s_mem)
  refine ⟨⟨good_all A W hX h12 _ _ P, fun ⟨c, hc⟩ => ?_⟩, fun hG K hK => ?_⟩
  · obtain ⟨K, hK⟩ := exists_pattern h12 h1s h2s P
    exact ⟨c, K, hK, hc K hK⟩
  · obtain ⟨c, hc⟩ := good_all A W hX h12 _ _ P hG
    have hne := wt_ne_of_not_int A W hX h12 K c (hc K hK)
    refine le_antisymm ?_ (A.one_le_cost _ K)
    have h : A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ (([c] : List S).length : ℕ∞) :=
      minLen_le_length (P := fun w => wt (A.alphaStat W.E (fun _ => 1 / 2)) (A.pre K w) ≠
        wt (A.alphaStat W.E (fun _ => 1 / 2)) K) hne
    simpa using h

/-! ### The joint orbit (Lemma 5.10, tex:790-803) -/

/-- The states `q.w` with `q ∈ T` and `|w| ≤ j`. -/
private noncomputable def jreach (T : Finset Q) (j : ℕ) : Finset Q :=
  Finset.univ.filter (fun q => ∃ y ∈ T, ∃ w : List S, w.length ≤ j ∧ A.act y w = q)

omit [DecidableEq Q] [Fintype S] in
private theorem mem_jreach {T : Finset Q} {j : ℕ} {q : Q} :
    q ∈ jreach A T j ↔ ∃ y ∈ T, ∃ w : List S, w.length ≤ j ∧ A.act y w = q := by
  simp [jreach]

omit [DecidableEq Q] [Fintype S] in
private theorem jreach_mono (T : Finset Q) (j : ℕ) : jreach A T j ⊆ jreach A T (j + 1) := by
  intro q hq
  obtain ⟨y, hy, w, hw, rfl⟩ := (mem_jreach A).mp hq
  exact (mem_jreach A).mpr ⟨y, hy, w, by omega, rfl⟩

omit [DecidableEq Q] [Fintype S] in
private theorem jreach_closed (T : Finset Q) (j : ℕ) (h : jreach A T j = jreach A T (j + 1)) :
    A.IsClosed (jreach A T j) := by
  intro q hq c
  obtain ⟨y, hy, w, hw, rfl⟩ := (mem_jreach A).mp hq
  rw [h]
  exact (mem_jreach A).mpr ⟨y, hy, w ++ [c], by simp; omega, by rw [act_concat]⟩

omit [DecidableEq Q] [Fintype S] in
private theorem T_sub_jreach (T : Finset Q) (j : ℕ) : T ⊆ jreach A T j := by
  intro y hy
  exact (mem_jreach A).mpr ⟨y, hy, [], by simp, rfl⟩

omit [Fintype Q] [Fintype S] in
private theorem card_three {x₁ x₂ s : Q} (h12 : x₁ ≠ x₂) (h1s : x₁ ≠ s) (h2s : x₂ ≠ s) :
    (insert s ({x₁, x₂} : Finset Q)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [h1s.symm, h2s.symm]), Finset.card_pair h12]

/-- The orbit facts for the pattern `(1,1,1)`: the exceptional states stay in `K` for `|w| ≤ esc_s(K)`. -/
private theorem stay_in (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) (K : Finset Q)
    (hK : insert W.s ({x₁, x₂} : Finset Q) ⊆ K) :
    (∀ w : List S, (w.length : ℕ∞) < A.esc W.s K → A.act W.s w ∈ K) ∧
      ∀ w : List S, ∀ x ∈ ({x₁, x₂} : Finset Q), (w.length : ℕ∞) ≤ A.esc W.s K → A.act x w ∈ K := by
  have hsK : W.s ∈ K := hK (Finset.mem_insert_self _ _)
  have hs : ∀ w : List S, (w.length : ℕ∞) < A.esc W.s K → A.act W.s w ∈ K := by
    intro w hw
    have h := not_of_lt_minLen (P := A.MovesAcross W.s K) hw
    rw [A.movesAcross_iff, not_not] at h
    exact h.mpr hsK
  refine ⟨hs, fun w => ?_⟩
  induction w with
  | nil => intro x hx _; exact hK (Finset.mem_insert_of_mem hx)
  | cons c w ih =>
    intro x hx hlen
    rw [act_cons]
    have hlt : (w.length : ℕ∞) < ((c :: w).length : ℕ∞) := by
      exact_mod_cast (show w.length < (c :: w).length by simp)
    have hy := step_three A W hX c hx
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]
      exact hs w (lt_of_lt_of_le hlt hlen)
    · exact ih _ h (le_trans hlt.le hlen)

/-- The chain of the joint orbit is strict while it stays in `K`. -/
private theorem chain_card (hsc : A.StronglyConnected) (W : QEWitness A 2) {x₁ x₂ : Q} (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (K : Finset Q) (hprop : K ≠ Finset.univ) (hK : insert W.s ({x₁, x₂} : Finset Q) ⊆ K) :
    ∀ j : ℕ, (j : ℕ∞) < A.esc W.s K →
      jreach A (insert W.s ({x₁, x₂} : Finset Q)) j ⊆ K ∧ j + 3 ≤ (jreach A (insert W.s ({x₁, x₂} : Finset Q)) j).card := by
  have h1s : x₁ ≠ W.s := fun h => not_mem_E A W hX (show x₁ ∈ ({x₁, x₂} : Finset Q) by simp) (h ▸ W.s_mem)
  have h2s : x₂ ≠ W.s := fun h => not_mem_E A W hX (show x₂ ∈ ({x₁, x₂} : Finset Q) by simp) (h ▸ W.s_mem)
  set T := insert W.s ({x₁, x₂} : Finset Q) with hT
  obtain ⟨hs, hx⟩ := stay_in A W hX K hK
  have hsub : ∀ j : ℕ, (j : ℕ∞) < A.esc W.s K → jreach A T j ⊆ K := by
    intro j hj q hq
    obtain ⟨y, hy, w, hw, rfl⟩ := (mem_jreach A).mp hq
    have hwj : (w.length : ℕ∞) < A.esc W.s K := lt_of_le_of_lt (by exact_mod_cast hw) hj
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]
      exact hs w hwj
    · exact hx w y h hwj.le
  intro j
  induction j with
  | zero =>
    intro hj
    refine ⟨hsub 0 hj, ?_⟩
    have h := Finset.card_le_card (T_sub_jreach A T 0)
    rw [hT, card_three h12 h1s h2s] at h
    omega
  | succ j ih =>
    intro hj
    have hj' : (j : ℕ∞) < A.esc W.s K := lt_of_le_of_lt (by exact_mod_cast (Nat.le_succ j)) hj
    obtain ⟨hsubj, hcard⟩ := ih hj'
    refine ⟨hsub (j + 1) hj, ?_⟩
    have hne : jreach A T j ≠ jreach A T (j + 1) := by
      intro heq
      have hcl := jreach_closed A T j heq
      rcases hsc _ hcl with h | h
      · have hs' : W.s ∈ jreach A T j := T_sub_jreach A T j (Finset.mem_insert_self _ _)
        rw [h] at hs'
        exact Finset.notMem_empty _ hs'
      · exact hprop (Finset.eq_univ_of_forall fun q => hsubj (h ▸ Finset.mem_univ q))
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨jreach_mono A T j, hne⟩)
    omega

/-- Lemma 5.10 (joint orbit), tex:790-791, the pattern `(1,1,1)`. -/
theorem lem_5_10_a_proved (hsc : A.StronglyConnected) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ)
    (hP : pattern x₁ x₂ W.s K = (true, true, true)) :
    A.esc W.s K ≤ ((K.card - 2 : ℕ) : ℕ∞) ∧
      (∀ w : List S, (w.length : ℕ∞) ≤ A.esc W.s K → A.act x₁ w ∈ K ∧ A.act x₂ w ∈ K) ∧
      (Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1)
          (true, true, false) →
        A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ ((K.card - 1 : ℕ) : ℕ∞)) := by
  have h1s : x₁ ≠ W.s := fun h => not_mem_E A W hX (show x₁ ∈ ({x₁, x₂} : Finset Q) by simp) (h ▸ W.s_mem)
  have h2s : x₂ ≠ W.s := fun h => not_mem_E A W hX (show x₂ ∈ ({x₁, x₂} : Finset Q) by simp) (h ▸ W.s_mem)
  simp only [pattern, Prod.mk.injEq, decide_eq_true_eq] at hP
  obtain ⟨k1, k2, k3⟩ := hP
  have hK : insert W.s ({x₁, x₂} : Finset Q) ⊆ K := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hk3 : 3 ≤ K.card := by
    have h := Finset.card_le_card hK
    rwa [card_three h12 h1s h2s] at h
  obtain ⟨hs, hx⟩ := stay_in A W hX K hK
  -- part 1: `esc_s(K) ≤ k - 2`
  have hesc : A.esc W.s K ≤ ((K.card - 2 : ℕ) : ℕ∞) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hsub, hcard⟩ := chain_card A hsc W hX h12 K hprop hK (K.card - 2) hlt
    have h := Finset.card_le_card hsub
    omega
  refine ⟨hesc, fun w hw => ⟨hx w x₁ (by simp) hw, hx w x₂ (by simp) hw⟩, fun hG => ?_⟩
  -- part 3: a good pattern `(1,1,0)` gives `m(K) ≤ k - 1`
  have hfin : A.esc W.s K ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hesc
  obtain ⟨w, hmov, hwlen⟩ := exists_of_minLen_ne_top (P := A.MovesAcross W.s K) hfin
  have hwle : w.length ≤ K.card - 2 := by
    have h : (w.length : ℕ∞) ≤ ((K.card - 2 : ℕ) : ℕ∞) := by
      rw [show (w.length : ℕ∞) = A.esc W.s K from hwlen]
      exact hesc
    exact_mod_cast h
  have hout : A.act W.s w ∉ K := by
    rw [A.movesAcross_iff] at hmov
    intro h
    exact hmov ⟨fun _ => k3, fun _ => h⟩
  have hwle' : (w.length : ℕ∞) ≤ A.esc W.s K := le_of_eq hwlen
  have hpat : pattern x₁ x₂ W.s (A.pre K w) = (true, true, false) := by
    simp only [pattern, mem_pre, hx w x₁ (by simp) hwle', hx w x₂ (by simp) hwle', hout, decide_true,
      decide_false]
  obtain ⟨c, hc⟩ := good_all A W hX h12 _ _ _ hG
  have hc' := wt_ne_of_not_int A W hX h12 (A.pre K w) c (hc _ hpat)
  set al := A.alphaStat W.E (fun _ => (1 : ℝ) / 2) with hal
  have hcw : A.pre (A.pre K w) [c] = A.pre K (c :: w) := by
    rw [← pre_append]
    rfl
  by_cases hw : wt al (A.pre K w) = wt al K
  · have h := minLen_le_length (P := fun v => wt al (A.pre K v) ≠ wt al K) (w := c :: w)
      (by rw [← hcw, ← hw]; exact hc')
    refine le_trans h ?_
    simp only [List.length_cons]
    exact_mod_cast (show w.length + 1 ≤ K.card - 1 by omega)
  · have h := minLen_le_length (P := fun v => wt al (A.pre K v) ≠ wt al K) (w := w) hw
    refine le_trans h ?_
    exact_mod_cast (show w.length ≤ K.card - 1 by omega)

omit [Fintype S] in
private theorem esc_compl (x : Q) (K : Finset Q) : A.esc x Kᶜ = A.esc x K := by
  unfold Automaton.esc
  congr 1
  funext w
  apply propext
  rw [A.movesAcross_iff, A.movesAcross_iff, Finset.mem_compl, Finset.mem_compl]
  tauto

omit [Fintype S] in
private theorem cost_compl (β : Q → ℝ) (K : Finset Q) : A.cost β Kᶜ = A.cost β K := by
  unfold Automaton.cost
  congr 1
  funext w
  apply propext
  have h1 : A.pre Kᶜ w = (A.pre K w)ᶜ := by
    ext q
    simp
  have h2 : ∀ L : Finset Q, wt β Lᶜ = wt β Finset.univ - wt β L := by
    intro L
    unfold wt
    rw [← Finset.sum_compl_add_sum L]
    ring
  rw [h1, h2, h2]
  constructor
  · intro h hh
    exact h (by linarith)
  · intro h hh
    exact h (by linarith)

/-- Lemma 5.10, tex:791-792, the pattern `(0,0,0)`. -/
theorem lem_5_10_b_proved (hsc : A.StronglyConnected) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ)
    (hP : pattern x₁ x₂ W.s K = (false, false, false)) :
    A.esc W.s K ≤ ((Fintype.card Q - K.card - 2 : ℕ) : ℕ∞) ∧
      (Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1)
          (false, false, true) →
        A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ ((Fintype.card Q - K.card - 1 : ℕ) : ℕ∞)) := by
  have hne' : Kᶜ.Nonempty := by
    obtain ⟨q, hq⟩ : ∃ q, q ∉ K := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hprop (Finset.eq_univ_of_forall h)
    exact ⟨q, Finset.mem_compl.mpr hq⟩
  have hprop' : Kᶜ ≠ Finset.univ := fun h => hne.ne_empty ((Finset.compl_eq_univ_iff K).mp h)
  have hP' : pattern x₁ x₂ W.s Kᶜ = (true, true, true) := by
    have h : pattern x₁ x₂ W.s Kᶜ = (!(pattern x₁ x₂ W.s K).1, !(pattern x₁ x₂ W.s K).2.1,
        !(pattern x₁ x₂ W.s K).2.2) := by
      simp [pattern]
    rw [h, hP]
    rfl
  obtain ⟨hesc, -, hcost⟩ := lem_5_10_a_proved A hsc W x₁ x₂ hX h12 Kᶜ hne' hprop' hP'
  rw [esc_compl, Finset.card_compl] at hesc
  refine ⟨hesc, fun hG => ?_⟩
  have hG' := good_compl_imp A x₁ x₂ W.s _ _ _ hG
  have h := hcost hG'
  rw [cost_compl, Finset.card_compl] at h
  exact h

end Binary

end CernyQE
