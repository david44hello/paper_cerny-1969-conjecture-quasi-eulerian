/-
CernyQE/Proofs/ImageSearch.lean — a verified image-set search for reset words, and the soundness of the census checks.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Automaton
import CernyQE.Proofs.Census514.Search
import Mathlib

/-!
Part 1 (any automaton): `imgs A k` is the set of images `Q.w` of the words `w` of length at most `k`; it is computed by
one-letter steps, and `A.rt ≤ k ↔ ∃ T ∈ imgs A k, |T| = 1`. So `rt = k + 1` exactly when this holds at `k + 1` and
fails at `k`; for a concrete automaton both are decidable.

Part 2 (tables): the automaton `tabAut n tbl` of a table, and the soundness of the checks of `Census514/Search.lean`:
a checked reset word is a reset word, a checked pair certificate excludes synchronization, and `allSeq` covers every
edge assignment with the prescribed in-degrees (also when it is split into chunks).
-/

namespace CernyQE

open Finset

namespace ImageSearch

/-! ### Least lengths -/

section MinLen

variable {S : Type*} {P : List S → Prop}

private theorem minLen_le_of {w : List S} (h : P w) : minLen P ≤ w.length := iInf₂_le w h

private theorem minLen_le_nat {k : ℕ} : minLen P ≤ k ↔ ∃ w, P w ∧ w.length ≤ k := by
  constructor
  · intro h
    by_contra hne
    have hlt : ∀ w, P w → k < w.length := fun w hw => by
      by_contra h'
      exact hne ⟨w, hw, by omega⟩
    have h1 : ((k + 1 : ℕ) : ℕ∞) ≤ minLen P :=
      le_iInf₂ (fun w hw => by exact_mod_cast hlt w hw)
    have h2 := h1.trans h
    exact absurd h2 (by exact_mod_cast Nat.not_succ_le_self k)
  · rintro ⟨w, hw, hk⟩
    exact (minLen_le_of hw).trans (by exact_mod_cast hk)

end MinLen

/-! ### Part 1: the images of the words of length at most `k` -/

section Generic

variable {Q : Type*} {S : Type*} [Fintype Q] [DecidableEq Q] [Fintype S]

omit [Fintype Q] [DecidableEq Q] [Fintype S] in
theorem act_append (A : Automaton Q S) (q : Q) (u w : List S) : A.act q (u ++ w) = A.act (A.act q u) w := by
  simp only [Automaton.act, List.foldl_append]

omit [Fintype Q] [Fintype S] in
theorem img_img (A : Automaton Q S) (K : Finset Q) (u w : List S) : A.img (A.img K u) w = A.img K (u ++ w) := by
  simp only [Automaton.img, Finset.image_image]
  congr 1
  funext q
  simp only [Function.comp, act_append]

omit [Fintype Q] [Fintype S] in
theorem img_nil (A : Automaton Q S) (K : Finset Q) : A.img K [] = K := by
  simp only [Automaton.img, Automaton.act, List.foldl_nil, Finset.image_id']

/-- The images `Q.w` of the words `w` of length at most `k`: `{Q}`, then one more letter at each step. -/
def imgs (A : Automaton Q S) : ℕ → Finset (Finset Q)
  | 0 => {univ}
  | k + 1 => let L := imgs A k; L ∪ L.biUnion (fun T => univ.image (fun c => A.img T [c]))

theorem mem_imgs (A : Automaton Q S) :
    ∀ (k : ℕ) (T : Finset Q), T ∈ imgs A k ↔ ∃ w : List S, w.length ≤ k ∧ T = A.img univ w
  | 0, T => by
    simp only [imgs, Finset.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨[], rfl, (img_nil A univ).symm⟩
    · rintro ⟨w, rfl, rfl⟩
      exact img_nil A univ
  | k + 1, T => by
    simp only [imgs, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and,
      mem_imgs A k]
    constructor
    · rintro (⟨w, hw, rfl⟩ | ⟨T', ⟨w, hw, rfl⟩, c, rfl⟩)
      · exact ⟨w, by omega, rfl⟩
      · exact ⟨w ++ [c], by simp only [List.length_append, List.length_singleton]; omega, img_img A _ _ _⟩
    · rintro ⟨w, hw, rfl⟩
      rcases Nat.lt_or_ge w.length (k + 1) with h | h
      · exact Or.inl ⟨w, by omega, rfl⟩
      · right
        have hne : w ≠ [] := by
          rintro rfl
          simp at h
        refine ⟨A.img univ w.dropLast, ⟨w.dropLast, by simp only [List.length_dropLast]; omega, rfl⟩,
          w.getLast hne, ?_⟩
        rw [img_img, List.dropLast_append_getLast hne]

omit [Fintype S] in
theorem isReset_iff_card [Nonempty Q] (A : Automaton Q S) (w : List S) :
    A.IsReset w ↔ (A.img univ w).card = 1 := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    ext x
    simp only [Automaton.img, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton, hr]
    exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨Classical.arbitrary Q, h.symm⟩⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, fun q => ?_⟩
    have h : A.act q w ∈ A.img univ w := Finset.mem_image_of_mem _ (Finset.mem_univ q)
    rw [hr] at h
    exact Finset.mem_singleton.1 h

/-- `rt ≤ k` iff some image of a word of length at most `k` is a singleton. -/
theorem rt_le_iff [Nonempty Q] (A : Automaton Q S) (k : ℕ) :
    A.rt ≤ k ↔ ∃ T ∈ imgs A k, T.card = 1 := by
  unfold Automaton.rt
  rw [minLen_le_nat]
  constructor
  · rintro ⟨w, hw, hk⟩
    exact ⟨A.img univ w, (mem_imgs A k _).2 ⟨w, hk, rfl⟩, (isReset_iff_card A w).1 hw⟩
  · rintro ⟨T, hT, hc⟩
    obtain ⟨w, hk, rfl⟩ := (mem_imgs A k T).1 hT
    exact ⟨w, (isReset_iff_card A w).2 hc, hk⟩

/-- `rt = k + 1` exactly: true at `k + 1`, false at `k`. -/
theorem rt_eq_succ [Nonempty Q] (A : Automaton Q S) (k : ℕ) (h1 : ∃ T ∈ imgs A (k + 1), T.card = 1)
    (h2 : ∀ T ∈ imgs A k, T.card ≠ 1) : A.rt = ((k + 1 : ℕ) : ℕ∞) := by
  have hle := (rt_le_iff A (k + 1)).2 h1
  have hnot : ¬ A.rt ≤ k := fun h => by
    obtain ⟨T, hT, hc⟩ := (rt_le_iff A k).1 h
    exact h2 T hT hc
  have hlt : (k : ℕ∞) < A.rt := not_le.1 hnot
  refine le_antisymm hle ?_
  have h3 : (k : ℕ∞) + 1 ≤ A.rt := Order.add_one_le_of_lt hlt
  exact_mod_cast h3

/-- A singleton image gives a reset word. -/
theorem sync_of_imgs [Nonempty Q] (A : Automaton Q S) (k : ℕ) (h : ∃ T ∈ imgs A k, T.card = 1) :
    A.Synchronizing := by
  obtain ⟨T, hT, hc⟩ := h
  obtain ⟨w, -, rfl⟩ := (mem_imgs A k T).1 hT
  exact ⟨w, (isReset_iff_card A w).2 hc⟩

end Generic

/-! ### Part 2: tables -/

open Census514

section Tables

variable (n : ℕ) [NeZero n]

/-- The automaton of a table: `q.c` is entry `c n + q`, reduced mod `n`. -/
def tabAut (tbl : List ℕ) : Automaton (Fin n) (Fin 2) :=
  ⟨fun q c => ⟨stp n tbl q.val c.val, Nat.mod_lt _ (NeZero.pos n)⟩⟩

theorem tabAut_step_val (tbl : List ℕ) (q : Fin n) (c : Fin 2) :
    ((tabAut n tbl).step q c).val = stp n tbl q.val c.val := rfl

theorem tabAut_act_val (tbl : List ℕ) :
    ∀ (w : List (Fin 2)) (q : Fin n), ((tabAut n tbl).act q w).val = run n tbl q.val w
  | [], _ => rfl
  | c :: w, q => tabAut_act_val tbl w ((tabAut n tbl).step q c)

/-- A checked reset word is a reset word. -/
theorem isResetB_sound (tbl : List ℕ) (w : List (Fin 2)) (h : isResetB n tbl w = true) :
    (tabAut n tbl).IsReset w := by
  refine ⟨(tabAut n tbl).act ⟨0, NeZero.pos n⟩ w, fun q => Fin.ext ?_⟩
  rw [tabAut_act_val, tabAut_act_val]
  unfold isResetB at h
  rw [List.all_eq_true] at h
  exact Nat.eq_of_beq_eq_true (h q.val (List.mem_range.2 q.isLt))

theorem memP_sound : ∀ (P : List (ℕ × ℕ)) (p q : ℕ), memP P p q = true → (p, q) ∈ P
  | [], _, _, h => by simp [memP] at h
  | x :: rest, p, q, h => by
    simp only [memP, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · have e1 := Nat.eq_of_beq_eq_true h1
      have e2 := Nat.eq_of_beq_eq_true h2
      rw [← e1, ← e2]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memP_sound rest p q h)

omit [NeZero n] in
theorem pairOK_spec (tbl : List ℕ) (P : List (ℕ × ℕ)) (pq : ℕ × ℕ) (h : pairOK n tbl P pq = true) :
    pq.1 ≠ pq.2 ∧ pq.1 < n ∧ pq.2 < n ∧ (stp n tbl pq.1 0, stp n tbl pq.2 0) ∈ P ∧
      (stp n tbl pq.1 1, stp n tbl pq.2 1) ∈ P := by
  unfold pairOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, memP_sound _ _ _ h4, memP_sound _ _ _ h5⟩
  · intro he
    rw [he] at h1
    simp [Nat.beq_refl] at h1
  · simpa [Nat.blt_eq] using h2
  · simpa [Nat.blt_eq] using h3

/-- A checked pair certificate excludes reset words. -/
theorem nonSyncB_sound (tbl : List ℕ) (P : List (ℕ × ℕ)) (h : nonSyncB n tbl P = true) :
    ¬ (tabAut n tbl).Synchronizing := by
  unfold nonSyncB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at h
  obtain ⟨hne, hall⟩ := h
  obtain ⟨pq, hpq⟩ := List.exists_mem_of_ne_nil P hne
  have key : ∀ (w : List (Fin 2)) (x : ℕ × ℕ), x ∈ P → (run n tbl x.1 w, run n tbl x.2 w) ∈ P := by
    intro w
    induction w with
    | nil => intro x hx; exact hx
    | cons c w ih =>
      intro x hx
      obtain ⟨-, -, -, h0, h1⟩ := pairOK_spec n tbl P x (hall x hx)
      have hc : (stp n tbl x.1 c.val, stp n tbl x.2 c.val) ∈ P := by
        rcases c with ⟨_ | _ | c, hc⟩
        · exact h0
        · exact h1
        · omega
      exact ih _ hc
  rintro ⟨w, r, hr⟩
  obtain ⟨-, hp1, hp2, -, -⟩ := pairOK_spec n tbl P pq (hall pq hpq)
  obtain ⟨hne', -, -, -, -⟩ := pairOK_spec n tbl P _ (hall _ (key w pq hpq))
  apply hne'
  have e1 := tabAut_act_val n tbl w ⟨pq.1, hp1⟩
  have e2 := tabAut_act_val n tbl w ⟨pq.2, hp2⟩
  rw [hr] at e1 e2
  exact e1.symm.trans e2

/-- A member that passes the check has a reset word of length at most `M`, if it is synchronizing. -/
theorem memberOK_sound (M : ℕ) (tbl : List ℕ) (h : memberOK n M tbl = true)
    (hs : (tabAut n tbl).Synchronizing) : ∃ w, (tabAut n tbl).IsReset w ∧ w.length ≤ M := by
  unfold memberOK at h
  split at h
  · rename_i w _
    simp only [Bool.and_eq_true] at h
    exact ⟨w, isResetB_sound n tbl w h.2, Nat.le_of_ble_eq_true h.1⟩
  · exact absurd hs (nonSyncB_sound n tbl _ h)

end Tables

/-! ### The enumeration -/

section Enumeration

theorem getD_set_self : ∀ (l : List ℕ) (i x : ℕ), i < l.length → (l.set i x).getD i 0 = x
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => rfl
  | _ :: l, i + 1, x, h => getD_set_self l i x (by simpa using h)

theorem getD_set_ne : ∀ (l : List ℕ) (i j x : ℕ), i ≠ j → (l.set i x).getD j 0 = l.getD j 0
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: l, i + 1, j + 1, x, h => getD_set_ne l i j x (fun e => h (by rw [e]))

theorem lt_length_of_getD_pos : ∀ (l : List ℕ) (i : ℕ), 0 < l.getD i 0 → i < l.length
  | [], _, h => by simp at h
  | _ :: _, 0, _ => by simp
  | _ :: l, i + 1, h => by
    have := lt_length_of_getD_pos l i h
    simp only [List.length_cons]
    omega

variable (n : ℕ)

/-- `allSeq` covers every list with the right length, values and counts. -/
theorem allSeq_sound (leaf : List ℕ → Bool) :
    ∀ (k : ℕ) (cnt pre σ : List ℕ), allSeq n leaf k cnt pre = true → σ.length = k → (∀ v ∈ σ, v < n) →
      (∀ v, σ.count v ≤ cnt.getD v 0) → leaf (pre ++ σ) = true
  | 0, cnt, pre, σ, h, hl, _, _ => by
    rw [List.length_eq_zero_iff.1 hl, List.append_nil]
    exact h
  | k + 1, cnt, pre, σ, h, hl, hlt, hc => by
    obtain ⟨v, σ', rfl⟩ : ∃ v σ', σ = v :: σ' := by
      cases σ with
      | nil => simp at hl
      | cons v σ' => exact ⟨v, σ', rfl⟩
    have hv : v < n := hlt v List.mem_cons_self
    simp only [allSeq, List.all_eq_true, List.mem_range] at h
    have h1 := h v hv
    have hpos : 0 < cnt.getD v 0 := by
      have := hc v
      simp only [List.count_cons_self] at this
      omega
    have hb : Nat.beq (cnt.getD v 0) 0 = false := by
      cases hh : Nat.beq (cnt.getD v 0) 0
      · rfl
      · have := Nat.eq_of_beq_eq_true hh
        omega
    rw [hb, Bool.false_or] at h1
    have hrest := allSeq_sound leaf k _ _ σ' h1 (by simpa using hl)
      (fun u hu => hlt u (List.mem_cons_of_mem _ hu)) (fun u => ?_)
    · simpa using hrest
    · have hcu := hc u
      by_cases huv : v = u
      · subst huv
        rw [getD_set_self _ _ _ (lt_length_of_getD_pos _ _ hpos)]
        simp only [List.count_cons_self] at hcu
        omega
      · rw [getD_set_ne _ _ _ _ huv]
        have : σ'.count u ≤ (v :: σ').count u := List.count_le_count_cons
        omega

/-- The chunks together cover the whole enumeration. -/
theorem allSeq_of_chunks (M : ℕ) (t : List ℕ) (hn : 3 ≤ n)
    (h : ∀ v₁, v₁ < n → ∀ v₂, v₂ < n → chunk n M t v₁ v₂ = true) :
    allSeq n (leafOf n M t) (2 * (n - 2)) (cntOf n t) [] = true := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * (n - 2) = k + 1 + 1 := ⟨2 * (n - 2) - 2, by omega⟩
  have hk' : 2 * (n - 2) - 2 = k := by omega
  rw [hk]
  unfold allSeq
  rw [List.all_eq_true]
  intro v₁ hv₁
  have h₁ : v₁ < n := List.mem_range.1 hv₁
  cases hb : Nat.beq ((cntOf n t).getD v₁ 0) 0
  · rw [Bool.false_or]
    unfold allSeq
    rw [List.all_eq_true]
    intro v₂ hv₂
    have hc := h v₁ h₁ v₂ (List.mem_range.1 hv₂)
    unfold chunk at hc
    rw [hb, Bool.false_or, hk'] at hc
    exact hc
  · rfl

/-- Every edge assignment with the prescribed in-degrees passes the leaf check, given all chunks. -/
theorem leaf_of_chunks (M : ℕ) (t : List ℕ) (hn : 3 ≤ n)
    (h : ∀ v₁, v₁ < n → ∀ v₂, v₂ < n → chunk n M t v₁ v₂ = true) (σ : List ℕ) (hl : σ.length = 2 * (n - 2))
    (hlt : ∀ v ∈ σ, v < n) (hc : ∀ v, σ.count v ≤ (cntOf n t).getD v 0) :
    memberOK n M (tblOf n t σ) = true := by
  have := allSeq_sound n (leafOf n M t) _ _ [] σ (allSeq_of_chunks n M t hn h) hl hlt hc
  simpa [leafOf] using this

end Enumeration

end ImageSearch

end CernyQE
