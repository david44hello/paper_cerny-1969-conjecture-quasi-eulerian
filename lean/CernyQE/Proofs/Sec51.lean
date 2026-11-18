/-
CernyQE/Proofs/Sec51.lean — closed sets and the push lemma of Section 5.1, small automata, and arithmetic facts.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness

namespace CernyQE

open Classical Automaton Matrix

universe u v

set_option linter.unusedSectionVars false

/-! ### Private helpers: least lengths, words, closed sets -/

section Helpers

private theorem s51_minLen_le {S' : Type*} {P : List S' → Prop} {w : List S'} (h : P w) :
    minLen P ≤ w.length :=
  iInf₂_le w h

private theorem s51_le_minLen {S' : Type*} {P : List S' → Prop} {k : ℕ∞}
    (h : ∀ w, P w → k ≤ w.length) : k ≤ minLen P :=
  le_iInf₂ h

private theorem s51_exists_of_minLen_ne_top {S' : Type*} {P : List S' → Prop} (h : minLen P ≠ ⊤) :
    ∃ w, P w ∧ (w.length : ℕ∞) = minLen P := by
  have hex : ∃ w, P w := by
    by_contra hne
    push Not at hne
    apply h
    simp only [minLen, iInf_eq_top]
    intro w hw
    exact absurd hw (hne w)
  have hn : ∃ n, ∃ w, P w ∧ w.length = n := by
    obtain ⟨w, hw⟩ := hex
    exact ⟨_, w, hw, rfl⟩
  obtain ⟨w, hw, hwn⟩ := Nat.find_spec hn
  refine ⟨w, hw, le_antisymm ?_ (s51_minLen_le hw)⟩
  apply s51_le_minLen
  intro w' hw'
  rw [hwn]
  exact_mod_cast Nat.find_min' hn ⟨w', hw', rfl⟩

variable {Q : Type u} {S : Type v} (A : Automaton Q S)

private theorem s51_act_cons (q : Q) (b : S) (w : List S) : A.act q (b :: w) = A.act (A.step q b) w := rfl

private theorem s51_act_append (q : Q) (u w : List S) : A.act q (u ++ w) = A.act (A.act q u) w := by
  simp [Automaton.act, List.foldl_append]

/-- A closed set is closed under words. -/
private theorem s51_act_mem {K : Finset Q} (hK : A.IsClosed K) :
    ∀ (w : List S) (q : Q), q ∈ K → A.act q w ∈ K
  | [], _, hq => hq
  | b :: w, q, hq => s51_act_mem hK w (A.step q b) (hK q hq b)

/-- The state of a reset word lies in every nonempty closed set. -/
private theorem s51_reset_mem {K : Finset Q} (hK : A.IsClosed K) (hne : K.Nonempty) {w : List S} {r : Q}
    (hr : ∀ q, A.act q w = r) : r ∈ K := by
  obtain ⟨q, hq⟩ := hne
  rw [← hr q]
  exact s51_act_mem A hK w q hq

private theorem s51_not_disjoint [DecidableEq Q] (hA : A.Synchronizing) (C C' : Finset Q) (hne : C.Nonempty)
    (hne' : C'.Nonempty) (hC : A.IsClosed C) (hC' : A.IsClosed C') : ¬ Disjoint C C' := by
  obtain ⟨w, r, hr⟩ := hA
  exact Finset.not_disjoint_iff.mpr ⟨r, s51_reset_mem A hC hne hr, s51_reset_mem A hC' hne' hr⟩

private theorem s51_inter_closed [DecidableEq Q] (C C' : Finset Q) (hC : A.IsClosed C) (hC' : A.IsClosed C') :
    A.IsClosed (C ∩ C') := by
  intro q hq b
  rw [Finset.mem_inter] at hq ⊢
  exact ⟨hC q hq.1 b, hC' q hq.2 b⟩

private theorem s51_univ_closed [Fintype Q] : A.IsClosed (Finset.univ : Finset Q) :=
  fun _ _ _ => Finset.mem_univ _

/-- A minimal nonempty closed set lies in every nonempty closed set. -/
private theorem s51_min_subset [DecidableEq Q] (hA : A.Synchronizing) {C : Finset Q} (hmin : A.IsMinClosed C)
    {K : Finset Q} (hne : K.Nonempty) (hK : A.IsClosed K) : C ⊆ K := by
  have hI : (C ∩ K).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp
    (s51_not_disjoint A hA C K hmin.1 hne hmin.2.1 hK)
  have heq := hmin.2.2 (C ∩ K) hI (s51_inter_closed A C K hmin.2.1 hK) Finset.inter_subset_left
  rw [← heq]
  exact Finset.inter_subset_right

/-- A nonempty closed set of least cardinality is minimal and lies in every nonempty closed set. -/
private theorem s51_exists_least [Fintype Q] [DecidableEq Q] [Nonempty Q] (hA : A.Synchronizing) :
    ∃ C : Finset Q, A.IsMinClosed C ∧ ∀ C' : Finset Q, C'.Nonempty → A.IsClosed C' → C ⊆ C' := by
  let T : Finset (Finset Q) := Finset.univ.filter (fun C => C.Nonempty ∧ A.IsClosed C)
  have hT : T.Nonempty :=
    ⟨Finset.univ, by simp [T, Finset.univ_nonempty, s51_univ_closed A]⟩
  obtain ⟨C, hCT, hmin⟩ := Finset.exists_min_image T Finset.card hT
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hCT hmin
  have hleast : ∀ C' : Finset Q, C'.Nonempty → A.IsClosed C' → C ⊆ C' := by
    intro C' hne' hC'
    have hI : (C ∩ C').Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp
      (s51_not_disjoint A hA C C' hCT.1 hne' hCT.2 hC')
    have hcard := hmin (C ∩ C') ⟨hI, s51_inter_closed A C C' hCT.2 hC'⟩
    have heq : C ∩ C' = C := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
    rw [← heq]
    exact Finset.inter_subset_right
  exact ⟨C, ⟨hCT.1, hCT.2, fun C' hne' hC' hsub => Finset.Subset.antisymm hsub (hleast C' hne' hC')⟩, hleast⟩

/-- Words act on the restriction as on `A`. -/
private theorem s51_restrict_act (C : Finset Q) (hC : A.IsClosed C) :
    ∀ (w : List S) (x : C), ((A.restrict C hC).act x w).1 = A.act x.1 w
  | [], _ => rfl
  | b :: w, x => s51_restrict_act C hC w ((A.restrict C hC).step x b)

private theorem s51_restrict_sc (C : Finset Q) (hmin : A.IsMinClosed C) (hC : A.IsClosed C) :
    (A.restrict C hC).StronglyConnected := by
  intro K hK
  rcases K.eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · right
    let K' : Finset Q := K.map (Function.Embedding.subtype (· ∈ C))
    have hK'ne : K'.Nonempty := Finset.map_nonempty.mpr h
    have hK'sub : K' ⊆ C := by
      intro q hq
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hq
      exact x.2
    have hK'cl : A.IsClosed K' := by
      intro q hq b
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hq
      exact Finset.mem_map.mpr ⟨(A.restrict C hC).step x b, hK x hx b, rfl⟩
    have heq : K' = C := hmin.2.2 K' hK'ne hK'cl hK'sub
    refine Finset.eq_univ_of_forall (fun x => ?_)
    have hx : x.1 ∈ K' := by rw [heq]; exact x.2
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy

private theorem s51_restrict_sync (hA : A.Synchronizing) (C : Finset Q) (hne : C.Nonempty) (hC : A.IsClosed C) :
    (A.restrict C hC).Synchronizing := by
  obtain ⟨w, r, hr⟩ := hA
  refine ⟨w, ⟨r, s51_reset_mem A hC hne hr⟩, fun x => Subtype.ext ?_⟩
  rw [s51_restrict_act A C hC w x, hr]

/-- Cutting the segment between two equal states of a path gives a shorter word with the same end. -/
private theorem s51_shortcut {P : Q → Prop} (q : Q) (w : List S) (hw : P (A.act q w)) {i j : ℕ} (hij : i < j)
    (hj : j < w.length) (heq : A.act q (w.take i) = A.act q (w.take j)) :
    ∃ w' : List S, w'.length < w.length ∧ P (A.act q w') := by
  refine ⟨w.take i ++ w.drop j, ?_, ?_⟩
  · simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · rw [s51_act_append, heq, ← s51_act_append, List.take_append_drop]
    exact hw

/-- If a state reaches the closed set `C`, it reaches it by a word of length at most `|Q \ C|`. -/
private theorem s51_short_reach [Fintype Q] [DecidableEq Q] (C : Finset Q) (q : Q)
    (hreach : ∃ w, A.act q w ∈ C) :
    ∃ v : List S, v.length ≤ (Finset.univ \ C).card ∧ A.act q v ∈ C := by
  have hex : ∃ n, ∃ w : List S, w.length = n ∧ A.act q w ∈ C := by
    obtain ⟨w, hw⟩ := hreach
    exact ⟨_, w, rfl, hw⟩
  obtain ⟨w, hwlen, hw⟩ := Nat.find_spec hex
  refine ⟨w, ?_, hw⟩
  by_contra hlt
  push Not at hlt
  have hout : ∀ i ∈ Finset.range w.length, A.act q (w.take i) ∈ Finset.univ \ C := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hin
    have := Nat.find_min' hex ⟨w.take i, rfl, hin⟩
    rw [List.length_take] at this
    omega
  have hcard : (Finset.univ \ C).card < (Finset.range w.length).card := by
    rw [Finset.card_range]
    exact hlt
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hout
  rw [Finset.mem_range] at hi hj
  have key : ∀ i j, i < j → j < w.length → A.act q (w.take i) = A.act q (w.take j) → False := by
    intro i j hij hj heq
    obtain ⟨w', hw'len, hw'⟩ := s51_shortcut A (P := (· ∈ C)) q w hw hij hj heq
    have := Nat.find_min' hex ⟨w', rfl, hw'⟩
    omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hj heq
  · exact key j i h hi heq.symm

/-- The push: a set `T` with `|T \ C| ≤ m` is mapped into `C` by a word of length at most `m |Q \ C|`. -/
private theorem s51_push_aux [Fintype Q] [DecidableEq Q] (C : Finset Q) (hC : A.IsClosed C)
    (hreach : ∀ q, ∃ w, A.act q w ∈ C) :
    ∀ (m : ℕ) (T : Finset Q), (T \ C).card ≤ m →
      ∃ u : List S, u.length ≤ m * (Finset.univ \ C).card ∧ ∀ q ∈ T, A.act q u ∈ C := by
  intro m
  induction m with
  | zero =>
    intro T hT
    refine ⟨[], by simp, fun q hq => ?_⟩
    have hTC : T \ C = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT)
    rw [Finset.sdiff_eq_empty_iff_subset] at hTC
    exact hTC hq
  | succ m ih =>
    intro T hT
    by_cases hsub : T \ C = ∅
    · refine ⟨[], by simp, fun q hq => ?_⟩
      rw [Finset.sdiff_eq_empty_iff_subset] at hsub
      exact hsub hq
    · obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hsub
      obtain ⟨v, hvlen, hv⟩ := s51_short_reach A C q₀ (hreach q₀)
      have hT' : ((T.image (fun q => A.act q v)) \ C).card ≤ m := by
        have hsub' : (T.image (fun q => A.act q v)) \ C ⊆ ((T \ C).erase q₀).image (fun q => A.act q v) := by
          intro y hy
          rw [Finset.mem_sdiff, Finset.mem_image] at hy
          obtain ⟨⟨x, hx, rfl⟩, hyC⟩ := hy
          rw [Finset.mem_image]
          refine ⟨x, ?_, rfl⟩
          rw [Finset.mem_erase, Finset.mem_sdiff]
          refine ⟨?_, hx, ?_⟩
          · rintro rfl
            exact hyC hv
          · intro hxC
            exact hyC (s51_act_mem A hC v x hxC)
        calc ((T.image (fun q => A.act q v)) \ C).card
            ≤ (((T \ C).erase q₀).image (fun q => A.act q v)).card := Finset.card_le_card hsub'
          _ ≤ ((T \ C).erase q₀).card := Finset.card_image_le
          _ = (T \ C).card - 1 := Finset.card_erase_of_mem hq₀
          _ ≤ m := by omega
      obtain ⟨u', hu'len, hu'⟩ := ih _ hT'
      refine ⟨v ++ u', ?_, fun q hq => ?_⟩
      · have hmul : (m + 1) * (Finset.univ \ C).card = m * (Finset.univ \ C).card + (Finset.univ \ C).card := by
          ring
        rw [List.length_append, hmul]
        omega
      · rw [s51_act_append]
        exact hu' _ (Finset.mem_image_of_mem _ hq)

/-- Some letter is not injective when a synchronizing automaton has two distinct states. -/
private theorem s51_injective_act (hinj : ∀ b : S, Function.Injective (fun q => A.step q b)) :
    ∀ w : List S, Function.Injective (fun q => A.act q w)
  | [] => fun _ _ h => h
  | b :: w => by
    intro x y h
    apply hinj b
    apply s51_injective_act hinj w
    exact h

private theorem s51_exists_merging [Fintype Q] (hA : A.Synchronizing) (h1 : 1 < Fintype.card Q) :
    ∃ b : S, ∃ x y : Q, x ≠ y ∧ A.step x b = A.step y b := by
  by_contra hcon
  push Not at hcon
  have hinj : ∀ b : S, Function.Injective (fun q => A.step q b) := by
    intro b x y hxy
    by_contra hne
    exact hcon b x y hne hxy
  obtain ⟨w, r, hr⟩ := hA
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card h1
  exact hxy (s51_injective_act A hinj w (by simp only [hr]))

private theorem s51_two_cover [Fintype Q] [DecidableEq Q] {x y : Q} (h2 : Fintype.card Q = 2) (hxy : x ≠ y) :
    ∀ z : Q, z = x ∨ z = y := by
  have hcard : ({x, y} : Finset Q).card = Fintype.card Q := by rw [Finset.card_pair hxy, h2]
  have huniv := Finset.eq_univ_of_card _ hcard
  intro z
  have hz : z ∈ ({x, y} : Finset Q) := by
    rw [huniv]
    exact Finset.mem_univ z
  simpa using hz

/-- Equal unordered pairs. -/
private theorem s51_pair_eq [DecidableEq Q] {a b c d : Q} (h : ({a, b} : Finset Q) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Finset Q) := by rw [← h]; simp
  have hb : b ∈ ({c, d} : Finset Q) := by rw [← h]; simp
  have hc : c ∈ ({a, b} : Finset Q) := by rw [h]; simp
  have hd : d ∈ ({a, b} : Finset Q) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- Two states that can be merged are merged by a word of length at most `C(n, 2)`. -/
private theorem s51_short_merge [Fintype Q] [DecidableEq Q] (p q : Q) (hm : ∃ w : List S, A.act p w = A.act q w) :
    ∃ v : List S, v.length ≤ (Fintype.card Q).choose 2 ∧ A.act p v = A.act q v := by
  have hex : ∃ n, ∃ w : List S, w.length = n ∧ A.act p w = A.act q w := by
    obtain ⟨w, hw⟩ := hm
    exact ⟨_, w, rfl, hw⟩
  obtain ⟨w, hwlen, hw⟩ := Nat.find_spec hex
  refine ⟨w, ?_, hw⟩
  by_contra hlt
  push Not at hlt
  have hout : ∀ i ∈ Finset.range w.length,
      ({A.act p (w.take i), A.act q (w.take i)} : Finset Q) ∈
        Finset.powersetCard 2 (Finset.univ : Finset Q) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, Finset.card_pair ?_⟩
    intro hin
    have := Nat.find_min' hex ⟨w.take i, rfl, hin⟩
    rw [List.length_take] at this
    omega
  have hcard : (Finset.powersetCard 2 (Finset.univ : Finset Q)).card < (Finset.range w.length).card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Finset.card_range]
    exact hlt
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hout
  rw [Finset.mem_range] at hi hj
  have key : ∀ i j, i < j → j < w.length →
      ({A.act p (w.take i), A.act q (w.take i)} : Finset Q) =
        {A.act p (w.take j), A.act q (w.take j)} → False := by
    intro i j hij hj heq
    have hlen : (w.take i ++ w.drop j).length < w.length := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    have hp : A.act p w = A.act (A.act p (w.take j)) (w.drop j) := by
      rw [← s51_act_append, List.take_append_drop]
    have hq : A.act q w = A.act (A.act q (w.take j)) (w.drop j) := by
      rw [← s51_act_append, List.take_append_drop]
    have hmerge : A.act p (w.take i ++ w.drop j) = A.act q (w.take i ++ w.drop j) := by
      rw [s51_act_append, s51_act_append]
      rcases s51_pair_eq heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, ← hp, ← hq, hw]
      · rw [h1, h2, ← hp, ← hq, hw]
    have := Nat.find_min' hex ⟨_, rfl, hmerge⟩
    omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hj heq
  · exact key j i h hi heq.symm

/-- A nonempty set of at most two states is covered by two states. -/
private theorem s51_card_le_two_cover [DecidableEq Q] {T : Finset Q} (hne : T.Nonempty) (h : T.card ≤ 2) :
    ∃ a b : Q, ∀ z ∈ T, z = a ∨ z = b := by
  rcases Nat.lt_or_ge T.card 2 with hlt | hge
  · have h1 : T.card = 1 := by
      have := hne.card_pos
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    refine ⟨a, a, fun z hz => Or.inl ?_⟩
    rw [ha] at hz
    exact Finset.mem_singleton.mp hz
  · have h2 : T.card = 2 := by omega
    obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp h2
    refine ⟨a, b, fun z hz => ?_⟩
    rw [hab] at hz
    simpa using hz

/-- With three states, a reset word of length at most four exists. -/
private theorem s51_rt_le_three [Fintype Q] [DecidableEq Q] (hA : A.Synchronizing) (h3 : Fintype.card Q = 3) :
    A.rt ≤ 4 := by
  obtain ⟨c, x, y, hxy, hc⟩ := s51_exists_merging A hA (by omega)
  have himg : (Finset.univ.image (fun q => A.step q c)).card ≤ 2 := by
    have hle := Finset.card_image_le (s := (Finset.univ : Finset Q)) (f := fun q => A.step q c)
    have hne : (Finset.univ.image (fun q => A.step q c)).card ≠ (Finset.univ : Finset Q).card := by
      intro heq
      exact hxy (Finset.card_image_iff.mp heq (Finset.mem_coe.mpr (Finset.mem_univ x))
        (Finset.mem_coe.mpr (Finset.mem_univ y)) hc)
    rw [Finset.card_univ, h3] at hle hne
    omega
  have hIne : (Finset.univ.image (fun q => A.step q c)).Nonempty :=
    ⟨A.step x c, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩
  obtain ⟨a, b, hcover⟩ := s51_card_le_two_cover hIne himg
  have hab : ∀ q, A.step q c = a ∨ A.step q c = b :=
    fun q => hcover _ (Finset.mem_image_of_mem _ (Finset.mem_univ q))
  obtain ⟨w, r, hr⟩ := hA
  obtain ⟨v, hvlen, hv⟩ := s51_short_merge A a b ⟨w, (hr a).trans (hr b).symm⟩
  have hreset : A.IsReset (c :: v) := by
    refine ⟨A.act a v, fun q => ?_⟩
    rw [s51_act_cons]
    rcases hab q with h | h
    · rw [h]
    · rw [h]
      exact hv.symm
  have hlen : (c :: v).length ≤ 4 := by
    rw [h3] at hvlen
    have hch : Nat.choose 3 2 = 3 := by decide
    simp only [List.length_cons]
    omega
  exact (s51_minLen_le hreset).trans (by exact_mod_cast hlen)

end Helpers

/-! ### The rows -/

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

theorem sec5_unique_min_closed_proved [Nonempty Q] (hA : A.Synchronizing) :
    (∀ C C' : Finset Q, C.Nonempty → C'.Nonempty → A.IsClosed C → A.IsClosed C' → ¬ Disjoint C C') ∧
      (∀ C C' : Finset Q, A.IsClosed C → A.IsClosed C' → A.IsClosed (C ∩ C')) ∧
      ∃! C : Finset Q, A.IsMinClosed C ∧ ∀ C' : Finset Q, C'.Nonempty → A.IsClosed C' → C ⊆ C' := by
  refine ⟨s51_not_disjoint A hA, s51_inter_closed A, ?_⟩
  obtain ⟨C, hC⟩ := s51_exists_least A hA
  exact ⟨C, hC, fun C' hC' => Finset.Subset.antisymm (hC'.2 C hC.1.1 hC.1.2.1) (hC.2 C' hC'.1.1 hC'.1.2.1)⟩

theorem sec5_restrict_proved (hA : A.Synchronizing) (C : Finset Q) (hmin : A.IsMinClosed C) (hC : A.IsClosed C) :
    (A.restrict C hC).StronglyConnected ∧ (A.restrict C hC).Synchronizing ∧ (∀ q, ∃ w, A.act q w ∈ C) ∧
      (¬ A.StronglyConnected → (Finset.univ \ C).Nonempty) := by
  refine ⟨s51_restrict_sc A C hmin hC, s51_restrict_sync A hA C hmin.1 hC, ?_, ?_⟩
  · intro q
    obtain ⟨w, r, hr⟩ := hA
    exact ⟨w, by rw [hr q]; exact s51_reset_mem A hC hmin.1 hr⟩
  · intro hsc
    by_contra hemp
    apply hsc
    intro K hK
    rcases K.eq_empty_or_nonempty with h | h
    · exact Or.inl h
    · right
      have hCK := s51_min_subset A hA hmin h hK
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
      exact Finset.eq_univ_of_forall (fun q => hCK (hemp (Finset.mem_univ q)))

theorem lem_5_3_push_word_proved (hA : A.Synchronizing) (C : Finset Q) (hne : C.Nonempty) (hC : A.IsClosed C) :
    ∃ u : List S, u.length ≤ (Finset.univ \ C).card ^ 2 ∧ ∀ q, A.act q u ∈ C := by
  have hreach : ∀ q, ∃ w, A.act q w ∈ C := by
    intro q
    obtain ⟨w, r, hr⟩ := hA
    exact ⟨w, by rw [hr q]; exact s51_reset_mem A hC hne hr⟩
  obtain ⟨u, hulen, hu⟩ := s51_push_aux A C hC hreach (Finset.univ \ C).card Finset.univ le_rfl
  exact ⟨u, by rw [sq]; exact hulen, fun q => hu q (Finset.mem_univ q)⟩

theorem lem_5_3_proved (hA : A.Synchronizing) (C : Finset Q) (hne : C.Nonempty) (hC : A.IsClosed C) :
    A.rt ≤ (((Finset.univ \ C).card ^ 2 : ℕ) : ℕ∞) + (A.restrict C hC).rt := by
  by_cases htop : (A.restrict C hC).rt = ⊤
  · rw [htop, add_top]
    exact le_top
  · obtain ⟨w, ⟨r, hr⟩, hwlen⟩ := s51_exists_of_minLen_ne_top (P := (A.restrict C hC).IsReset) htop
    obtain ⟨u, hulen, hu⟩ := lem_5_3_push_word_proved A hA C hne hC
    have hreset : A.IsReset (u ++ w) := by
      refine ⟨r.1, fun q => ?_⟩
      rw [s51_act_append]
      exact (s51_restrict_act A C hC w ⟨A.act q u, hu q⟩).symm.trans (congrArg Subtype.val (hr _))
    have hlen : ((u ++ w).length : ℕ∞) = (u.length : ℕ∞) + (w.length : ℕ∞) := by
      rw [List.length_append, Nat.cast_add]
    have hle : (u.length : ℕ∞) ≤ (((Finset.univ \ C).card ^ 2 : ℕ) : ℕ∞) := by exact_mod_cast hulen
    calc A.rt ≤ ((u ++ w).length : ℕ∞) := s51_minLen_le hreset
      _ = (u.length : ℕ∞) + (A.restrict C hC).rt := by rw [hlen, hwlen]; rfl
      _ ≤ (((Finset.univ \ C).card ^ 2 : ℕ) : ℕ∞) + (A.restrict C hC).rt := add_le_add hle le_rfl

theorem arith_r_sq_proved (n r : ℕ) (hr : r ≤ n - 1) : r ^ 2 + (n - 1 - r) ^ 2 ≤ (n - 1) ^ 2 := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hr
  rw [hs, Nat.add_sub_cancel_left]
  nlinarith [Nat.zero_le (r * s)]

theorem sec5_two_state_rt_proved (hA : A.Synchronizing) (h2 : Fintype.card Q = 2) : A.rt = 1 := by
  obtain ⟨b, x, y, hxy, hb⟩ := s51_exists_merging A hA (by omega)
  have hall : ∀ z : Q, z = x ∨ z = y := s51_two_cover h2 hxy
  apply le_antisymm
  · have hreset : A.IsReset [b] := by
      refine ⟨A.step x b, fun z => ?_⟩
      rcases hall z with h | h
      · rw [h]
        rfl
      · rw [h]
        exact hb.symm
    exact (s51_minLen_le hreset).trans (by simp)
  · show (1 : ℕ∞) ≤ minLen A.IsReset
    apply s51_le_minLen
    intro w hw
    match w, hw with
    | [], ⟨r, hr⟩ => exact absurd ((hr x).trans (hr y).symm) hxy
    | a :: l, _ =>
      have h1 : 1 ≤ (a :: l).length := by simp
      exact_mod_cast h1

end General

section General2

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

theorem sec54_small_n_proved (hA : A.Synchronizing) (hn : Fintype.card Q ≤ 3) :
    A.rt ≤ (((Fintype.card Q ^ 3 - Fintype.card Q) / 6 : ℕ) : ℕ∞) ∧
      (Fintype.card Q ^ 3 - Fintype.card Q) / 6 ≤ (Fintype.card Q - 1) ^ 2 := by
  refine ⟨?_, ?_⟩
  · have hpos : 0 < Fintype.card Q := by
      obtain ⟨_, r, _⟩ := hA
      exact Fintype.card_pos_iff.mpr ⟨r⟩
    have hcases : Fintype.card Q = 1 ∨ Fintype.card Q = 2 ∨ Fintype.card Q = 3 := by omega
    rcases hcases with h | h | h
    · rw [h]
      obtain ⟨r, hr⟩ := Fintype.card_eq_one_iff.mp h
      have hreset : A.IsReset ([] : List S) := ⟨r, fun q => hr q⟩
      exact (s51_minLen_le hreset).trans (by norm_num)
    · rw [h, sec5_two_state_rt_proved A hA h]
      norm_num
    · rw [h]
      exact (s51_rt_le_three A hA h).trans (by norm_num)
  · have hcases : Fintype.card Q = 0 ∨ Fintype.card Q = 1 ∨ Fintype.card Q = 2 ∨ Fintype.card Q = 3 := by
      omega
    rcases hcases with h | h | h | h <;> rw [h] <;> norm_num

end General2

/-! ### Arithmetic rows -/

private theorem s51_cubic_aux (m : ℕ) : (m + 2) * (m + 3) < 24 * 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    nlinarith [ih, Nat.zero_le k]

theorem sec6_cubic_smaller_proved (n : ℕ) (hn : 2 ≤ n) :
    (n ^ 3 - n) / 6 < 2 ^ (n - 1) * (n - (n - 1) + 1) * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - (m + 1) + 1 = 2 := by omega
  have h3 : (m + 2) ^ 3 - (m + 2) = (m + 1) * ((m + 2) * (m + 3)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h1, h2, h3, Nat.div_lt_iff_lt_mul (by norm_num)]
  have h4 := s51_cubic_aux m
  have h5 := Nat.mul_lt_mul_of_pos_left h4 (Nat.succ_pos m)
  rw [pow_succ]
  nlinarith [h5]

theorem prop_5_12_sum_proved (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑ j ∈ Finset.Icc 1 ℓ, max j (ℓ - j) ≤ (ℓ - 1) ^ 2 + ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
  have hbound : ∑ j ∈ Finset.Icc 1 k, max j (k + 1 - j) ≤ k * k := by
    have := Finset.sum_le_card_nsmul (Finset.Icc 1 k) (fun j => max j (k + 1 - j)) k (by
      intro j hj
      rw [Finset.mem_Icc] at hj
      exact max_le hj.2 (by omega))
    simpa [Nat.card_Icc] using this
  have hlast : max (k + 1) (k + 1 - (k + 1)) = k + 1 := by simp
  have hsq : (k + 1 - 1) ^ 2 = k * k := by rw [Nat.add_sub_cancel, sq]
  rw [hlast, hsq]
  omega

theorem rem_5_15_berlinkov_proved (n : ℕ) (_hn : 3 ≤ n) :
    (1 + ((n : ℤ) - 1) * (n + 2 + 2 - 4) = n ^ 2 - n + 1) ∧ (1 + ((n : ℤ) - 1) * (n + 2 + 3 - 4) = n ^ 2) ∧
      (1 + ((n : ℤ) - 1) * (n + 2 + 4 - 4) = n ^ 2 + n - 1) := by
  refine ⟨by ring, by ring, by ring⟩

theorem rem_3_4_vals_proved (n : ℕ) (hn : 2 ≤ n) :
    (∀ k : ℕ, 1 ≤ k → (1 + (n - 1) * ((n - 1 + k) - 2) : ℤ) = 1 + (n - 1) * (n + k - 3)) ∧
      (1 + ((n : ℤ) - 1) * (n + 1 - 3) = 1 + (n - 2) * (n - 1)) ∧
      (1 + ((n : ℤ) - 1) * (n + 2 - 3) = (n - 1) ^ 2 + 1) ∧
      ∀ k k' : ℕ, k < k' → (1 + ((n : ℤ) - 1) * (n + k - 3)) < 1 + (n - 1) * (n + k' - 3) := by
  refine ⟨fun k _ => by ring, by ring, by ring, fun k k' hkk' => ?_⟩
  have h1 : (1 : ℤ) ≤ (n : ℤ) - 1 := by
    have : (2 : ℤ) ≤ n := by exact_mod_cast hn
    linarith
  have h2 : (k : ℤ) < k' := by exact_mod_cast hkk'
  nlinarith

/-- The denominator of `a / b` for natural numbers. -/
private theorem s51_den_natDiv (a b : ℕ) (hb : b ≠ 0) : ((a : ℚ) / (b : ℚ)).den = b / Nat.gcd b a := by
  have h := Rat.den_mkRat (a : ℤ) b
  rw [Rat.mkRat_eq_div] at h
  simpa [hb] using h

theorem rem_3_4_w_eq_L_proved {ι : Type*} [Fintype ι] (u : ι → ℕ) (hu : ∀ i, 0 < u i)
    (hgcd : Finset.univ.gcd u = 1) :
    Finset.univ.lcm (fun i => ((u i : ℚ) / (∑ j, u j : ℕ)).den) = ∑ j, u j := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Finset.univ_eq_empty, Finset.gcd_empty] at hgcd
    exact absurd hgcd zero_ne_one
  obtain ⟨i₀⟩ := hι
  set w := ∑ j, u j with hw
  have hwpos : 0 < w :=
    lt_of_lt_of_le (hu i₀) (Finset.single_le_sum (fun j _ => Nat.zero_le (u j)) (Finset.mem_univ i₀))
  have hden : (fun i => ((u i : ℚ) / (w : ℚ)).den) = fun i => w / Nat.gcd w (u i) :=
    funext fun i => s51_den_natDiv (u i) w hwpos.ne'
  rw [hden]
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro i _
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left w (u i))
  · have hdiv : ∀ i ∈ (Finset.univ : Finset ι),
        w ∣ (Finset.univ.lcm (fun i => w / Nat.gcd w (u i))) * u i := by
      intro i hi
      have h1 : w / Nat.gcd w (u i) ∣ Finset.univ.lcm (fun i => w / Nat.gcd w (u i)) := Finset.dvd_lcm hi
      have h2 : w ∣ (w / Nat.gcd w (u i)) * u i := by
        obtain ⟨t, ht⟩ := Nat.gcd_dvd_right w (u i)
        refine ⟨t, ?_⟩
        calc w / Nat.gcd w (u i) * u i = w / Nat.gcd w (u i) * (Nat.gcd w (u i) * t) := by rw [← ht]
          _ = w / Nat.gcd w (u i) * Nat.gcd w (u i) * t := by ring
          _ = w * t := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left w (u i))]
      exact h2.trans (Nat.mul_dvd_mul_right h1 (u i))
    have hg := Finset.dvd_gcd hdiv
    rw [Finset.gcd_mul_left, hgcd, normalize_eq, mul_one] at hg
    exact hg

theorem rem_5_15_L_proved {ι : Type*} [Fintype ι] (u : ι → ℕ) (hu : ∀ i, 0 < u i) (h1 : ∃ i, u i = 1) :
    Finset.univ.lcm (fun i => ((u i : ℚ) / (∑ j, u j : ℕ)).den) = ∑ j, u j := by
  obtain ⟨i, hi⟩ := h1
  have hgcd : Finset.univ.gcd u = 1 := by
    have hd : Finset.univ.gcd u ∣ u i := Finset.gcd_dvd (Finset.mem_univ i)
    rw [hi] at hd
    exact Nat.dvd_one.mp hd
  exact rem_3_4_w_eq_L_proved u hu hgcd

end CernyQE
