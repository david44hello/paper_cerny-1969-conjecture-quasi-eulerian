/-
CernyQE/Proofs/Thm59.lean — Theorem 5.9: the case analysis over the configurations of a binary witness of degree two.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary
import CernyQE.Proofs.Sec51
import CernyQE.Proofs.Thm31
import CernyQE.Proofs.Stationary
import CernyQE.Proofs.BinaryBase
import CernyQE.Proofs.Census
import CernyQE.Proofs.Prop513
import CernyQE.Proofs.Prop514
import CernyQE.Proofs.Props511
import CernyQE.Proofs.Rows5x

namespace CernyQE

open Classical Automaton Matrix

universe u v

namespace Thm59

/-- The pair `(min a b, max a b)` determines `{a, b}`. -/
theorem min_max_cases {a b u v : ℚ} (h : (min a b, max a b) = (u, v)) : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_total a b with hab | hab
  · left
    rw [min_eq_left hab] at h1
    rw [max_eq_right hab] at h2
    exact ⟨h1, h2⟩
  · right
    rw [min_eq_right hab] at h1
    rw [max_eq_left hab] at h2
    exact ⟨h2, h1⟩

/-- The values `α(x₁), α(x₂)` of a configuration of class `(u, v)` are `u, v` in some order. -/
theorem alpha_pair {cf : Config} {α₁ α₂ : ℝ} (h1 : α₁ = (cf.t 0 : ℝ)) (h2 : α₂ = (cf.t 1 : ℝ)) {u v : ℚ}
    (hcls : cf.cls = (u, v)) : (α₁ = (u : ℝ) ∧ α₂ = (v : ℝ)) ∨ (α₁ = (v : ℝ) ∧ α₂ = (u : ℝ)) := by
  rcases min_max_cases (a := cf.t 0) (b := cf.t 1) hcls with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨by rw [h1, ha], by rw [h2, hb]⟩
  · exact Or.inr ⟨by rw [h1, ha], by rw [h2, hb]⟩

theorem fin3_pair (p q : Fin 3) : ({p, q} : Finset (Fin 3)) = {0, 1} ↔ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) := by
  revert p q
  decide

/-- `1 + (n-2) n = (n-1)^2` for `n ≥ 2`. -/
theorem sq_eq (n : ℕ) (hn : 2 ≤ n) : 1 + (n - 2) * n = (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left, show 2 + m - 1 = m + 1 by omega]
  ring

end Thm59

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

namespace Thm59

/-- The exceptional states are not in `E`; `s` is. -/
theorem x_not_mem {W : QEWitness A 2} {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) {x : Q} (hx : x = x₁ ∨ x = x₂) :
    x ∉ W.E := by
  intro hE
  have hxX : x ∈ W.X := by
    rw [hX]
    rcases hx with rfl | rfl <;> simp
  exact (Finset.mem_sdiff.mp hxX).2 hE

/-- Every letter maps an exceptional state to `x₁`, `x₂` or `s`. -/
theorem step_mem {W : QEWitness A 2} {x₁ x₂ : Q} (hX : W.X = {x₁, x₂}) {x : Q} (hx : x = x₁ ∨ x = x₂) (c : S) :
    A.step x c = x₁ ∨ A.step x c = x₂ ∨ A.step x c = W.s := by
  rcases W.edge_X x (x_not_mem A hX hx) c with h | h
  · have hmem : A.step x c ∈ W.X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩
    rw [hX] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    tauto
  · exact Or.inr (Or.inr h)

/-- A block configuration comes from a block pair. -/
theorem block_pair (a b : S) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (hb : (A.configOf a b W.E x₁ x₂).IsBlock) : A.IsBlockPair x₁ x₂ := by
  have hs1 : W.s ≠ x₁ := fun h => x_not_mem A hX (Or.inl rfl) (h ▸ W.s_mem)
  have hs2 : W.s ≠ x₂ := fun h => x_not_mem A hX (Or.inr rfl) (h ▸ W.s_mem)
  have key : ∀ c : S, (stateCode x₁ x₂ (A.step x₁ c) = stateCode x₁ x₂ (A.step x₂ c) ∨
      ({stateCode x₁ x₂ (A.step x₁ c), stateCode x₁ x₂ (A.step x₂ c)} : Finset (Fin 3)) = {0, 1}) →
      A.step x₁ c = A.step x₂ c ∨ ({A.step x₁ c, A.step x₂ c} : Finset Q) = {x₁, x₂} := by
    intro c hc
    rw [fin3_pair] at hc
    rcases step_mem A hX (Or.inl rfl) c with h1 | h1 | h1 <;>
      rcases step_mem A hX (Or.inr rfl) c with h2 | h2 | h2 <;>
      rw [h1, h2] at hc ⊢ <;>
      simp [stateCode, h12, h12.symm, hs1, hs2, Finset.pair_comm] at hc ⊢
  intro c
  obtain ⟨ha, hb'⟩ := hb
  rcases hS c with rfl | rfl
  · exact key _ ha
  · exact key _ hb'

/-- With the weights `1/2`, `α(x_i)` is `t_i` of the configuration. -/
theorem alpha_t (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected) (W : QEWitness A 2)
    (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    A.alphaStat W.E (fun _ => 1 / 2) x₁ = ((A.configOf a b W.E x₁ x₂).t 0 : ℝ) ∧
      A.alphaStat W.E (fun _ => 1 / 2) x₂ = ((A.configOf a b W.E x₁ x₂).t 1 : ℝ) := by
  have h := (lem_5_7_b_proved A a b hab hS W x₁ x₂ hX h12).2.2.2.2 hsc
  exact ⟨h 0, h 1⟩

/-- If `α` is `1` at one exceptional state, Theorem 3.1 applies at the other one. -/
theorem case_t1 (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    {x y : Q} (hxy : (x = x₁ ∧ y = x₂) ∨ (x = x₂ ∧ y = x₁)) (hy1 : A.alphaStat W.E (fun _ => 1 / 2) y = 1) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  obtain ⟨W', hE, -, hp⟩ := lem_5_7_a_proved A a b hab hS W
  obtain ⟨-, hstat, hpos⟩ := lem_5_5_proved A hsc W'
  have hw := W'.weights
  rw [hE, hp] at hstat hpos
  rw [hp] at hw
  refine thm_3_1_proved A hA hn _ hw _ hstat hpos x ?_
  have hone : ∀ q, q ≠ x → A.alphaStat W.E (fun _ => 1 / 2) q = 1 := by
    intro q hq
    by_cases hqE : q ∈ W.E
    · have h' : q ∉ Finset.univ \ W.E := fun h => (Finset.mem_sdiff.mp h).2 hqE
      simp [Automaton.alphaStat, h']
    · have hqX : q ∈ W.X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hqE⟩
      rw [hX] at hqX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqX
      have hqy : q = y := by
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
      rw [hqy, hy1]
  intro q q' hq hq'
  rw [hone q hq, hone q' hq']

/-- Theorem 5.9 for `n ≥ 4`, from Propositions 5.6, 5.11 and 5.12 (given as hypotheses for this witness). -/
theorem main_of (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (hopen : ∀ o ∈ openConfigs, A.configOf a b W.E x₁ x₂ ∉ o.renamings)
    (h56 : A.IsBlockPair x₁ x₂ → A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞))
    (h511 : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ)) →
      A.rt ≤ ((1 + (Fintype.card Q - 2) * Fintype.card Q : ℕ) : ℕ∞))
    (h512 : A.configOf a b W.E x₁ x₂ ∈ (⟨2, 1, 0, 2, 0, 1⟩ : Config).renamings ∪
      (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings →
      A.rt ≤ ((Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧
        Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q ≤ (Fintype.card Q - 1) ^ 2) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  set cf := A.configOf a b W.E x₁ x₂ with hcfdef
  have hn2 : 2 ≤ Fintype.card Q := by omega
  obtain ⟨hch, hval⟩ := sec54_config_valid_proved A a b hab hS hsc W x₁ x₂ hX h12
  obtain ⟨hα1, hα2⟩ := alpha_t A a b hab hS hsc W x₁ x₂ hX h12
  -- (1) some `t_i = 1`: Theorem 3.1
  by_cases ht0 : cf.t 0 = 1
  · refine case_t1 A a b hab hS hA hsc hn2 W x₁ x₂ hX (x := x₂) (y := x₁) (Or.inr ⟨rfl, rfl⟩) ?_
    rw [hα1, ht0, Rat.cast_one]
  by_cases ht1 : cf.t 1 = 1
  · refine case_t1 A a b hab hS hA hsc hn2 W x₁ x₂ hX (x := x₁) (y := x₂) (Or.inl ⟨rfl, rfl⟩) ?_
    rw [hα2, ht1, Rat.cast_one]
  -- (2) block configurations: Proposition 5.6
  by_cases hblk : cf.IsBlock
  · exact h56 (block_pair A a b hS W x₁ x₂ hX h12 hblk)
  -- (3) the integer classes: Proposition 5.14
  by_cases hint : cf.cls ∈ ({(2, 2), (2, 3), (2, 4)} : Finset (ℚ × ℚ))
  · refine prop_5_14_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hint
    rcases hint with h | h | h <;> rcases alpha_pair hα1 hα2 h with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rw [e1, e2] <;> push_cast <;> simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] <;> norm_num
  -- (4) the six remaining configurations: Propositions 5.11-5.13
  have hmem : cf ∈ choices.filter (fun c => c.Valid ∧ c.t 0 ≠ 1 ∧ c.t 1 ≠ 1 ∧ ¬ c.IsBlock ∧
      (∀ o ∈ openConfigs, c ∉ o.renamings) ∧ c.cls ∉ ({(2, 2), (2, 3), (2, 4)} : Finset (ℚ × ℚ))) :=
    Finset.mem_filter.2 ⟨hch, hval, ht0, ht1, hblk, hopen, hint⟩
  have himg := Finset.mem_image_of_mem Config.renamings hmem
  rw [thm_5_9_remaining_six_proved.1] at himg
  obtain ⟨c₀, hc₀, hren⟩ := Finset.mem_image.1 himg
  have hcf : cf ∈ c₀.renamings := by
    rw [hren]
    simp [Config.renamings]
  have hcls : c₀ ∈ choices → c₀.Valid → cf.cls = c₀.cls := fun h0 hv =>
    (lem_5_8_proved.2.2.2.2 c₀ h0 cf hcf).2.2 hv
  have h511' : ∀ {u v : ℚ}, cf.cls = (u, v) →
      ((u : ℝ), (v : ℝ)) ∈ ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ)) →
      ((v : ℝ), (u : ℝ)) ∈ ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ)) →
      A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
    intro u v hc huv hvu
    rw [← sq_eq _ hn2]
    apply h511
    rcases alpha_pair hα1 hα2 hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact huv
    · exact hvu
  have h513' : ∀ {u v : ℚ}, cf.cls = (u, v) →
      ((u : ℝ), (v : ℝ)) ∈ ({(1/2, 2), (2, 1/2), (3/2, 2), (2, 3/2)} : Finset (ℝ × ℝ)) →
      ((v : ℝ), (u : ℝ)) ∈ ({(1/2, 2), (2, 1/2), (3/2, 2), (2, 3/2)} : Finset (ℝ × ℝ)) →
      A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
    intro u v hc huv hvu
    have hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
        ({(1/2, 2), (2, 1/2), (3/2, 2), (2, 3/2)} : Finset (ℝ × ℝ)) := by
      rcases alpha_pair hα1 hα2 hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
      · exact huv
      · exact hvu
    obtain ⟨hrt, hle⟩ := prop_5_13_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 hcl
    exact hrt.trans (by exact_mod_cast hle)
  have h512' : A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) → A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := id
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc₀
  rcases hc₀ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : cf.cls = ((1/2 : ℚ), (3/4 : ℚ)) :=
      (hcls ((Census.mem_choices _).2 (by decide)) (by decide +kernel)).trans (by decide +kernel)
    exact h511' hc (by norm_num) (by norm_num)
  · have hc : cf.cls = ((1/4 : ℚ), (1/2 : ℚ)) :=
      (hcls ((Census.mem_choices _).2 (by decide)) (by decide +kernel)).trans (by decide +kernel)
    exact h511' hc (by norm_num) (by norm_num)
  · obtain ⟨hrt, hle⟩ := h512 (Finset.mem_union.2 (Or.inl hcf))
    exact h512' (hrt.trans (by exact_mod_cast hle))
  · obtain ⟨hrt, hle⟩ := h512 (Finset.mem_union.2 (Or.inr hcf))
    exact h512' (hrt.trans (by exact_mod_cast hle))
  · have hc : cf.cls = ((1/2 : ℚ), (2 : ℚ)) :=
      (hcls ((Census.mem_choices _).2 (by decide)) (by decide +kernel)).trans (by decide +kernel)
    exact h513' hc (by norm_num) (by norm_num)
  · have hc : cf.cls = ((3/2 : ℚ), (2 : ℚ)) :=
      (hcls ((Census.mem_choices _).2 (by decide)) (by decide +kernel)).trans (by decide +kernel)
    exact h513' hc (by norm_num) (by norm_num)

end Thm59

theorem thm_5_9_proved (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected)
    (hW : ∃ (W : QEWitness A 2) (x₁ x₂ : Q), W.X = {x₁, x₂} ∧ x₁ ≠ x₂ ∧
      ∀ o ∈ openConfigs, A.configOf a b W.E x₁ x₂ ∉ o.renamings) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) := by
  by_cases hn : Fintype.card Q ≤ 3
  · obtain ⟨h1, h2⟩ := sec54_small_n_proved A hA hn
    exact h1.trans (by exact_mod_cast h2)
  obtain ⟨W, x₁, x₂, hX, h12, hopen⟩ := hW
  exact Thm59.main_of A a b hab hS hA hsc (by omega) W x₁ x₂ hX h12 hopen
    (prop_5_6_proved A hA W x₁ x₂ hX h12)
    (prop_5_11_proved A a b hab hS hA hsc (by omega) W x₁ x₂ hX h12)
    (prop_5_12_proved A a b hab hS hA hsc (by omega) W x₁ x₂ hX h12)

end General

end CernyQE
