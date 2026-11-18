/-
CernyQE/Proofs/Census.lean — the finite facts of Section 5.4 on configurations, checked by kernel computation.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Binary
import Mathlib

namespace CernyQE

open Classical Automaton Matrix

universe u v

/-! Helpers live in `CernyQE.Census`, so that they cannot clash with other modules. -/

namespace Census

open Config

/-! ### `choices` as an injective map (no deduplication in the kernel) -/

/-- The map behind `choices`. -/
def choiceOf (v : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3) : Config :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1.val, v.2.2.2.2.2.val⟩

theorem choiceOf_injective : Function.Injective choiceOf := by
  rintro ⟨a, b, c, d, e, f⟩ ⟨a', b', c', d', e', f'⟩ h
  simp only [choiceOf, Config.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [h1, h2, h3, h4, Fin.ext h5, Fin.ext h6]

/-- `choices` is the image of an injective map, so it is a `Finset.map`. -/
theorem choices_eq_map : choices = ((Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3)).filter
      (fun v => v.2.2.2.2.1.val + v.2.2.2.2.2.val ≤ 2 ∧ ¬ (v.2.2.2.2.1 = 0 ∧ v.2.2.2.2.2 = 0))).map
      ⟨choiceOf, choiceOf_injective⟩ := by
  rw [Finset.map_eq_image]; rfl

/-! ### Membership in `choices`, and the renamings keep the choices, validity and the class -/

theorem mem_choices (c : Config) : c ∈ choices ↔ c.nu1 + c.nu2 ≤ 2 ∧ ¬ (c.nu1 = 0 ∧ c.nu2 = 0) := by
  rw [choices_eq_map]
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv.1, fun h => hv.2 ⟨Fin.ext h.1, Fin.ext h.2⟩⟩
  · intro h
    refine ⟨(c.x1a, c.x1b, c.x2a, c.x2b, ⟨c.nu1, by omega⟩, ⟨c.nu2, by omega⟩), ⟨h.1, ?_⟩, rfl⟩
    rintro ⟨h1, h2⟩
    exact h.2 ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩

theorem swapCode_eq_castSucc : ∀ (k : Fin 3) (j : Fin 2), swapCode k = j.castSucc ↔ k = j.rev.castSucc := by
  decide

theorem tgt_swapX (cf : Config) (i c : Fin 2) : cf.swapX.tgt i c = swapCode (cf.tgt i.rev c) := by
  fin_cases i <;> fin_cases c <;> rfl

theorem tgt_swapL (cf : Config) (i c : Fin 2) : cf.swapL.tgt i c = cf.tgt i c.rev := by
  fin_cases i <;> fin_cases c <;> rfl

theorem Z_swapX (cf : Config) (i j : Fin 2) : cf.swapX.Z i j = cf.Z i.rev j.rev := by
  unfold Config.Z
  congr 3
  exact Finset.filter_congr (fun c _ => by rw [tgt_swapX, swapCode_eq_castSucc])

theorem Z_swapL (cf : Config) : cf.swapL.Z = cf.Z := by
  funext i j
  unfold Config.Z
  congr 2
  rw [Finset.card_filter, Finset.card_filter]
  simp only [Fin.sum_univ_two, tgt_swapL]
  exact add_comm _ _

theorem Z_swapX_00 (cf : Config) : cf.swapX.Z 0 0 = cf.Z 1 1 := Z_swapX cf 0 0
theorem Z_swapX_01 (cf : Config) : cf.swapX.Z 0 1 = cf.Z 1 0 := Z_swapX cf 0 1
theorem Z_swapX_10 (cf : Config) : cf.swapX.Z 1 0 = cf.Z 0 1 := Z_swapX cf 1 0
theorem Z_swapX_11 (cf : Config) : cf.swapX.Z 1 1 = cf.Z 0 0 := Z_swapX cf 1 1
theorem y_swapX_0 (cf : Config) : cf.swapX.y 0 = cf.y 1 := rfl
theorem y_swapX_1 (cf : Config) : cf.swapX.y 1 = cf.y 0 := rfl

theorem det_swapX (cf : Config) : cf.swapX.det = cf.det := by
  simp only [Config.det, Z_swapX_00, Z_swapX_01, Z_swapX_10, Z_swapX_11]
  ring

theorem t_swapX_zero (cf : Config) : cf.swapX.t 0 = cf.t 1 := by
  simp only [Config.t, Matrix.cons_val_zero, Matrix.cons_val_one, det_swapX, Z_swapX_00, Z_swapX_01, Z_swapX_10,
    Z_swapX_11, y_swapX_0, y_swapX_1]

theorem t_swapX_one (cf : Config) : cf.swapX.t 1 = cf.t 0 := by
  simp only [Config.t, Matrix.cons_val_zero, Matrix.cons_val_one, det_swapX, Z_swapX_00, Z_swapX_01, Z_swapX_10,
    Z_swapX_11, y_swapX_0, y_swapX_1]

theorem det_swapL (cf : Config) : cf.swapL.det = cf.det := by
  unfold Config.det; rw [Z_swapL]

theorem t_swapL (cf : Config) : cf.swapL.t = cf.t := by
  unfold Config.t; rw [det_swapL, Z_swapL]; rfl

theorem valid_swapX (cf : Config) : cf.swapX.Valid ↔ cf.Valid := by
  unfold Config.Valid; rw [det_swapX, t_swapX_zero, t_swapX_one]; tauto

theorem cls_swapX (cf : Config) : cf.swapX.cls = cf.cls := by
  unfold Config.cls; rw [t_swapX_zero, t_swapX_one, min_comm, max_comm]

theorem valid_swapL (cf : Config) : cf.swapL.Valid ↔ cf.Valid := by
  unfold Config.Valid; rw [det_swapL, t_swapL]

theorem cls_swapL (cf : Config) : cf.swapL.cls = cf.cls := by
  unfold Config.cls; rw [t_swapL]

theorem mem_choices_swapX {cf : Config} (h : cf ∈ choices) : cf.swapX ∈ choices := by
  rw [mem_choices] at h ⊢; exact ⟨by simp only [swapX]; omega, by simp only [swapX]; omega⟩

theorem mem_choices_swapL {cf : Config} (h : cf ∈ choices) : cf.swapL ∈ choices := by
  rw [mem_choices] at h ⊢; exact h

theorem renamings_keep : ∀ c ∈ choices, ∀ c' ∈ c.renamings,
    c' ∈ choices ∧ (c'.Valid ↔ c.Valid) ∧ (c.Valid → c'.cls = c.cls) := by
  intro c hc c' hc'
  simp only [Config.renamings, Finset.mem_insert, Finset.mem_singleton] at hc'
  rcases hc' with rfl | rfl | rfl | rfl
  · exact ⟨hc, Iff.rfl, fun _ => rfl⟩
  · exact ⟨mem_choices_swapX hc, valid_swapX c, fun _ => cls_swapX c⟩
  · exact ⟨mem_choices_swapL hc, valid_swapL c, fun _ => cls_swapL c⟩
  · refine ⟨mem_choices_swapL (mem_choices_swapX hc), ?_, fun _ => ?_⟩
    · rw [valid_swapL, valid_swapX]
    · rw [cls_swapL, cls_swapX]

/-! ### The classes, by two inclusions (deduplicating rationals in the kernel is slow) -/

/-- One valid configuration in each class of Table 1. -/
def classWitnesses : List Config :=
  [⟨1, 2, 2, 2, 1, 0⟩, ⟨1, 2, 0, 2, 0, 1⟩, ⟨0, 2, 0, 2, 0, 1⟩, ⟨1, 2, 2, 2, 1, 1⟩, ⟨0, 1, 2, 2, 1, 0⟩,
    ⟨0, 2, 0, 2, 1, 1⟩, ⟨0, 2, 0, 0, 1, 1⟩, ⟨1, 2, 0, 2, 0, 2⟩, ⟨0, 1, 0, 2, 0, 1⟩, ⟨0, 1, 0, 2, 1, 0⟩,
    ⟨1, 1, 0, 2, 1, 1⟩, ⟨0, 1, 0, 2, 0, 2⟩, ⟨0, 1, 0, 2, 1, 1⟩, ⟨0, 1, 0, 2, 2, 0⟩]

theorem classWitnesses_spec : ∀ k ∈ tableClasses, ∃ c ∈ classWitnesses,
    (c.nu1 + c.nu2 ≤ 2 ∧ ¬ (c.nu1 = 0 ∧ c.nu2 = 0)) ∧ c.Valid ∧ c.cls = k := by
  decide +kernel

theorem image_cls_choices : (choices.filter Config.Valid).image Config.cls = tableClasses := by
  apply Finset.Subset.antisymm
  · rw [Finset.image_subset_iff, choices_eq_map]; decide +kernel
  · intro k hk
    obtain ⟨c, -, hc, hv, rfl⟩ := classWitnesses_spec k hk
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨(mem_choices c).mpr hc, hv⟩)

/-- A rational with denominator other than `1` is not an integer. -/
theorem not_int_of_den_ne_one {g : ℚ} (h : g.den ≠ 1) : ¬ ∃ z : ℤ, g = z := by
  rintro ⟨z, rfl⟩
  exact h (Rat.den_intCast z)

end Census

open Census

/-! ### The rows -/

theorem sec54_405_proved : choices.card = 405 := by
  rw [choices_eq_map]; decide +kernel

theorem lem_5_8_proved :
    (choices.filter Config.Valid).card = 179 ∧ ((choices.filter Config.Valid).image Config.renamings).card = 49 ∧
      (choices.filter Config.Valid).image Config.cls = tableClasses ∧ tableClasses.card = 14 ∧
      ∀ c ∈ choices, ∀ c' ∈ c.renamings, c' ∈ choices ∧ (c'.Valid ↔ c.Valid) ∧ (c.Valid → c'.cls = c.cls) := by
  refine ⟨?_, ?_, image_cls_choices, by decide +kernel, renamings_keep⟩ <;> rw [choices_eq_map] <;>
    decide +kernel

theorem table_1_proved :
    (∀ e ∈ [((1, 1), 13), ((1/2, 1), 6), ((1, 2), 7), ((1/4, 1/2), 1), ((1/2, 3/4), 1), ((1/3, 2/3), 2),
        ((2/3, 4/3), 2), ((1/2, 2), 1), ((3/2, 2), 1), ((2, 2), 5), ((2, 3), 2), ((2, 4), 2), ((1/2, 1/2), 4),
        ((1/2, 3/2), 2)],
      ((choices.filter (fun c => c.Valid ∧ c.cls = (e : (ℚ × ℚ) × ℕ).1)).image Config.renamings).card = e.2) ∧
    (∀ e ∈ [((1/3, 2/3), 1), ((2/3, 4/3), 1), ((1/2, 1/2), 2), ((1/2, 3/2), 1)],
      ((choices.filter (fun c => c.Valid ∧ c.IsBlock ∧ c.cls = (e : (ℚ × ℚ) × ℕ).1)).image Config.renamings).card
        = e.2) ∧
    (∀ e ∈ [((1/2, 1/2), 2), ((1/2, 3/2), 1)],
      (openConfigs.filter (fun c => c.cls = (e : (ℚ × ℚ) × ℕ).1)).card = e.2) := by
  rw [choices_eq_map]; decide +kernel

theorem sec54_block_list_proved :
    (choices.filter (fun c => c.Valid ∧ c.IsBlock ∧ c.t 0 ≠ 1 ∧ c.t 1 ≠ 1)).image Config.renamings =
        ({⟨2, 2, 2, 2, 1, 1⟩, ⟨2, 0, 2, 0, 0, 1⟩, ⟨2, 1, 2, 0, 0, 1⟩, ⟨2, 1, 2, 0, 0, 2⟩, ⟨2, 0, 2, 0, 1, 1⟩} :
          Finset Config).image Config.renamings ∧
      (⟨2, 2, 2, 2, 1, 1⟩ : Config).cls = (1/2, 1/2) ∧ (⟨2, 0, 2, 0, 0, 1⟩ : Config).cls = (1/2, 1/2) ∧
      (⟨2, 1, 2, 0, 0, 1⟩ : Config).cls = (1/3, 2/3) ∧ (⟨2, 1, 2, 0, 0, 2⟩ : Config).cls = (2/3, 4/3) ∧
      (⟨2, 0, 2, 0, 1, 1⟩ : Config).cls = (1/2, 3/2) := by
  rw [choices_eq_map]; decide +kernel

theorem thm_5_9_remaining_six_proved :
    ((choices.filter (fun c => c.Valid ∧ c.t 0 ≠ 1 ∧ c.t 1 ≠ 1 ∧ ¬ c.IsBlock ∧
        (∀ o ∈ openConfigs, c ∉ o.renamings) ∧ c.cls ∉ ({(2, 2), (2, 3), (2, 4)} : Finset (ℚ × ℚ)))).image
        Config.renamings) =
      ({⟨2, 2, 2, 0, 1, 1⟩, ⟨2, 2, 2, 0, 0, 1⟩, ⟨2, 1, 0, 2, 0, 1⟩, ⟨2, 1, 0, 2, 0, 2⟩, ⟨1, 1, 2, 1, 1, 1⟩,
        ⟨1, 1, 2, 0, 1, 1⟩} : Finset Config).image Config.renamings ∧
      ((choices.filter (fun c => c.Valid ∧
        c.cls ∈ ({(2, 2), (2, 3), (2, 4)} : Finset (ℚ × ℚ)))).image Config.renamings).card = 9 := by
  rw [choices_eq_map]; decide +kernel

theorem count_46_of_49_proved :
    (((choices.filter Config.Valid).image Config.renamings).filter
        (fun o => ∀ c ∈ openConfigs, c.renamings ≠ o)).card = 46 ∧
      (openConfigs.image Config.renamings).card = 3 := by
  rw [choices_eq_map]; decide +kernel

theorem count_12_classes_proved :
    (tableClasses.filter (fun k => ∀ c ∈ openConfigs, c.cls ≠ k)).card = 12 := by
  decide +kernel

theorem sec6_three_configs_proved :
    (∀ c ∈ openConfigs, c ∈ choices ∧ c.Valid) ∧ (⟨2, 0, 0, 2, 0, 1⟩ : Config).cls = (1/2, 1/2) ∧
      (⟨2, 2, 0, 0, 0, 1⟩ : Config).cls = (1/2, 1/2) ∧ (⟨2, 0, 0, 2, 1, 1⟩ : Config).cls = (1/2, 3/2) := by
  rw [choices_eq_map]; decide +kernel

theorem prop_5_11_config_proved :
    (choices.filter (fun c => c.Valid ∧ c.cls = (1/2, 3/4))).image Config.renamings =
        {(⟨2, 2, 2, 0, 1, 1⟩ : Config).renamings} ∧
      (choices.filter (fun c => c.Valid ∧ c.cls = (1/4, 1/2))).image Config.renamings =
        {(⟨2, 2, 2, 0, 0, 1⟩ : Config).renamings} ∧
      (⟨2, 2, 2, 0, 1, 1⟩ : Config).t = ![3/4, 1/2] ∧ (⟨2, 2, 2, 0, 0, 1⟩ : Config).t = ![1/4, 1/2] ∧
      ∀ cf ∈ ({⟨2, 2, 2, 0, 1, 1⟩, ⟨2, 2, 2, 0, 0, 1⟩} : Finset Config),
        (∀ i, -1 < cf.t i - 1 ∧ cf.t i - 1 < 0) ∧
        ∀ g ∈ ({cf.t 0 - 1, cf.t 1 - 1, cf.t 0 - 1 + (cf.t 1 - 1), cf.t 0 - 1 - (cf.t 1 - 1)} : Finset ℚ),
          ¬ ∃ z : ℤ, g = z := by
  have key : ∀ cf ∈ ({⟨2, 2, 2, 0, 1, 1⟩, ⟨2, 2, 2, 0, 0, 1⟩} : Finset Config),
      (∀ i, -1 < cf.t i - 1 ∧ cf.t i - 1 < 0) ∧
      ∀ g ∈ ({cf.t 0 - 1, cf.t 1 - 1, cf.t 0 - 1 + (cf.t 1 - 1), cf.t 0 - 1 - (cf.t 1 - 1)} : Finset ℚ),
        g.den ≠ 1 := by
    decide +kernel
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel,
    fun cf hcf => ⟨(key cf hcf).1, fun g hg => not_int_of_den_ne_one ((key cf hcf).2 g hg)⟩⟩ <;>
    rw [choices_eq_map] <;> decide +kernel

theorem prop_5_12_config_proved :
    (⟨2, 1, 0, 2, 0, 1⟩ : Config).t = ![1/3, 2/3] ∧ (⟨2, 1, 0, 2, 0, 2⟩ : Config).t = ![2/3, 4/3] ∧
      (⟨2, 1, 0, 2, 0, 1⟩ : Config).cls = (1/3, 2/3) ∧ (⟨2, 1, 0, 2, 0, 2⟩ : Config).cls = (2/3, 4/3) ∧
      (⟨2, 1, 0, 2, 0, 1⟩ : Config).t 0 - 1 + ((⟨2, 1, 0, 2, 0, 1⟩ : Config).t 1 - 1) = -1 ∧
      (⟨2, 1, 0, 2, 0, 2⟩ : Config).t 0 - 1 + ((⟨2, 1, 0, 2, 0, 2⟩ : Config).t 1 - 1) = 0 ∧
      ∀ cf ∈ ({⟨2, 1, 0, 2, 0, 1⟩, ⟨2, 1, 0, 2, 0, 2⟩} : Finset Config),
        ∀ g ∈ ({cf.t 0 - 1, cf.t 1 - 1, cf.t 0 - 1 - (cf.t 1 - 1)} : Finset ℚ), ¬ ∃ z : ℤ, g = z := by
  have key : ∀ cf ∈ ({⟨2, 1, 0, 2, 0, 1⟩, ⟨2, 1, 0, 2, 0, 2⟩} : Finset Config),
      ∀ g ∈ ({cf.t 0 - 1, cf.t 1 - 1, cf.t 0 - 1 - (cf.t 1 - 1)} : Finset ℚ), g.den ≠ 1 := by
    decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun cf hcf g hg => not_int_of_den_ne_one (key cf hcf g hg)⟩ <;>
    decide +kernel

theorem prop_5_13_config_proved :
    (choices.filter (fun c => c.Valid ∧ c.cls = (1/2, 2))).image Config.renamings =
        {(⟨1, 1, 2, 1, 1, 1⟩ : Config).renamings} ∧
      (choices.filter (fun c => c.Valid ∧ c.cls = (3/2, 2))).image Config.renamings =
        {(⟨1, 1, 2, 0, 1, 1⟩ : Config).renamings} ∧
      (⟨1, 1, 2, 1, 1, 1⟩ : Config).t = ![1/2, 2] ∧ (⟨1, 1, 2, 0, 1, 1⟩ : Config).t = ![3/2, 2] := by
  rw [choices_eq_map]; decide +kernel

end CernyQE
