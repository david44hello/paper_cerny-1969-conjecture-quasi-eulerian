/-
Table 2 and the counts in the proof of Lemma 5.8.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Printed
import CernyQE.Proofs.Census

namespace CernyQE

/-- Table 2, tab_configs_float.tex:10-23 (included at tex:745). A printed (x1.a, x1.b, x2.a, x2.b; nu1, nu2) is the Config with these fields in this order; targets coded 0 = x_1, 1 = x_2, 2 = s (Defs/Binary.lean). -/
theorem table_2_configs_proved :
    let orbits := table2Rows.map (fun r => r.1.renamings)
    table2Rows.length = 49 ∧ (∀ r ∈ table2Rows, r.1 ∈ choices ∧ r.1.Valid ∧ r.1.cls = r.2) ∧
      orbits.Nodup ∧ orbits.toFinset = (choices.filter Config.Valid).image Config.renamings ∧
      (orbits.filter (fun o => o.card = 1)).length = 1 ∧
      (orbits.filter (fun o => o.card = 2)).length = 7 ∧
      (orbits.filter (fun o => o.card = 4)).length = 41 ∧ 1 + 7 * 2 + 41 * 4 = 179 :=
  by
  dsimp only
  have hrows : ∀ r ∈ table2Rows, r.1 ∈ choices ∧ r.1.Valid ∧ r.1.cls = r.2 := by
    simp_rw [Census.mem_choices]
    decide +kernel
  refine ⟨rfl, hrows, by decide +kernel, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, rfl⟩
  apply Finset.eq_of_subset_of_card_le
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨(hrows r hr).1, (hrows r hr).2.1⟩)
  · rw [lem_5_8_proved.2.1]
    decide +kernel

/-- Lemma 5.8, proof_classes.tex:4-9 (included at tex:719). The determinant, its zeros, the two coordinates of t, and their positivity. -/
theorem lem_5_8_delta_proved :
    ∀ cf ∈ choices,
    (∀ i j, cf.G i j = 2 * cf.Z i j) ∧ cf.delta = 4 * cf.det ∧
    0 ≤ cf.delta ∧ (cf.delta = 0 ↔ cf.closedException) ∧
    (cf.closedException ↔ cf.G 0 0 = 2 ∨ cf.G 1 1 = 2 ∨
      (cf.G 0 0 + cf.G 0 1 = 2 ∧ cf.G 1 0 + cf.G 1 1 = 2)) ∧
    (∀ i, cf.G i 0 + cf.G i 1 ≤ 2) ∧ (cf.delta ≠ 0 →
      cf.G 0 0 < 2 ∧ cf.G 1 1 < 2 ∧
      cf.t 0 = ((2 - cf.G 1 1) * cf.nu1 + cf.G 1 0 * cf.nu2) / cf.delta ∧
      cf.t 1 = (cf.G 0 1 * cf.nu1 + (2 - cf.G 0 0) * cf.nu2) / cf.delta ∧
      (0 < cf.t 0 ↔ 0 < cf.nu1 ∨ (0 < cf.nu2 ∧ 0 < cf.G 1 0)) ∧
      (0 < cf.t 1 ↔ 0 < cf.nu2 ∨ (0 < cf.nu1 ∧ 0 < cf.G 0 1))) :=
  by
  rw [Census.choices_eq_map]
  decide +kernel

/-- Lemma 5.8, proof_classes.tex:8-10 (included at tex:719). Counts of targets, including each of the five boundary pairs. -/
theorem lem_5_8_target_counts_proved :
    let targets := (Finset.univ : Finset TargetChoices)
    let nonsingular := targets.filter (fun v => (configWith v 1 1).delta ≠ 0)
    targets.card = 81 ∧ (targets.filter (fun v => (configWith v 1 1).closedException)).card = 26 ∧
      nonsingular.card = 55 ∧
      (nonsingular.filter (fun v => 0 < (configWith v 1 1).G 0 1)).card = 31 ∧
      (nonsingular.filter (fun v => 0 < (configWith v 1 1).G 1 0)).card = 31 ∧
      (targets.filter (fun v => (configWith v 1 1).Valid)).card = 55 ∧
      (∀ p ∈ ([(0,1), (1,0), (0,2), (2,0)] : List (ℕ × ℕ)),
        (targets.filter (fun v => (configWith v p.1 p.2).Valid)).card = 31) ∧
      55 + 4 * 31 = 179 :=
  by decide +kernel

/-- Lemma 5.8, proof_classes.tex:4-7 (included at tex:719). The expanded determinants agree with matrix determinants. -/
theorem lem_5_8_determinants_proved (cf : Config) :
    ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) - Matrix.of cf.G).det = cf.delta ∧
      (1 - cf.Z).det = cf.det ∧ cf.delta = 4 * cf.det := by
  constructor
  · simp [Matrix.det_fin_two, Config.delta, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply]
  constructor
  · simp [Matrix.det_fin_two, Config.det, Matrix.sub_apply, Matrix.one_apply]
    <;> ring
  · have hG (i j : Fin 2) : cf.G i j = 2 * cf.Z i j := by
      unfold Config.G Config.Z
      ring
    simp only [Config.delta, Config.det, hG]
    ring

/-- Lemma 5.8, proof_classes.tex:9-11 (included at tex:719). The two renamings are commuting involutions, and their four composites act distinctly. -/
theorem lem_5_8_renaming_action_proved :
    (∀ cf ∈ choices, cf.swapX.swapX = cf ∧ cf.swapL.swapL = cf ∧ cf.swapX.swapL = cf.swapL.swapX) ∧
      (∃ cf ∈ table2Rows, cf.1.renamings.card = 4) := by
  rw [Census.choices_eq_map]
  decide +kernel

end CernyQE
