/-
CernyQE/Proofs/Census514/N6_01.lean — kernel check of the census of Proposition 5.14 at n = 6, configuration 1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Proofs.Census514.Search

namespace CernyQE
namespace Census514

/-! ### Configuration 1: `[0, 1, 0, 2, 1, 1]` -/

theorem N6_c1_0_0 : chunk 6 19 [0, 1, 0, 2, 1, 1] 0 0 = true := by decide +kernel
theorem N6_c1_0_1 : chunk 6 19 [0, 1, 0, 2, 1, 1] 0 1 = true := by decide +kernel
theorem N6_c1_0_2 : chunk 6 19 [0, 1, 0, 2, 1, 1] 0 2 = true := by decide +kernel
theorem N6_c1_0_3 : chunk 6 19 [0, 1, 0, 2, 1, 1] 0 3 = true := by decide +kernel
theorem N6_c1_0_4 : chunk 6 19 [0, 1, 0, 2, 1, 1] 0 4 = true := by decide +kernel
theorem N6_c1_0_5 : chunk 6 19 [0, 1, 0, 2, 1, 1] 0 5 = true := by decide +kernel
theorem N6_c1_1_0 : chunk 6 19 [0, 1, 0, 2, 1, 1] 1 0 = true := by decide +kernel
theorem N6_c1_1_1 : chunk 6 19 [0, 1, 0, 2, 1, 1] 1 1 = true := by decide +kernel
theorem N6_c1_1_2 : chunk 6 19 [0, 1, 0, 2, 1, 1] 1 2 = true := by decide +kernel
theorem N6_c1_1_3 : chunk 6 19 [0, 1, 0, 2, 1, 1] 1 3 = true := by decide +kernel
theorem N6_c1_1_4 : chunk 6 19 [0, 1, 0, 2, 1, 1] 1 4 = true := by decide +kernel
theorem N6_c1_1_5 : chunk 6 19 [0, 1, 0, 2, 1, 1] 1 5 = true := by decide +kernel
theorem N6_c1_2_0 : chunk 6 19 [0, 1, 0, 2, 1, 1] 2 0 = true := by decide +kernel
theorem N6_c1_2_1 : chunk 6 19 [0, 1, 0, 2, 1, 1] 2 1 = true := by decide +kernel
theorem N6_c1_2_2 : chunk 6 19 [0, 1, 0, 2, 1, 1] 2 2 = true := by decide +kernel
theorem N6_c1_2_3 : chunk 6 19 [0, 1, 0, 2, 1, 1] 2 3 = true := by decide +kernel
theorem N6_c1_2_4 : chunk 6 19 [0, 1, 0, 2, 1, 1] 2 4 = true := by decide +kernel
theorem N6_c1_2_5 : chunk 6 19 [0, 1, 0, 2, 1, 1] 2 5 = true := by decide +kernel
theorem N6_c1_3_0 : chunk 6 19 [0, 1, 0, 2, 1, 1] 3 0 = true := by decide +kernel
theorem N6_c1_3_1 : chunk 6 19 [0, 1, 0, 2, 1, 1] 3 1 = true := by decide +kernel
theorem N6_c1_3_2 : chunk 6 19 [0, 1, 0, 2, 1, 1] 3 2 = true := by decide +kernel
theorem N6_c1_3_3 : chunk 6 19 [0, 1, 0, 2, 1, 1] 3 3 = true := by decide +kernel
theorem N6_c1_3_4 : chunk 6 19 [0, 1, 0, 2, 1, 1] 3 4 = true := by decide +kernel
theorem N6_c1_3_5 : chunk 6 19 [0, 1, 0, 2, 1, 1] 3 5 = true := by decide +kernel
theorem N6_c1_4_0 : chunk 6 19 [0, 1, 0, 2, 1, 1] 4 0 = true := by decide +kernel
theorem N6_c1_4_1 : chunk 6 19 [0, 1, 0, 2, 1, 1] 4 1 = true := by decide +kernel
theorem N6_c1_4_2 : chunk 6 19 [0, 1, 0, 2, 1, 1] 4 2 = true := by decide +kernel
theorem N6_c1_4_3 : chunk 6 19 [0, 1, 0, 2, 1, 1] 4 3 = true := by decide +kernel
theorem N6_c1_4_4 : chunk 6 19 [0, 1, 0, 2, 1, 1] 4 4 = true := by decide +kernel
theorem N6_c1_4_5 : chunk 6 19 [0, 1, 0, 2, 1, 1] 4 5 = true := by decide +kernel
theorem N6_c1_5_0 : chunk 6 19 [0, 1, 0, 2, 1, 1] 5 0 = true := by decide +kernel
theorem N6_c1_5_1 : chunk 6 19 [0, 1, 0, 2, 1, 1] 5 1 = true := by decide +kernel
theorem N6_c1_5_2 : chunk 6 19 [0, 1, 0, 2, 1, 1] 5 2 = true := by decide +kernel
theorem N6_c1_5_3 : chunk 6 19 [0, 1, 0, 2, 1, 1] 5 3 = true := by decide +kernel
theorem N6_c1_5_4 : chunk 6 19 [0, 1, 0, 2, 1, 1] 5 4 = true := by decide +kernel
theorem N6_c1_5_5 : chunk 6 19 [0, 1, 0, 2, 1, 1] 5 5 = true := by decide +kernel

/-- Every chunk of configuration 1 at `n = 6`. -/
theorem N6_c1 : ∀ v₁, v₁ < 6 → ∀ v₂, v₂ < 6 → chunk 6 19 [0, 1, 0, 2, 1, 1] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N6_c1_0_0
  | 0, 1, _, _ => exact N6_c1_0_1
  | 0, 2, _, _ => exact N6_c1_0_2
  | 0, 3, _, _ => exact N6_c1_0_3
  | 0, 4, _, _ => exact N6_c1_0_4
  | 0, 5, _, _ => exact N6_c1_0_5
  | 1, 0, _, _ => exact N6_c1_1_0
  | 1, 1, _, _ => exact N6_c1_1_1
  | 1, 2, _, _ => exact N6_c1_1_2
  | 1, 3, _, _ => exact N6_c1_1_3
  | 1, 4, _, _ => exact N6_c1_1_4
  | 1, 5, _, _ => exact N6_c1_1_5
  | 2, 0, _, _ => exact N6_c1_2_0
  | 2, 1, _, _ => exact N6_c1_2_1
  | 2, 2, _, _ => exact N6_c1_2_2
  | 2, 3, _, _ => exact N6_c1_2_3
  | 2, 4, _, _ => exact N6_c1_2_4
  | 2, 5, _, _ => exact N6_c1_2_5
  | 3, 0, _, _ => exact N6_c1_3_0
  | 3, 1, _, _ => exact N6_c1_3_1
  | 3, 2, _, _ => exact N6_c1_3_2
  | 3, 3, _, _ => exact N6_c1_3_3
  | 3, 4, _, _ => exact N6_c1_3_4
  | 3, 5, _, _ => exact N6_c1_3_5
  | 4, 0, _, _ => exact N6_c1_4_0
  | 4, 1, _, _ => exact N6_c1_4_1
  | 4, 2, _, _ => exact N6_c1_4_2
  | 4, 3, _, _ => exact N6_c1_4_3
  | 4, 4, _, _ => exact N6_c1_4_4
  | 4, 5, _, _ => exact N6_c1_4_5
  | 5, 0, _, _ => exact N6_c1_5_0
  | 5, 1, _, _ => exact N6_c1_5_1
  | 5, 2, _, _ => exact N6_c1_5_2
  | 5, 3, _, _ => exact N6_c1_5_3
  | 5, 4, _, _ => exact N6_c1_5_4
  | 5, 5, _, _ => exact N6_c1_5_5
  | _ + 6, _, h, _ => exact absurd h (by omega)
  | _, _ + 6, _, h => exact absurd h (by omega)

end Census514
end CernyQE
