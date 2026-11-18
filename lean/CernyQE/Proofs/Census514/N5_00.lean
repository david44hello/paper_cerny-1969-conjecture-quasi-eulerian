/-
CernyQE/Proofs/Census514/N5_00.lean — kernel check of the census of Proposition 5.14 at n = 5, all nine configurations.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Proofs.Census514.Search

namespace CernyQE
namespace Census514

/-! ### Configuration 0: `[0, 1, 0, 2, 0, 2]` -/

theorem N5_c0_0_0 : chunk 5 13 [0, 1, 0, 2, 0, 2] 0 0 = true := by decide +kernel
theorem N5_c0_0_1 : chunk 5 13 [0, 1, 0, 2, 0, 2] 0 1 = true := by decide +kernel
theorem N5_c0_0_2 : chunk 5 13 [0, 1, 0, 2, 0, 2] 0 2 = true := by decide +kernel
theorem N5_c0_0_3 : chunk 5 13 [0, 1, 0, 2, 0, 2] 0 3 = true := by decide +kernel
theorem N5_c0_0_4 : chunk 5 13 [0, 1, 0, 2, 0, 2] 0 4 = true := by decide +kernel
theorem N5_c0_1_0 : chunk 5 13 [0, 1, 0, 2, 0, 2] 1 0 = true := by decide +kernel
theorem N5_c0_1_1 : chunk 5 13 [0, 1, 0, 2, 0, 2] 1 1 = true := by decide +kernel
theorem N5_c0_1_2 : chunk 5 13 [0, 1, 0, 2, 0, 2] 1 2 = true := by decide +kernel
theorem N5_c0_1_3 : chunk 5 13 [0, 1, 0, 2, 0, 2] 1 3 = true := by decide +kernel
theorem N5_c0_1_4 : chunk 5 13 [0, 1, 0, 2, 0, 2] 1 4 = true := by decide +kernel
theorem N5_c0_2_0 : chunk 5 13 [0, 1, 0, 2, 0, 2] 2 0 = true := by decide +kernel
theorem N5_c0_2_1 : chunk 5 13 [0, 1, 0, 2, 0, 2] 2 1 = true := by decide +kernel
theorem N5_c0_2_2 : chunk 5 13 [0, 1, 0, 2, 0, 2] 2 2 = true := by decide +kernel
theorem N5_c0_2_3 : chunk 5 13 [0, 1, 0, 2, 0, 2] 2 3 = true := by decide +kernel
theorem N5_c0_2_4 : chunk 5 13 [0, 1, 0, 2, 0, 2] 2 4 = true := by decide +kernel
theorem N5_c0_3_0 : chunk 5 13 [0, 1, 0, 2, 0, 2] 3 0 = true := by decide +kernel
theorem N5_c0_3_1 : chunk 5 13 [0, 1, 0, 2, 0, 2] 3 1 = true := by decide +kernel
theorem N5_c0_3_2 : chunk 5 13 [0, 1, 0, 2, 0, 2] 3 2 = true := by decide +kernel
theorem N5_c0_3_3 : chunk 5 13 [0, 1, 0, 2, 0, 2] 3 3 = true := by decide +kernel
theorem N5_c0_3_4 : chunk 5 13 [0, 1, 0, 2, 0, 2] 3 4 = true := by decide +kernel
theorem N5_c0_4_0 : chunk 5 13 [0, 1, 0, 2, 0, 2] 4 0 = true := by decide +kernel
theorem N5_c0_4_1 : chunk 5 13 [0, 1, 0, 2, 0, 2] 4 1 = true := by decide +kernel
theorem N5_c0_4_2 : chunk 5 13 [0, 1, 0, 2, 0, 2] 4 2 = true := by decide +kernel
theorem N5_c0_4_3 : chunk 5 13 [0, 1, 0, 2, 0, 2] 4 3 = true := by decide +kernel
theorem N5_c0_4_4 : chunk 5 13 [0, 1, 0, 2, 0, 2] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 0 at `n = 5`. -/
theorem N5_c0 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [0, 1, 0, 2, 0, 2] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c0_0_0
  | 0, 1, _, _ => exact N5_c0_0_1
  | 0, 2, _, _ => exact N5_c0_0_2
  | 0, 3, _, _ => exact N5_c0_0_3
  | 0, 4, _, _ => exact N5_c0_0_4
  | 1, 0, _, _ => exact N5_c0_1_0
  | 1, 1, _, _ => exact N5_c0_1_1
  | 1, 2, _, _ => exact N5_c0_1_2
  | 1, 3, _, _ => exact N5_c0_1_3
  | 1, 4, _, _ => exact N5_c0_1_4
  | 2, 0, _, _ => exact N5_c0_2_0
  | 2, 1, _, _ => exact N5_c0_2_1
  | 2, 2, _, _ => exact N5_c0_2_2
  | 2, 3, _, _ => exact N5_c0_2_3
  | 2, 4, _, _ => exact N5_c0_2_4
  | 3, 0, _, _ => exact N5_c0_3_0
  | 3, 1, _, _ => exact N5_c0_3_1
  | 3, 2, _, _ => exact N5_c0_3_2
  | 3, 3, _, _ => exact N5_c0_3_3
  | 3, 4, _, _ => exact N5_c0_3_4
  | 4, 0, _, _ => exact N5_c0_4_0
  | 4, 1, _, _ => exact N5_c0_4_1
  | 4, 2, _, _ => exact N5_c0_4_2
  | 4, 3, _, _ => exact N5_c0_4_3
  | 4, 4, _, _ => exact N5_c0_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

/-! ### Configuration 1: `[0, 1, 0, 2, 1, 1]` -/

theorem N5_c1_0_0 : chunk 5 13 [0, 1, 0, 2, 1, 1] 0 0 = true := by decide +kernel
theorem N5_c1_0_1 : chunk 5 13 [0, 1, 0, 2, 1, 1] 0 1 = true := by decide +kernel
theorem N5_c1_0_2 : chunk 5 13 [0, 1, 0, 2, 1, 1] 0 2 = true := by decide +kernel
theorem N5_c1_0_3 : chunk 5 13 [0, 1, 0, 2, 1, 1] 0 3 = true := by decide +kernel
theorem N5_c1_0_4 : chunk 5 13 [0, 1, 0, 2, 1, 1] 0 4 = true := by decide +kernel
theorem N5_c1_1_0 : chunk 5 13 [0, 1, 0, 2, 1, 1] 1 0 = true := by decide +kernel
theorem N5_c1_1_1 : chunk 5 13 [0, 1, 0, 2, 1, 1] 1 1 = true := by decide +kernel
theorem N5_c1_1_2 : chunk 5 13 [0, 1, 0, 2, 1, 1] 1 2 = true := by decide +kernel
theorem N5_c1_1_3 : chunk 5 13 [0, 1, 0, 2, 1, 1] 1 3 = true := by decide +kernel
theorem N5_c1_1_4 : chunk 5 13 [0, 1, 0, 2, 1, 1] 1 4 = true := by decide +kernel
theorem N5_c1_2_0 : chunk 5 13 [0, 1, 0, 2, 1, 1] 2 0 = true := by decide +kernel
theorem N5_c1_2_1 : chunk 5 13 [0, 1, 0, 2, 1, 1] 2 1 = true := by decide +kernel
theorem N5_c1_2_2 : chunk 5 13 [0, 1, 0, 2, 1, 1] 2 2 = true := by decide +kernel
theorem N5_c1_2_3 : chunk 5 13 [0, 1, 0, 2, 1, 1] 2 3 = true := by decide +kernel
theorem N5_c1_2_4 : chunk 5 13 [0, 1, 0, 2, 1, 1] 2 4 = true := by decide +kernel
theorem N5_c1_3_0 : chunk 5 13 [0, 1, 0, 2, 1, 1] 3 0 = true := by decide +kernel
theorem N5_c1_3_1 : chunk 5 13 [0, 1, 0, 2, 1, 1] 3 1 = true := by decide +kernel
theorem N5_c1_3_2 : chunk 5 13 [0, 1, 0, 2, 1, 1] 3 2 = true := by decide +kernel
theorem N5_c1_3_3 : chunk 5 13 [0, 1, 0, 2, 1, 1] 3 3 = true := by decide +kernel
theorem N5_c1_3_4 : chunk 5 13 [0, 1, 0, 2, 1, 1] 3 4 = true := by decide +kernel
theorem N5_c1_4_0 : chunk 5 13 [0, 1, 0, 2, 1, 1] 4 0 = true := by decide +kernel
theorem N5_c1_4_1 : chunk 5 13 [0, 1, 0, 2, 1, 1] 4 1 = true := by decide +kernel
theorem N5_c1_4_2 : chunk 5 13 [0, 1, 0, 2, 1, 1] 4 2 = true := by decide +kernel
theorem N5_c1_4_3 : chunk 5 13 [0, 1, 0, 2, 1, 1] 4 3 = true := by decide +kernel
theorem N5_c1_4_4 : chunk 5 13 [0, 1, 0, 2, 1, 1] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 1 at `n = 5`. -/
theorem N5_c1 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [0, 1, 0, 2, 1, 1] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c1_0_0
  | 0, 1, _, _ => exact N5_c1_0_1
  | 0, 2, _, _ => exact N5_c1_0_2
  | 0, 3, _, _ => exact N5_c1_0_3
  | 0, 4, _, _ => exact N5_c1_0_4
  | 1, 0, _, _ => exact N5_c1_1_0
  | 1, 1, _, _ => exact N5_c1_1_1
  | 1, 2, _, _ => exact N5_c1_1_2
  | 1, 3, _, _ => exact N5_c1_1_3
  | 1, 4, _, _ => exact N5_c1_1_4
  | 2, 0, _, _ => exact N5_c1_2_0
  | 2, 1, _, _ => exact N5_c1_2_1
  | 2, 2, _, _ => exact N5_c1_2_2
  | 2, 3, _, _ => exact N5_c1_2_3
  | 2, 4, _, _ => exact N5_c1_2_4
  | 3, 0, _, _ => exact N5_c1_3_0
  | 3, 1, _, _ => exact N5_c1_3_1
  | 3, 2, _, _ => exact N5_c1_3_2
  | 3, 3, _, _ => exact N5_c1_3_3
  | 3, 4, _, _ => exact N5_c1_3_4
  | 4, 0, _, _ => exact N5_c1_4_0
  | 4, 1, _, _ => exact N5_c1_4_1
  | 4, 2, _, _ => exact N5_c1_4_2
  | 4, 3, _, _ => exact N5_c1_4_3
  | 4, 4, _, _ => exact N5_c1_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

/-! ### Configuration 2: `[0, 1, 0, 2, 2, 0]` -/

theorem N5_c2_0_0 : chunk 5 13 [0, 1, 0, 2, 2, 0] 0 0 = true := by decide +kernel
theorem N5_c2_0_1 : chunk 5 13 [0, 1, 0, 2, 2, 0] 0 1 = true := by decide +kernel
theorem N5_c2_0_2 : chunk 5 13 [0, 1, 0, 2, 2, 0] 0 2 = true := by decide +kernel
theorem N5_c2_0_3 : chunk 5 13 [0, 1, 0, 2, 2, 0] 0 3 = true := by decide +kernel
theorem N5_c2_0_4 : chunk 5 13 [0, 1, 0, 2, 2, 0] 0 4 = true := by decide +kernel
theorem N5_c2_1_0 : chunk 5 13 [0, 1, 0, 2, 2, 0] 1 0 = true := by decide +kernel
theorem N5_c2_1_1 : chunk 5 13 [0, 1, 0, 2, 2, 0] 1 1 = true := by decide +kernel
theorem N5_c2_1_2 : chunk 5 13 [0, 1, 0, 2, 2, 0] 1 2 = true := by decide +kernel
theorem N5_c2_1_3 : chunk 5 13 [0, 1, 0, 2, 2, 0] 1 3 = true := by decide +kernel
theorem N5_c2_1_4 : chunk 5 13 [0, 1, 0, 2, 2, 0] 1 4 = true := by decide +kernel
theorem N5_c2_2_0 : chunk 5 13 [0, 1, 0, 2, 2, 0] 2 0 = true := by decide +kernel
theorem N5_c2_2_1 : chunk 5 13 [0, 1, 0, 2, 2, 0] 2 1 = true := by decide +kernel
theorem N5_c2_2_2 : chunk 5 13 [0, 1, 0, 2, 2, 0] 2 2 = true := by decide +kernel
theorem N5_c2_2_3 : chunk 5 13 [0, 1, 0, 2, 2, 0] 2 3 = true := by decide +kernel
theorem N5_c2_2_4 : chunk 5 13 [0, 1, 0, 2, 2, 0] 2 4 = true := by decide +kernel
theorem N5_c2_3_0 : chunk 5 13 [0, 1, 0, 2, 2, 0] 3 0 = true := by decide +kernel
theorem N5_c2_3_1 : chunk 5 13 [0, 1, 0, 2, 2, 0] 3 1 = true := by decide +kernel
theorem N5_c2_3_2 : chunk 5 13 [0, 1, 0, 2, 2, 0] 3 2 = true := by decide +kernel
theorem N5_c2_3_3 : chunk 5 13 [0, 1, 0, 2, 2, 0] 3 3 = true := by decide +kernel
theorem N5_c2_3_4 : chunk 5 13 [0, 1, 0, 2, 2, 0] 3 4 = true := by decide +kernel
theorem N5_c2_4_0 : chunk 5 13 [0, 1, 0, 2, 2, 0] 4 0 = true := by decide +kernel
theorem N5_c2_4_1 : chunk 5 13 [0, 1, 0, 2, 2, 0] 4 1 = true := by decide +kernel
theorem N5_c2_4_2 : chunk 5 13 [0, 1, 0, 2, 2, 0] 4 2 = true := by decide +kernel
theorem N5_c2_4_3 : chunk 5 13 [0, 1, 0, 2, 2, 0] 4 3 = true := by decide +kernel
theorem N5_c2_4_4 : chunk 5 13 [0, 1, 0, 2, 2, 0] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 2 at `n = 5`. -/
theorem N5_c2 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [0, 1, 0, 2, 2, 0] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c2_0_0
  | 0, 1, _, _ => exact N5_c2_0_1
  | 0, 2, _, _ => exact N5_c2_0_2
  | 0, 3, _, _ => exact N5_c2_0_3
  | 0, 4, _, _ => exact N5_c2_0_4
  | 1, 0, _, _ => exact N5_c2_1_0
  | 1, 1, _, _ => exact N5_c2_1_1
  | 1, 2, _, _ => exact N5_c2_1_2
  | 1, 3, _, _ => exact N5_c2_1_3
  | 1, 4, _, _ => exact N5_c2_1_4
  | 2, 0, _, _ => exact N5_c2_2_0
  | 2, 1, _, _ => exact N5_c2_2_1
  | 2, 2, _, _ => exact N5_c2_2_2
  | 2, 3, _, _ => exact N5_c2_2_3
  | 2, 4, _, _ => exact N5_c2_2_4
  | 3, 0, _, _ => exact N5_c2_3_0
  | 3, 1, _, _ => exact N5_c2_3_1
  | 3, 2, _, _ => exact N5_c2_3_2
  | 3, 3, _, _ => exact N5_c2_3_3
  | 3, 4, _, _ => exact N5_c2_3_4
  | 4, 0, _, _ => exact N5_c2_4_0
  | 4, 1, _, _ => exact N5_c2_4_1
  | 4, 2, _, _ => exact N5_c2_4_2
  | 4, 3, _, _ => exact N5_c2_4_3
  | 4, 4, _, _ => exact N5_c2_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

/-! ### Configuration 3: `[0, 1, 1, 2, 2, 0]` -/

theorem N5_c3_0_0 : chunk 5 13 [0, 1, 1, 2, 2, 0] 0 0 = true := by decide +kernel
theorem N5_c3_0_1 : chunk 5 13 [0, 1, 1, 2, 2, 0] 0 1 = true := by decide +kernel
theorem N5_c3_0_2 : chunk 5 13 [0, 1, 1, 2, 2, 0] 0 2 = true := by decide +kernel
theorem N5_c3_0_3 : chunk 5 13 [0, 1, 1, 2, 2, 0] 0 3 = true := by decide +kernel
theorem N5_c3_0_4 : chunk 5 13 [0, 1, 1, 2, 2, 0] 0 4 = true := by decide +kernel
theorem N5_c3_1_0 : chunk 5 13 [0, 1, 1, 2, 2, 0] 1 0 = true := by decide +kernel
theorem N5_c3_1_1 : chunk 5 13 [0, 1, 1, 2, 2, 0] 1 1 = true := by decide +kernel
theorem N5_c3_1_2 : chunk 5 13 [0, 1, 1, 2, 2, 0] 1 2 = true := by decide +kernel
theorem N5_c3_1_3 : chunk 5 13 [0, 1, 1, 2, 2, 0] 1 3 = true := by decide +kernel
theorem N5_c3_1_4 : chunk 5 13 [0, 1, 1, 2, 2, 0] 1 4 = true := by decide +kernel
theorem N5_c3_2_0 : chunk 5 13 [0, 1, 1, 2, 2, 0] 2 0 = true := by decide +kernel
theorem N5_c3_2_1 : chunk 5 13 [0, 1, 1, 2, 2, 0] 2 1 = true := by decide +kernel
theorem N5_c3_2_2 : chunk 5 13 [0, 1, 1, 2, 2, 0] 2 2 = true := by decide +kernel
theorem N5_c3_2_3 : chunk 5 13 [0, 1, 1, 2, 2, 0] 2 3 = true := by decide +kernel
theorem N5_c3_2_4 : chunk 5 13 [0, 1, 1, 2, 2, 0] 2 4 = true := by decide +kernel
theorem N5_c3_3_0 : chunk 5 13 [0, 1, 1, 2, 2, 0] 3 0 = true := by decide +kernel
theorem N5_c3_3_1 : chunk 5 13 [0, 1, 1, 2, 2, 0] 3 1 = true := by decide +kernel
theorem N5_c3_3_2 : chunk 5 13 [0, 1, 1, 2, 2, 0] 3 2 = true := by decide +kernel
theorem N5_c3_3_3 : chunk 5 13 [0, 1, 1, 2, 2, 0] 3 3 = true := by decide +kernel
theorem N5_c3_3_4 : chunk 5 13 [0, 1, 1, 2, 2, 0] 3 4 = true := by decide +kernel
theorem N5_c3_4_0 : chunk 5 13 [0, 1, 1, 2, 2, 0] 4 0 = true := by decide +kernel
theorem N5_c3_4_1 : chunk 5 13 [0, 1, 1, 2, 2, 0] 4 1 = true := by decide +kernel
theorem N5_c3_4_2 : chunk 5 13 [0, 1, 1, 2, 2, 0] 4 2 = true := by decide +kernel
theorem N5_c3_4_3 : chunk 5 13 [0, 1, 1, 2, 2, 0] 4 3 = true := by decide +kernel
theorem N5_c3_4_4 : chunk 5 13 [0, 1, 1, 2, 2, 0] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 3 at `n = 5`. -/
theorem N5_c3 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [0, 1, 1, 2, 2, 0] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c3_0_0
  | 0, 1, _, _ => exact N5_c3_0_1
  | 0, 2, _, _ => exact N5_c3_0_2
  | 0, 3, _, _ => exact N5_c3_0_3
  | 0, 4, _, _ => exact N5_c3_0_4
  | 1, 0, _, _ => exact N5_c3_1_0
  | 1, 1, _, _ => exact N5_c3_1_1
  | 1, 2, _, _ => exact N5_c3_1_2
  | 1, 3, _, _ => exact N5_c3_1_3
  | 1, 4, _, _ => exact N5_c3_1_4
  | 2, 0, _, _ => exact N5_c3_2_0
  | 2, 1, _, _ => exact N5_c3_2_1
  | 2, 2, _, _ => exact N5_c3_2_2
  | 2, 3, _, _ => exact N5_c3_2_3
  | 2, 4, _, _ => exact N5_c3_2_4
  | 3, 0, _, _ => exact N5_c3_3_0
  | 3, 1, _, _ => exact N5_c3_3_1
  | 3, 2, _, _ => exact N5_c3_3_2
  | 3, 3, _, _ => exact N5_c3_3_3
  | 3, 4, _, _ => exact N5_c3_3_4
  | 4, 0, _, _ => exact N5_c3_4_0
  | 4, 1, _, _ => exact N5_c3_4_1
  | 4, 2, _, _ => exact N5_c3_4_2
  | 4, 3, _, _ => exact N5_c3_4_3
  | 4, 4, _, _ => exact N5_c3_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

/-! ### Configuration 4: `[0, 1, 2, 0, 0, 2]` -/

theorem N5_c4_0_0 : chunk 5 13 [0, 1, 2, 0, 0, 2] 0 0 = true := by decide +kernel
theorem N5_c4_0_1 : chunk 5 13 [0, 1, 2, 0, 0, 2] 0 1 = true := by decide +kernel
theorem N5_c4_0_2 : chunk 5 13 [0, 1, 2, 0, 0, 2] 0 2 = true := by decide +kernel
theorem N5_c4_0_3 : chunk 5 13 [0, 1, 2, 0, 0, 2] 0 3 = true := by decide +kernel
theorem N5_c4_0_4 : chunk 5 13 [0, 1, 2, 0, 0, 2] 0 4 = true := by decide +kernel
theorem N5_c4_1_0 : chunk 5 13 [0, 1, 2, 0, 0, 2] 1 0 = true := by decide +kernel
theorem N5_c4_1_1 : chunk 5 13 [0, 1, 2, 0, 0, 2] 1 1 = true := by decide +kernel
theorem N5_c4_1_2 : chunk 5 13 [0, 1, 2, 0, 0, 2] 1 2 = true := by decide +kernel
theorem N5_c4_1_3 : chunk 5 13 [0, 1, 2, 0, 0, 2] 1 3 = true := by decide +kernel
theorem N5_c4_1_4 : chunk 5 13 [0, 1, 2, 0, 0, 2] 1 4 = true := by decide +kernel
theorem N5_c4_2_0 : chunk 5 13 [0, 1, 2, 0, 0, 2] 2 0 = true := by decide +kernel
theorem N5_c4_2_1 : chunk 5 13 [0, 1, 2, 0, 0, 2] 2 1 = true := by decide +kernel
theorem N5_c4_2_2 : chunk 5 13 [0, 1, 2, 0, 0, 2] 2 2 = true := by decide +kernel
theorem N5_c4_2_3 : chunk 5 13 [0, 1, 2, 0, 0, 2] 2 3 = true := by decide +kernel
theorem N5_c4_2_4 : chunk 5 13 [0, 1, 2, 0, 0, 2] 2 4 = true := by decide +kernel
theorem N5_c4_3_0 : chunk 5 13 [0, 1, 2, 0, 0, 2] 3 0 = true := by decide +kernel
theorem N5_c4_3_1 : chunk 5 13 [0, 1, 2, 0, 0, 2] 3 1 = true := by decide +kernel
theorem N5_c4_3_2 : chunk 5 13 [0, 1, 2, 0, 0, 2] 3 2 = true := by decide +kernel
theorem N5_c4_3_3 : chunk 5 13 [0, 1, 2, 0, 0, 2] 3 3 = true := by decide +kernel
theorem N5_c4_3_4 : chunk 5 13 [0, 1, 2, 0, 0, 2] 3 4 = true := by decide +kernel
theorem N5_c4_4_0 : chunk 5 13 [0, 1, 2, 0, 0, 2] 4 0 = true := by decide +kernel
theorem N5_c4_4_1 : chunk 5 13 [0, 1, 2, 0, 0, 2] 4 1 = true := by decide +kernel
theorem N5_c4_4_2 : chunk 5 13 [0, 1, 2, 0, 0, 2] 4 2 = true := by decide +kernel
theorem N5_c4_4_3 : chunk 5 13 [0, 1, 2, 0, 0, 2] 4 3 = true := by decide +kernel
theorem N5_c4_4_4 : chunk 5 13 [0, 1, 2, 0, 0, 2] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 4 at `n = 5`. -/
theorem N5_c4 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [0, 1, 2, 0, 0, 2] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c4_0_0
  | 0, 1, _, _ => exact N5_c4_0_1
  | 0, 2, _, _ => exact N5_c4_0_2
  | 0, 3, _, _ => exact N5_c4_0_3
  | 0, 4, _, _ => exact N5_c4_0_4
  | 1, 0, _, _ => exact N5_c4_1_0
  | 1, 1, _, _ => exact N5_c4_1_1
  | 1, 2, _, _ => exact N5_c4_1_2
  | 1, 3, _, _ => exact N5_c4_1_3
  | 1, 4, _, _ => exact N5_c4_1_4
  | 2, 0, _, _ => exact N5_c4_2_0
  | 2, 1, _, _ => exact N5_c4_2_1
  | 2, 2, _, _ => exact N5_c4_2_2
  | 2, 3, _, _ => exact N5_c4_2_3
  | 2, 4, _, _ => exact N5_c4_2_4
  | 3, 0, _, _ => exact N5_c4_3_0
  | 3, 1, _, _ => exact N5_c4_3_1
  | 3, 2, _, _ => exact N5_c4_3_2
  | 3, 3, _, _ => exact N5_c4_3_3
  | 3, 4, _, _ => exact N5_c4_3_4
  | 4, 0, _, _ => exact N5_c4_4_0
  | 4, 1, _, _ => exact N5_c4_4_1
  | 4, 2, _, _ => exact N5_c4_4_2
  | 4, 3, _, _ => exact N5_c4_4_3
  | 4, 4, _, _ => exact N5_c4_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

/-! ### Configuration 5: `[0, 1, 2, 0, 1, 1]` -/

theorem N5_c5_0_0 : chunk 5 13 [0, 1, 2, 0, 1, 1] 0 0 = true := by decide +kernel
theorem N5_c5_0_1 : chunk 5 13 [0, 1, 2, 0, 1, 1] 0 1 = true := by decide +kernel
theorem N5_c5_0_2 : chunk 5 13 [0, 1, 2, 0, 1, 1] 0 2 = true := by decide +kernel
theorem N5_c5_0_3 : chunk 5 13 [0, 1, 2, 0, 1, 1] 0 3 = true := by decide +kernel
theorem N5_c5_0_4 : chunk 5 13 [0, 1, 2, 0, 1, 1] 0 4 = true := by decide +kernel
theorem N5_c5_1_0 : chunk 5 13 [0, 1, 2, 0, 1, 1] 1 0 = true := by decide +kernel
theorem N5_c5_1_1 : chunk 5 13 [0, 1, 2, 0, 1, 1] 1 1 = true := by decide +kernel
theorem N5_c5_1_2 : chunk 5 13 [0, 1, 2, 0, 1, 1] 1 2 = true := by decide +kernel
theorem N5_c5_1_3 : chunk 5 13 [0, 1, 2, 0, 1, 1] 1 3 = true := by decide +kernel
theorem N5_c5_1_4 : chunk 5 13 [0, 1, 2, 0, 1, 1] 1 4 = true := by decide +kernel
theorem N5_c5_2_0 : chunk 5 13 [0, 1, 2, 0, 1, 1] 2 0 = true := by decide +kernel
theorem N5_c5_2_1 : chunk 5 13 [0, 1, 2, 0, 1, 1] 2 1 = true := by decide +kernel
theorem N5_c5_2_2 : chunk 5 13 [0, 1, 2, 0, 1, 1] 2 2 = true := by decide +kernel
theorem N5_c5_2_3 : chunk 5 13 [0, 1, 2, 0, 1, 1] 2 3 = true := by decide +kernel
theorem N5_c5_2_4 : chunk 5 13 [0, 1, 2, 0, 1, 1] 2 4 = true := by decide +kernel
theorem N5_c5_3_0 : chunk 5 13 [0, 1, 2, 0, 1, 1] 3 0 = true := by decide +kernel
theorem N5_c5_3_1 : chunk 5 13 [0, 1, 2, 0, 1, 1] 3 1 = true := by decide +kernel
theorem N5_c5_3_2 : chunk 5 13 [0, 1, 2, 0, 1, 1] 3 2 = true := by decide +kernel
theorem N5_c5_3_3 : chunk 5 13 [0, 1, 2, 0, 1, 1] 3 3 = true := by decide +kernel
theorem N5_c5_3_4 : chunk 5 13 [0, 1, 2, 0, 1, 1] 3 4 = true := by decide +kernel
theorem N5_c5_4_0 : chunk 5 13 [0, 1, 2, 0, 1, 1] 4 0 = true := by decide +kernel
theorem N5_c5_4_1 : chunk 5 13 [0, 1, 2, 0, 1, 1] 4 1 = true := by decide +kernel
theorem N5_c5_4_2 : chunk 5 13 [0, 1, 2, 0, 1, 1] 4 2 = true := by decide +kernel
theorem N5_c5_4_3 : chunk 5 13 [0, 1, 2, 0, 1, 1] 4 3 = true := by decide +kernel
theorem N5_c5_4_4 : chunk 5 13 [0, 1, 2, 0, 1, 1] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 5 at `n = 5`. -/
theorem N5_c5 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [0, 1, 2, 0, 1, 1] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c5_0_0
  | 0, 1, _, _ => exact N5_c5_0_1
  | 0, 2, _, _ => exact N5_c5_0_2
  | 0, 3, _, _ => exact N5_c5_0_3
  | 0, 4, _, _ => exact N5_c5_0_4
  | 1, 0, _, _ => exact N5_c5_1_0
  | 1, 1, _, _ => exact N5_c5_1_1
  | 1, 2, _, _ => exact N5_c5_1_2
  | 1, 3, _, _ => exact N5_c5_1_3
  | 1, 4, _, _ => exact N5_c5_1_4
  | 2, 0, _, _ => exact N5_c5_2_0
  | 2, 1, _, _ => exact N5_c5_2_1
  | 2, 2, _, _ => exact N5_c5_2_2
  | 2, 3, _, _ => exact N5_c5_2_3
  | 2, 4, _, _ => exact N5_c5_2_4
  | 3, 0, _, _ => exact N5_c5_3_0
  | 3, 1, _, _ => exact N5_c5_3_1
  | 3, 2, _, _ => exact N5_c5_3_2
  | 3, 3, _, _ => exact N5_c5_3_3
  | 3, 4, _, _ => exact N5_c5_3_4
  | 4, 0, _, _ => exact N5_c5_4_0
  | 4, 1, _, _ => exact N5_c5_4_1
  | 4, 2, _, _ => exact N5_c5_4_2
  | 4, 3, _, _ => exact N5_c5_4_3
  | 4, 4, _, _ => exact N5_c5_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

/-! ### Configuration 6: `[0, 1, 2, 0, 2, 0]` -/

theorem N5_c6_0_0 : chunk 5 13 [0, 1, 2, 0, 2, 0] 0 0 = true := by decide +kernel
theorem N5_c6_0_1 : chunk 5 13 [0, 1, 2, 0, 2, 0] 0 1 = true := by decide +kernel
theorem N5_c6_0_2 : chunk 5 13 [0, 1, 2, 0, 2, 0] 0 2 = true := by decide +kernel
theorem N5_c6_0_3 : chunk 5 13 [0, 1, 2, 0, 2, 0] 0 3 = true := by decide +kernel
theorem N5_c6_0_4 : chunk 5 13 [0, 1, 2, 0, 2, 0] 0 4 = true := by decide +kernel
theorem N5_c6_1_0 : chunk 5 13 [0, 1, 2, 0, 2, 0] 1 0 = true := by decide +kernel
theorem N5_c6_1_1 : chunk 5 13 [0, 1, 2, 0, 2, 0] 1 1 = true := by decide +kernel
theorem N5_c6_1_2 : chunk 5 13 [0, 1, 2, 0, 2, 0] 1 2 = true := by decide +kernel
theorem N5_c6_1_3 : chunk 5 13 [0, 1, 2, 0, 2, 0] 1 3 = true := by decide +kernel
theorem N5_c6_1_4 : chunk 5 13 [0, 1, 2, 0, 2, 0] 1 4 = true := by decide +kernel
theorem N5_c6_2_0 : chunk 5 13 [0, 1, 2, 0, 2, 0] 2 0 = true := by decide +kernel
theorem N5_c6_2_1 : chunk 5 13 [0, 1, 2, 0, 2, 0] 2 1 = true := by decide +kernel
theorem N5_c6_2_2 : chunk 5 13 [0, 1, 2, 0, 2, 0] 2 2 = true := by decide +kernel
theorem N5_c6_2_3 : chunk 5 13 [0, 1, 2, 0, 2, 0] 2 3 = true := by decide +kernel
theorem N5_c6_2_4 : chunk 5 13 [0, 1, 2, 0, 2, 0] 2 4 = true := by decide +kernel
theorem N5_c6_3_0 : chunk 5 13 [0, 1, 2, 0, 2, 0] 3 0 = true := by decide +kernel
theorem N5_c6_3_1 : chunk 5 13 [0, 1, 2, 0, 2, 0] 3 1 = true := by decide +kernel
theorem N5_c6_3_2 : chunk 5 13 [0, 1, 2, 0, 2, 0] 3 2 = true := by decide +kernel
theorem N5_c6_3_3 : chunk 5 13 [0, 1, 2, 0, 2, 0] 3 3 = true := by decide +kernel
theorem N5_c6_3_4 : chunk 5 13 [0, 1, 2, 0, 2, 0] 3 4 = true := by decide +kernel
theorem N5_c6_4_0 : chunk 5 13 [0, 1, 2, 0, 2, 0] 4 0 = true := by decide +kernel
theorem N5_c6_4_1 : chunk 5 13 [0, 1, 2, 0, 2, 0] 4 1 = true := by decide +kernel
theorem N5_c6_4_2 : chunk 5 13 [0, 1, 2, 0, 2, 0] 4 2 = true := by decide +kernel
theorem N5_c6_4_3 : chunk 5 13 [0, 1, 2, 0, 2, 0] 4 3 = true := by decide +kernel
theorem N5_c6_4_4 : chunk 5 13 [0, 1, 2, 0, 2, 0] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 6 at `n = 5`. -/
theorem N5_c6 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [0, 1, 2, 0, 2, 0] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c6_0_0
  | 0, 1, _, _ => exact N5_c6_0_1
  | 0, 2, _, _ => exact N5_c6_0_2
  | 0, 3, _, _ => exact N5_c6_0_3
  | 0, 4, _, _ => exact N5_c6_0_4
  | 1, 0, _, _ => exact N5_c6_1_0
  | 1, 1, _, _ => exact N5_c6_1_1
  | 1, 2, _, _ => exact N5_c6_1_2
  | 1, 3, _, _ => exact N5_c6_1_3
  | 1, 4, _, _ => exact N5_c6_1_4
  | 2, 0, _, _ => exact N5_c6_2_0
  | 2, 1, _, _ => exact N5_c6_2_1
  | 2, 2, _, _ => exact N5_c6_2_2
  | 2, 3, _, _ => exact N5_c6_2_3
  | 2, 4, _, _ => exact N5_c6_2_4
  | 3, 0, _, _ => exact N5_c6_3_0
  | 3, 1, _, _ => exact N5_c6_3_1
  | 3, 2, _, _ => exact N5_c6_3_2
  | 3, 3, _, _ => exact N5_c6_3_3
  | 3, 4, _, _ => exact N5_c6_3_4
  | 4, 0, _, _ => exact N5_c6_4_0
  | 4, 1, _, _ => exact N5_c6_4_1
  | 4, 2, _, _ => exact N5_c6_4_2
  | 4, 3, _, _ => exact N5_c6_4_3
  | 4, 4, _, _ => exact N5_c6_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

/-! ### Configuration 7: `[0, 1, 2, 1, 2, 0]` -/

theorem N5_c7_0_0 : chunk 5 13 [0, 1, 2, 1, 2, 0] 0 0 = true := by decide +kernel
theorem N5_c7_0_1 : chunk 5 13 [0, 1, 2, 1, 2, 0] 0 1 = true := by decide +kernel
theorem N5_c7_0_2 : chunk 5 13 [0, 1, 2, 1, 2, 0] 0 2 = true := by decide +kernel
theorem N5_c7_0_3 : chunk 5 13 [0, 1, 2, 1, 2, 0] 0 3 = true := by decide +kernel
theorem N5_c7_0_4 : chunk 5 13 [0, 1, 2, 1, 2, 0] 0 4 = true := by decide +kernel
theorem N5_c7_1_0 : chunk 5 13 [0, 1, 2, 1, 2, 0] 1 0 = true := by decide +kernel
theorem N5_c7_1_1 : chunk 5 13 [0, 1, 2, 1, 2, 0] 1 1 = true := by decide +kernel
theorem N5_c7_1_2 : chunk 5 13 [0, 1, 2, 1, 2, 0] 1 2 = true := by decide +kernel
theorem N5_c7_1_3 : chunk 5 13 [0, 1, 2, 1, 2, 0] 1 3 = true := by decide +kernel
theorem N5_c7_1_4 : chunk 5 13 [0, 1, 2, 1, 2, 0] 1 4 = true := by decide +kernel
theorem N5_c7_2_0 : chunk 5 13 [0, 1, 2, 1, 2, 0] 2 0 = true := by decide +kernel
theorem N5_c7_2_1 : chunk 5 13 [0, 1, 2, 1, 2, 0] 2 1 = true := by decide +kernel
theorem N5_c7_2_2 : chunk 5 13 [0, 1, 2, 1, 2, 0] 2 2 = true := by decide +kernel
theorem N5_c7_2_3 : chunk 5 13 [0, 1, 2, 1, 2, 0] 2 3 = true := by decide +kernel
theorem N5_c7_2_4 : chunk 5 13 [0, 1, 2, 1, 2, 0] 2 4 = true := by decide +kernel
theorem N5_c7_3_0 : chunk 5 13 [0, 1, 2, 1, 2, 0] 3 0 = true := by decide +kernel
theorem N5_c7_3_1 : chunk 5 13 [0, 1, 2, 1, 2, 0] 3 1 = true := by decide +kernel
theorem N5_c7_3_2 : chunk 5 13 [0, 1, 2, 1, 2, 0] 3 2 = true := by decide +kernel
theorem N5_c7_3_3 : chunk 5 13 [0, 1, 2, 1, 2, 0] 3 3 = true := by decide +kernel
theorem N5_c7_3_4 : chunk 5 13 [0, 1, 2, 1, 2, 0] 3 4 = true := by decide +kernel
theorem N5_c7_4_0 : chunk 5 13 [0, 1, 2, 1, 2, 0] 4 0 = true := by decide +kernel
theorem N5_c7_4_1 : chunk 5 13 [0, 1, 2, 1, 2, 0] 4 1 = true := by decide +kernel
theorem N5_c7_4_2 : chunk 5 13 [0, 1, 2, 1, 2, 0] 4 2 = true := by decide +kernel
theorem N5_c7_4_3 : chunk 5 13 [0, 1, 2, 1, 2, 0] 4 3 = true := by decide +kernel
theorem N5_c7_4_4 : chunk 5 13 [0, 1, 2, 1, 2, 0] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 7 at `n = 5`. -/
theorem N5_c7 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [0, 1, 2, 1, 2, 0] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c7_0_0
  | 0, 1, _, _ => exact N5_c7_0_1
  | 0, 2, _, _ => exact N5_c7_0_2
  | 0, 3, _, _ => exact N5_c7_0_3
  | 0, 4, _, _ => exact N5_c7_0_4
  | 1, 0, _, _ => exact N5_c7_1_0
  | 1, 1, _, _ => exact N5_c7_1_1
  | 1, 2, _, _ => exact N5_c7_1_2
  | 1, 3, _, _ => exact N5_c7_1_3
  | 1, 4, _, _ => exact N5_c7_1_4
  | 2, 0, _, _ => exact N5_c7_2_0
  | 2, 1, _, _ => exact N5_c7_2_1
  | 2, 2, _, _ => exact N5_c7_2_2
  | 2, 3, _, _ => exact N5_c7_2_3
  | 2, 4, _, _ => exact N5_c7_2_4
  | 3, 0, _, _ => exact N5_c7_3_0
  | 3, 1, _, _ => exact N5_c7_3_1
  | 3, 2, _, _ => exact N5_c7_3_2
  | 3, 3, _, _ => exact N5_c7_3_3
  | 3, 4, _, _ => exact N5_c7_3_4
  | 4, 0, _, _ => exact N5_c7_4_0
  | 4, 1, _, _ => exact N5_c7_4_1
  | 4, 2, _, _ => exact N5_c7_4_2
  | 4, 3, _, _ => exact N5_c7_4_3
  | 4, 4, _, _ => exact N5_c7_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

/-! ### Configuration 8: `[1, 1, 0, 2, 2, 0]` -/

theorem N5_c8_0_0 : chunk 5 13 [1, 1, 0, 2, 2, 0] 0 0 = true := by decide +kernel
theorem N5_c8_0_1 : chunk 5 13 [1, 1, 0, 2, 2, 0] 0 1 = true := by decide +kernel
theorem N5_c8_0_2 : chunk 5 13 [1, 1, 0, 2, 2, 0] 0 2 = true := by decide +kernel
theorem N5_c8_0_3 : chunk 5 13 [1, 1, 0, 2, 2, 0] 0 3 = true := by decide +kernel
theorem N5_c8_0_4 : chunk 5 13 [1, 1, 0, 2, 2, 0] 0 4 = true := by decide +kernel
theorem N5_c8_1_0 : chunk 5 13 [1, 1, 0, 2, 2, 0] 1 0 = true := by decide +kernel
theorem N5_c8_1_1 : chunk 5 13 [1, 1, 0, 2, 2, 0] 1 1 = true := by decide +kernel
theorem N5_c8_1_2 : chunk 5 13 [1, 1, 0, 2, 2, 0] 1 2 = true := by decide +kernel
theorem N5_c8_1_3 : chunk 5 13 [1, 1, 0, 2, 2, 0] 1 3 = true := by decide +kernel
theorem N5_c8_1_4 : chunk 5 13 [1, 1, 0, 2, 2, 0] 1 4 = true := by decide +kernel
theorem N5_c8_2_0 : chunk 5 13 [1, 1, 0, 2, 2, 0] 2 0 = true := by decide +kernel
theorem N5_c8_2_1 : chunk 5 13 [1, 1, 0, 2, 2, 0] 2 1 = true := by decide +kernel
theorem N5_c8_2_2 : chunk 5 13 [1, 1, 0, 2, 2, 0] 2 2 = true := by decide +kernel
theorem N5_c8_2_3 : chunk 5 13 [1, 1, 0, 2, 2, 0] 2 3 = true := by decide +kernel
theorem N5_c8_2_4 : chunk 5 13 [1, 1, 0, 2, 2, 0] 2 4 = true := by decide +kernel
theorem N5_c8_3_0 : chunk 5 13 [1, 1, 0, 2, 2, 0] 3 0 = true := by decide +kernel
theorem N5_c8_3_1 : chunk 5 13 [1, 1, 0, 2, 2, 0] 3 1 = true := by decide +kernel
theorem N5_c8_3_2 : chunk 5 13 [1, 1, 0, 2, 2, 0] 3 2 = true := by decide +kernel
theorem N5_c8_3_3 : chunk 5 13 [1, 1, 0, 2, 2, 0] 3 3 = true := by decide +kernel
theorem N5_c8_3_4 : chunk 5 13 [1, 1, 0, 2, 2, 0] 3 4 = true := by decide +kernel
theorem N5_c8_4_0 : chunk 5 13 [1, 1, 0, 2, 2, 0] 4 0 = true := by decide +kernel
theorem N5_c8_4_1 : chunk 5 13 [1, 1, 0, 2, 2, 0] 4 1 = true := by decide +kernel
theorem N5_c8_4_2 : chunk 5 13 [1, 1, 0, 2, 2, 0] 4 2 = true := by decide +kernel
theorem N5_c8_4_3 : chunk 5 13 [1, 1, 0, 2, 2, 0] 4 3 = true := by decide +kernel
theorem N5_c8_4_4 : chunk 5 13 [1, 1, 0, 2, 2, 0] 4 4 = true := by decide +kernel

/-- Every chunk of configuration 8 at `n = 5`. -/
theorem N5_c8 : ∀ v₁, v₁ < 5 → ∀ v₂, v₂ < 5 → chunk 5 13 [1, 1, 0, 2, 2, 0] v₁ v₂ = true := by
  intro v₁ h₁ v₂ h₂
  match v₁, v₂, h₁, h₂ with
  | 0, 0, _, _ => exact N5_c8_0_0
  | 0, 1, _, _ => exact N5_c8_0_1
  | 0, 2, _, _ => exact N5_c8_0_2
  | 0, 3, _, _ => exact N5_c8_0_3
  | 0, 4, _, _ => exact N5_c8_0_4
  | 1, 0, _, _ => exact N5_c8_1_0
  | 1, 1, _, _ => exact N5_c8_1_1
  | 1, 2, _, _ => exact N5_c8_1_2
  | 1, 3, _, _ => exact N5_c8_1_3
  | 1, 4, _, _ => exact N5_c8_1_4
  | 2, 0, _, _ => exact N5_c8_2_0
  | 2, 1, _, _ => exact N5_c8_2_1
  | 2, 2, _, _ => exact N5_c8_2_2
  | 2, 3, _, _ => exact N5_c8_2_3
  | 2, 4, _, _ => exact N5_c8_2_4
  | 3, 0, _, _ => exact N5_c8_3_0
  | 3, 1, _, _ => exact N5_c8_3_1
  | 3, 2, _, _ => exact N5_c8_3_2
  | 3, 3, _, _ => exact N5_c8_3_3
  | 3, 4, _, _ => exact N5_c8_3_4
  | 4, 0, _, _ => exact N5_c8_4_0
  | 4, 1, _, _ => exact N5_c8_4_1
  | 4, 2, _, _ => exact N5_c8_4_2
  | 4, 3, _, _ => exact N5_c8_4_3
  | 4, 4, _, _ => exact N5_c8_4_4
  | _ + 5, _, h, _ => exact absurd h (by omega)
  | _, _ + 5, _, h => exact absurd h (by omega)

end Census514
end CernyQE
