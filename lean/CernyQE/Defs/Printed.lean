/-
Finite data in Table 2 and the proof of Lemma 5.8.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Binary

namespace CernyQE

/-- Table 2 in printed order, with the class explicitly recorded for each representative. -/
def table2Rows : List (Config × (ℚ × ℚ)) :=
  [
    (⟨2, 2, 0, 0, 0, 2⟩, (1, 1)),
    (⟨2, 2, 0, 1, 1, 1⟩, (1, 1)),
    (⟨2, 0, 2, 0, 0, 2⟩, (1, 1)),
    (⟨2, 0, 2, 1, 1, 1⟩, (1, 1)),
    (⟨2, 0, 0, 2, 0, 2⟩, (1, 1)),
    (⟨2, 0, 0, 1, 0, 1⟩, (1, 1)),
    (⟨2, 0, 1, 2, 1, 1⟩, (1, 1)),
    (⟨2, 0, 1, 0, 0, 1⟩, (1, 1)),
    (⟨2, 1, 2, 0, 1, 1⟩, (1, 1)),
    (⟨2, 1, 0, 2, 1, 1⟩, (1, 1)),
    (⟨2, 1, 0, 0, 0, 1⟩, (1, 1)),
    (⟨2, 1, 0, 1, 1, 0⟩, (1, 1)),
    (⟨2, 1, 1, 0, 1, 0⟩, (1, 1)),
    (⟨2, 2, 2, 0, 0, 2⟩, (1/2, 1)),
    (⟨2, 2, 2, 1, 1, 1⟩, (1/2, 1)),
    (⟨2, 2, 0, 0, 1, 1⟩, (1/2, 1)),
    (⟨2, 2, 0, 1, 0, 1⟩, (1/2, 1)),
    (⟨2, 0, 0, 0, 0, 1⟩, (1/2, 1)),
    (⟨2, 1, 0, 0, 1, 0⟩, (1/2, 1)),
    (⟨2, 2, 0, 1, 0, 2⟩, (1, 2)),
    (⟨2, 0, 0, 0, 0, 2⟩, (1, 2)),
    (⟨2, 0, 0, 1, 1, 1⟩, (1, 2)),
    (⟨2, 0, 1, 0, 1, 1⟩, (1, 2)),
    (⟨2, 1, 0, 0, 2, 0⟩, (1, 2)),
    (⟨2, 1, 0, 1, 0, 1⟩, (1, 2)),
    (⟨2, 1, 1, 0, 0, 1⟩, (1, 2)),
    (⟨2, 2, 2, 0, 0, 1⟩, (1/4, 1/2)),
    (⟨2, 2, 2, 0, 1, 1⟩, (1/2, 3/4)),
    (⟨2, 1, 2, 0, 0, 1⟩, (1/3, 2/3)),
    (⟨2, 1, 0, 2, 0, 1⟩, (1/3, 2/3)),
    (⟨2, 1, 2, 0, 0, 2⟩, (2/3, 4/3)),
    (⟨2, 1, 0, 2, 0, 2⟩, (2/3, 4/3)),
    (⟨2, 0, 0, 0, 1, 1⟩, (1/2, 2)),
    (⟨2, 1, 0, 0, 1, 1⟩, (3/2, 2)),
    (⟨2, 0, 0, 1, 0, 2⟩, (2, 2)),
    (⟨2, 0, 1, 0, 0, 2⟩, (2, 2)),
    (⟨2, 1, 0, 0, 0, 2⟩, (2, 2)),
    (⟨2, 1, 0, 1, 2, 0⟩, (2, 2)),
    (⟨2, 1, 1, 0, 2, 0⟩, (2, 2)),
    (⟨2, 1, 0, 1, 1, 1⟩, (2, 3)),
    (⟨2, 1, 1, 0, 1, 1⟩, (2, 3)),
    (⟨2, 1, 0, 1, 0, 2⟩, (2, 4)),
    (⟨2, 1, 1, 0, 0, 2⟩, (2, 4)),
    (⟨2, 2, 2, 2, 1, 1⟩, (1/2, 1/2)),
    (⟨2, 2, 0, 0, 0, 1⟩, (1/2, 1/2)),
    (⟨2, 0, 2, 0, 0, 1⟩, (1/2, 1/2)),
    (⟨2, 0, 0, 2, 0, 1⟩, (1/2, 1/2)),
    (⟨2, 0, 2, 0, 1, 1⟩, (1/2, 3/2)),
    (⟨2, 0, 0, 2, 1, 1⟩, (1/2, 3/2))]

namespace Config

/-- Number of letters that map exceptional state i to exceptional state j. -/
def G (cf : Config) (i j : Fin 2) : ℚ :=
  ((Finset.univ.filter (fun c : Fin 2 => cf.tgt i c = Fin.castSucc j)).card : ℚ)

/-- The two-by-two determinant of 2I − G, expanded in its four entries. -/
def delta (cf : Config) : ℚ :=
  (2 - cf.G 0 0) * (2 - cf.G 1 1) - cf.G 0 1 * cf.G 1 0

/-- A nonempty subset of the two exceptional states is closed under both letters. -/
def closedException (cf : Config) : Prop :=
  (∀ c, cf.tgt 0 c = 0) ∨ (∀ c, cf.tgt 1 c = 1) ∨ (∀ i c, cf.tgt i c ≠ 2)

instance (cf : Config) : Decidable cf.closedException := by unfold closedException; infer_instance

end Config

abbrev TargetChoices := Fin 3 × Fin 3 × Fin 3 × Fin 3

/-- The four targets and the two boundary counts, in the printed order. -/
def configWith (v : TargetChoices) (a b : ℕ) : Config :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2, a, b⟩

/-- The two possible noninteger levels for a subset of size k in Proposition 5.12. -/
noncomputable def thirdValue (p : ℕ × Bool) : ℝ :=
  if p.2 then (p.1 : ℝ) + 1/3 else (p.1 : ℝ) - 1/3

noncomputable def thirdLevels (n : ℕ) : Finset ℝ :=
  ((Finset.Icc 2 (n-1)) ×ˢ (Finset.univ : Finset Bool)).image thirdValue

/-- Noninteger values attained by subsets in a half-open interval. -/
noncomputable def nonintegerWeights {Q : Type*} [Fintype Q] [DecidableEq Q] (α : Q → ℝ)
    (lo hi : ℝ) : Finset ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset Q)).image (wt α)).filter
    (fun z => lo ≤ z ∧ z < hi ∧ ¬ ∃ m : ℤ, z = m)

end CernyQE
