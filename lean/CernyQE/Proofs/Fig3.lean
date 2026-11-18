/-
Proofs/Fig3.lean — Figure 3: the chain of preimages of the Cerny automaton C_4.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.01 - 20261105 — first.
-/
import Mathlib
import CernyQE.Defs.Automaton
import CernyQE.Proofs.Basic

namespace CernyQE

open Classical Automaton Matrix

namespace Fig3

/-- All words of length `m` over `Fin 2`. -/
def words2 : ℕ → List (List (Fin 2))
  | 0 => [[]]
  | m + 1 => (words2 m).flatMap (fun w => [0 :: w, 1 :: w])

theorem mem_words2 : ∀ w : List (Fin 2), w ∈ words2 w.length
  | [] => by simp [words2]
  | c :: w => by
      simp only [List.length_cons, words2, List.mem_flatMap]
      refine ⟨w, mem_words2 w, ?_⟩
      fin_cases c <;> simp

/-- `minLen P = k` from a word of length `k` with `P` and a check of every shorter word. -/
theorem minLen_eq_of {P : List (Fin 2) → Prop} {k : ℕ} (w : List (Fin 2)) (hw : P w) (hlen : w.length = k)
    (hshort : ∀ m < k, ∀ v ∈ words2 m, ¬ P v) : minLen P = k := by
  refine le_antisymm (hlen ▸ minLen_le_length hw) (le_minLen_iff.2 fun v hv => ?_)
  by_contra hlt
  exact hshort v.length (by exact_mod_cast not_le.mp hlt) v (mem_words2 v) hv

end Fig3

open Fig3

/-- `MovesAcross` unfolds to a comparison of two booleans, so it is decidable (used by `decide` below only). -/
local instance decMovesAcross {Q S : Type*} [DecidableEq Q] (A : Automaton Q S) (x : Q) (K : Finset Q)
    (w : List S) : Decidable (A.MovesAcross x K w) :=
  inferInstanceAs (Decidable (decide (A.act x w ∈ K) ≠ decide (x ∈ K)))

theorem fig3_c4_chain_proved :
    (cerny 4).pre {1} [0] = {0, 1} ∧ (cerny 4).pre {0, 1} [1] = {0, 3} ∧ (cerny 4).pre {0, 3} [1] = {2, 3} ∧
      (cerny 4).pre {2, 3} [1] = {1, 2} ∧ (cerny 4).pre {1, 2} [0] = {0, 1, 2} ∧
      (cerny 4).pre {0, 1, 2} [1] = {0, 1, 3} ∧ (cerny 4).pre {0, 1, 3} [1] = {0, 2, 3} ∧
      (cerny 4).pre {0, 2, 3} [1] = {1, 2, 3} ∧ (cerny 4).pre {1, 2, 3} [0] = Finset.univ ∧
      (cerny 4).pre {0, 1} [0, 1, 1, 1] = {0, 1, 2} ∧ (cerny 4).pre {0, 1, 2} [0, 1, 1, 1] = Finset.univ ∧
      (cerny 4).IsReset [0, 1, 1, 1, 0, 1, 1, 1, 0] ∧ [0, 1, 1, 1, 0, 1, 1, 1, 0].length = 1 + (4 - 2) * 4 ∧
      1 + (4 - 2) * 4 = (4 - 1) ^ 2 ∧
      (cerny 4).esc 0 {0, 1} = 2 ∧ (cerny 4).esc 0 {2, 3} = 2 ∧ (cerny 4).esc 0 {0, 1, 2} = 3 ∧
      (cerny 4).esc 0 {1, 2, 3} = 1 ∧ (cerny 4).ext {2, 3} = 2 ∧ (cerny 4).ext {1, 2, 3} = 1 ∧
      (cerny 4).ext {0, 1} = 4 ∧ (cerny 4).ext {0, 1, 2} = 4 ∧
      ({2, 3} : Finset (Fin 4)).card = ({0, 1} : Finset (Fin 4)).card ∧
      ({1, 2, 3} : Finset (Fin 4)).card = ({0, 1, 2} : Finset (Fin 4)).card := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ⟨1, by decide +kernel⟩, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
  · exact_mod_cast minLen_eq_of [1, 1] (by decide +kernel) rfl (by decide +kernel)
  · exact_mod_cast minLen_eq_of [1, 1] (by decide +kernel) rfl (by decide +kernel)
  · exact_mod_cast minLen_eq_of [1, 1, 1] (by decide +kernel) rfl (by decide +kernel)
  · exact_mod_cast minLen_eq_of [0] (by decide +kernel) rfl (by decide +kernel)
  · exact_mod_cast minLen_eq_of [0, 1] (by decide +kernel) rfl (by decide +kernel)
  · exact_mod_cast minLen_eq_of [0] (by decide +kernel) rfl (by decide +kernel)
  · exact_mod_cast minLen_eq_of [0, 1, 1, 1] (by decide +kernel) rfl (by decide +kernel)
  · exact_mod_cast minLen_eq_of [0, 1, 1, 1] (by decide +kernel) rfl (by decide +kernel)

end CernyQE
