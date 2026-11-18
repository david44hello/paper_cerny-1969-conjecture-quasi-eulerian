/-
CernyQE/Proofs/Census514/Lower.lean — finite facts for Proposition 5.14: the automata that attain 8, 13, 19, and the
integer classes up to renaming.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import CernyQE.Defs.Binary
import CernyQE.Proofs.ImageSearch
import Mathlib

/-!
For `n = 4, 5, 6` one automaton `tabAut n (lowTbl n)` with `E = {0, …, n-3}`, `s = 0`, `x₁ = n-2`, `x₂ = n-1`: the
edges from `X` end in `X ∪ {s}`, every state of `E \ {s}` has in-degree two, the configuration, strong connectivity,
and the exact reset threshold by the image search (a singleton image at length `M`, none at length `M - 1`; for
`n = 6` the singleton image is shown by one explicit word).
Then: every configuration of the five integer classes is, after renaming `x₁ ↔ x₂` and `a ↔ b`, one of the nine of
`canonCfgs`.
-/

namespace CernyQE
namespace Census514

open ImageSearch

/-- The set `E = {0, …, n-3}`. -/
def lowE (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun q => q.val < n - 2)

/-- The tables (images under `a`, then under `b`). -/
def lowTbl4 : List ℕ := [1, 3, 2, 0, 2, 1, 3, 2]
def lowTbl5 : List ℕ := [1, 2, 2, 3, 4, 3, 1, 3, 4, 0]
def lowTbl6 : List ℕ := [5, 2, 1, 5, 4, 0, 1, 3, 2, 3, 5, 4]

/-! ### n = 4 -/

theorem low4_cardE : (lowE 4).card = 2 := by decide
theorem low4_X : Finset.univ \ lowE 4 = {2, 3} := by decide
theorem low4_edgeX : ∀ q : Fin 4, q ∉ lowE 4 → ∀ c : Fin 2,
    (tabAut 4 lowTbl4).step q c ∉ lowE 4 ∨ (tabAut 4 lowTbl4).step q c = 0 := by decide
theorem low4_indeg : ∀ r : Fin 4, r ∈ lowE 4 → r ≠ 0 →
    ((tabAut 4 lowTbl4).pre {r} [0]).card + ((tabAut 4 lowTbl4).pre {r} [1]).card = 2 := by decide
theorem low4_cfg : (tabAut 4 lowTbl4).configOf 0 1 (lowE 4) 2 3 = ⟨0, 1, 2, 0, 1, 1⟩ := by decide
theorem low4_sc : (tabAut 4 lowTbl4).StronglyConnected := by
  unfold Automaton.StronglyConnected Automaton.IsClosed
  decide
theorem low4_upper : ∃ T ∈ imgs (tabAut 4 lowTbl4) 8, T.card = 1 := by decide +kernel
theorem low4_lower : ∀ T ∈ imgs (tabAut 4 lowTbl4) 7, T.card ≠ 1 := by decide +kernel

/-! ### n = 5 -/

theorem low5_cardE : (lowE 5).card = 3 := by decide
theorem low5_X : Finset.univ \ lowE 5 = {3, 4} := by decide
theorem low5_edgeX : ∀ q : Fin 5, q ∉ lowE 5 → ∀ c : Fin 2,
    (tabAut 5 lowTbl5).step q c ∉ lowE 5 ∨ (tabAut 5 lowTbl5).step q c = 0 := by decide
theorem low5_indeg : ∀ r : Fin 5, r ∈ lowE 5 → r ≠ 0 →
    ((tabAut 5 lowTbl5).pre {r} [0]).card + ((tabAut 5 lowTbl5).pre {r} [1]).card = 2 := by decide
theorem low5_cfg : (tabAut 5 lowTbl5).configOf 0 1 (lowE 5) 3 4 = ⟨0, 1, 1, 2, 2, 0⟩ := by decide
theorem low5_sc : (tabAut 5 lowTbl5).StronglyConnected := by
  unfold Automaton.StronglyConnected Automaton.IsClosed
  decide +kernel
theorem low5_upper : ∃ T ∈ imgs (tabAut 5 lowTbl5) 13, T.card = 1 := by decide +kernel
theorem low5_lower : ∀ T ∈ imgs (tabAut 5 lowTbl5) 12, T.card ≠ 1 := by decide +kernel

/-! ### n = 6 -/

theorem low6_cardE : (lowE 6).card = 4 := by decide
theorem low6_X : Finset.univ \ lowE 6 = {4, 5} := by decide
theorem low6_edgeX : ∀ q : Fin 6, q ∉ lowE 6 → ∀ c : Fin 2,
    (tabAut 6 lowTbl6).step q c ∉ lowE 6 ∨ (tabAut 6 lowTbl6).step q c = 0 := by decide
theorem low6_indeg : ∀ r : Fin 6, r ∈ lowE 6 → r ≠ 0 →
    ((tabAut 6 lowTbl6).pre {r} [0]).card + ((tabAut 6 lowTbl6).pre {r} [1]).card = 2 := by decide
theorem low6_cfg : (tabAut 6 lowTbl6).configOf 0 1 (lowE 6) 4 5 = ⟨0, 1, 2, 0, 0, 2⟩ := by decide
theorem low6_sc : (tabAut 6 lowTbl6).StronglyConnected := by
  unfold Automaton.StronglyConnected Automaton.IsClosed
  decide +kernel
/-- A reset word of length 19 for `n = 6`, found by the image search (`findWord`, Census514/Search.lean). -/
def low6Word : List (Fin 2) := [1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]

/-- One explicit word, checked by `isResetB`: this avoids computing every image of length 19 in the kernel. -/
theorem low6_upper : ∃ T ∈ imgs (tabAut 6 lowTbl6) 19, T.card = 1 := by
  have hreset : (tabAut 6 lowTbl6).IsReset low6Word := isResetB_sound 6 lowTbl6 low6Word (by decide +kernel)
  refine ⟨(tabAut 6 lowTbl6).img Finset.univ low6Word, ?_, (isReset_iff_card _ low6Word).1 hreset⟩
  rw [mem_imgs]
  exact ⟨low6Word, by decide +kernel, rfl⟩
theorem low6_lower : ∀ T ∈ imgs (tabAut 6 lowTbl6) 18, T.card ≠ 1 := by decide +kernel

/-! ### The values `t` of the three configurations -/

theorem low_t4 : (⟨0, 1, 2, 0, 1, 1⟩ : Config).t 0 = 3 ∧ (⟨0, 1, 2, 0, 1, 1⟩ : Config).t 1 = 2 := by decide +kernel
theorem low_t5 : (⟨0, 1, 1, 2, 2, 0⟩ : Config).t 0 = 2 ∧ (⟨0, 1, 1, 2, 2, 0⟩ : Config).t 1 = 2 := by decide +kernel
theorem low_t6 : (⟨0, 1, 2, 0, 0, 2⟩ : Config).t 0 = 2 ∧ (⟨0, 1, 2, 0, 0, 2⟩ : Config).t 1 = 2 := by decide +kernel

/-! ### The integer classes up to renaming -/

/-- The raw list `[x₁.a, x₁.b, x₂.a, x₂.b, ν₁, ν₂]` of a configuration. -/
def rawOf (cf : Config) : List ℕ := [cf.x1a.val, cf.x1b.val, cf.x2a.val, cf.x2b.val, cf.nu1, cf.nu2]

/-- `(t₁, t₂)` is one of `(2,2), (2,3), (3,2), (2,4), (4,2)`. -/
def IntClass (cf : Config) : Prop :=
  (cf.t 0 = 2 ∧ cf.t 1 = 2) ∨ (cf.t 0 = 2 ∧ cf.t 1 = 3) ∨ (cf.t 0 = 3 ∧ cf.t 1 = 2) ∨
    (cf.t 0 = 2 ∧ cf.t 1 = 4) ∨ (cf.t 0 = 4 ∧ cf.t 1 = 2)

instance (cf : Config) : Decidable (IntClass cf) := by unfold IntClass; infer_instance

/-- Some renaming of `cf` is one of the nine. -/
def CanonOK (cf : Config) : Prop :=
  rawOf cf ∈ canonCfgs ∨ rawOf cf.swapX ∈ canonCfgs ∨ rawOf cf.swapL ∈ canonCfgs ∨
    rawOf cf.swapX.swapL ∈ canonCfgs

instance (cf : Config) : Decidable (CanonOK cf) := by unfold CanonOK; infer_instance

theorem canon_table : ∀ (x1a x1b x2a x2b ν₁ ν₂ : Fin 3), ν₁.val + ν₂.val ≤ 2 →
    IntClass ⟨x1a, x1b, x2a, x2b, ν₁.val, ν₂.val⟩ → CanonOK ⟨x1a, x1b, x2a, x2b, ν₁.val, ν₂.val⟩ := by
  decide +kernel

end Census514
end CernyQE
