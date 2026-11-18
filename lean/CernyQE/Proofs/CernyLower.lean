/-
CernyQE/Proofs/CernyLower.lean — the lower bound rt(C_n) ≥ (n-1)^2 for the Cerny automata.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import CernyQE.Defs.Automaton

/-!
### Proof idea

Fix a state `q` and follow it along a word `w`. An *a-event* is a letter `a` read while the current state is `0`;
it is the only way the letter `a` moves a state (it sends `0` to `1`). Let `N` be the number of a-events and `B` the
number of letters `b`.

* Every letter `b` and every a-event moves the state by `+1`; other letters fix it. So `q.w = q + B + N` in `Fin n`
  (`cerny_act_eq`).
* Two consecutive a-events are separated by at least `n - 1` letters `b`, and every a-event is a letter. A potential
  argument gives `n * N + d(q) + 1 ≤ |w| + n`, where `d(q) = (-q).val` is the distance from `q` up to `0`
  (`cerny_length_bound`).
* If `w` resets to `r`, take `q = r - B + 1`: then `N ≡ -1 (mod n)`, so `N ≥ n - 1` and `|w| ≥ (n - 1)^2`.
-/

namespace CernyQE

open Automaton

section Helpers

variable {n : ℕ} [NeZero n]

/-! ### The letters of the Černý automaton -/

private theorem act_nil' {Q S : Type*} (A : Automaton Q S) (q : Q) : A.act q [] = q := rfl

private theorem act_cons' {Q S : Type*} (A : Automaton Q S) (q : Q) (c : S) (w : List S) :
    A.act q (c :: w) = A.act (A.step q c) w := rfl

private theorem fin_two_cases (c : Fin 2) : c = 0 ∨ c = 1 := by
  fin_cases c <;> simp

theorem cerny_step_a_zero : (cerny n).step 0 0 = 1 := by
  simp [cerny]

theorem cerny_step_a_ne {q : Fin n} (hq : q ≠ 0) : (cerny n).step q 0 = q := by
  simp [cerny, hq]

theorem cerny_step_b (q : Fin n) : (cerny n).step q 1 = q + 1 := by
  simp [cerny]

private theorem count_b_cons_a (w : List (Fin 2)) : (0 :: w).count 1 = w.count 1 := by
  simp

private theorem count_b_cons_b (w : List (Fin 2)) : (1 :: w).count 1 = w.count 1 + 1 := by
  simp

end Helpers

/-! ### a-events -/

/-- The number of a-events of the state `q` along the word `w`: the letters `a` read while the current state is `0`
(exactly the steps at which the letter `a` moves the state). -/
def cernyEvents (n : ℕ) [NeZero n] : Fin n → List (Fin 2) → ℕ
  | _, [] => 0
  | q, c :: w => (if c = 0 ∧ q = 0 then 1 else 0) + cernyEvents n ((cerny n).step q c) w

section Events

variable {n : ℕ} [NeZero n]

theorem cernyEvents_nil (q : Fin n) : cernyEvents n q [] = 0 := rfl

theorem cernyEvents_a_zero (w : List (Fin 2)) : cernyEvents n 0 (0 :: w) = 1 + cernyEvents n 1 w := by
  simp [cernyEvents, cerny_step_a_zero]

theorem cernyEvents_a_ne {q : Fin n} (hq : q ≠ 0) (w : List (Fin 2)) :
    cernyEvents n q (0 :: w) = cernyEvents n q w := by
  simp [cernyEvents, cerny_step_a_ne hq, hq]

theorem cernyEvents_b (q : Fin n) (w : List (Fin 2)) : cernyEvents n q (1 :: w) = cernyEvents n (q + 1) w := by
  simp [cernyEvents, cerny_step_b]

-- The cast `ℕ → Fin n` lives in the scoped ring structure of `Fin n`.
open Fin.CommRing

/-- Rotating frame: every letter `b` and every a-event moves the state by `+1`, so `q.w = q + #b(w) + N_q(w)`. -/
theorem cerny_act_eq (q : Fin n) (w : List (Fin 2)) :
    (cerny n).act q w = q + ((w.count 1 + cernyEvents n q w : ℕ) : Fin n) := by
  induction w generalizing q with
  | nil => simp [act_nil', cernyEvents_nil]
  | cons c w ih =>
    rw [act_cons']
    rcases fin_two_cases c with rfl | rfl
    · by_cases hq : q = 0
      · subst hq
        rw [cerny_step_a_zero, ih, cernyEvents_a_zero, count_b_cons_a]
        push_cast
        abel
      · rw [cerny_step_a_ne hq, ih, cernyEvents_a_ne hq, count_b_cons_a]
    · rw [cerny_step_b, ih, cernyEvents_b, count_b_cons_b]
      push_cast
      abel

/-! ### The distance up to `0` -/

private theorem neg_one_val (hn : 2 ≤ n) : ((-1 : Fin n) : ℕ) = n - 1 := by
  rw [Fin.val_neg', Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega : n - 1 < n)]

private theorem neg_val_le_succ (q : Fin n) : ((-q : Fin n) : ℕ) ≤ ((-(q + 1) : Fin n) : ℕ) + 1 := by
  have hsplit : -q = -(q + 1) + 1 := by abel
  rw [hsplit, Fin.val_add, Fin.val_one']
  have h1 : 1 % n ≤ 1 := Nat.mod_le 1 n
  have h2 := Nat.mod_le (((-(q + 1) : Fin n) : ℕ) + 1 % n) n
  omega

/-- The potential bound: along `w`, the state `q` has `N` a-events with `n * N + (-q).val + 1 ≤ |w| + n`. -/
theorem cerny_length_bound (hn : 2 ≤ n) (q : Fin n) (w : List (Fin 2)) :
    n * cernyEvents n q w + ((-q : Fin n) : ℕ) + 1 ≤ w.length + n := by
  induction w generalizing q with
  | nil =>
    have hlt := (-q).isLt
    rw [cernyEvents_nil, List.length_nil]
    omega
  | cons c w ih =>
    rcases fin_two_cases c with rfl | rfl
    · by_cases hq : q = 0
      · subst hq
        have h1 := ih 1
        rw [neg_one_val hn] at h1
        rw [cernyEvents_a_zero, neg_zero, Fin.val_zero, List.length_cons, mul_add, mul_one]
        omega
      · have h1 := ih q
        rw [cernyEvents_a_ne hq, List.length_cons]
        omega
    · have h1 := ih (q + 1)
      have h2 := neg_val_le_succ q
      rw [cernyEvents_b, List.length_cons]
      omega

/-- If `w` resets to `r`, the state `r - #b(w) + 1` has at least `n - 1` a-events along `w`. -/
theorem cerny_events_ge_of_reset (hn : 2 ≤ n) (w : List (Fin 2)) (r : Fin n)
    (hr : ∀ q : Fin n, (cerny n).act q w = r) :
    n - 1 ≤ cernyEvents n (r - ((w.count 1 : ℕ) : Fin n) + 1) w := by
  have hact := cerny_act_eq (r - ((w.count 1 : ℕ) : Fin n) + 1) w
  rw [hr] at hact
  generalize cernyEvents n (r - ((w.count 1 : ℕ) : Fin n) + 1) w = N at hact ⊢
  push_cast at hact
  have hN : ((N : ℕ) : Fin n) = -1 :=
    calc ((N : ℕ) : Fin n) = (r - ((w.count 1 : ℕ) : Fin n) + 1 + (((w.count 1 : ℕ) : Fin n) + (N : Fin n)))
          - r - 1 := by abel
      _ = -1 := by rw [← hact]; abel
  have hval := congrArg Fin.val hN
  rw [Fin.val_natCast, neg_one_val hn] at hval
  have hmod := Nat.mod_le N n
  omega

end Events

/-! ### The lower bound -/

open Fin.CommRing in
/-- Every reset word of the Černý automaton `C_n` has length at least `(n - 1)^2`. -/
theorem cerny_reset_length_ge (n : ℕ) [NeZero n] (hn : 2 ≤ n) (w : List (Fin 2))
    (hw : (cerny n).IsReset w) : (n - 1) ^ 2 ≤ w.length := by
  obtain ⟨r, hr⟩ := hw
  have hN := cerny_events_ge_of_reset hn w r hr
  have hlen := cerny_length_bound hn (r - ((w.count 1 : ℕ) : Fin n) + 1) w
  generalize cernyEvents n (r - ((w.count 1 : ℕ) : Fin n) + 1) w = N at hN hlen
  generalize (((-(r - ((w.count 1 : ℕ) : Fin n) + 1)) : Fin n) : ℕ) = d at hlen
  have hmul := Nat.mul_le_mul_left n hN
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hN hmul ⊢
  nlinarith

/-- The reset threshold of the Černý automaton `C_n` is at least `(n - 1)^2`. -/
theorem cerny_rt_ge (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (((n - 1) ^ 2 : ℕ) : ℕ∞) ≤ (cerny n).rt := by
  unfold Automaton.rt minLen
  refine le_iInf₂ (fun w hw => ?_)
  exact_mod_cast cerny_reset_length_ge n hn w hw

end CernyQE
