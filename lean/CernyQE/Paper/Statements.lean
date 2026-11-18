/-
CernyQE/Paper/Statements.lean — one Lean theorem ("row") per claim of the paper "The Cerny (1969) conjecture holds for
quasi-Eulerian automata of degree one". SINGLE WRITER: one person.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.51 - 20261118 — source references use the paper metadata recorded in the audit notes and claim map.
## version 0.21 - 20261105 — + row fig3_c4_chain; Section 2 linked.
## version 0.01 - 20261105 — first: every row of CLAIM_MAP.tsv 0.01 typed; bodies open.
Paper = the paper's frozen text (AUDIT_NOTES.md and CLAIM_MAP.tsv name its
version and the SHA-256 of its source files); a pointer "tex:N" is line N of its main source file.
A row is proved iff its body is a proof term `X_proved ...` from the proof modules.
Lengths are in `ℕ∞` (`minLen`, Defs/Automaton.lean): `A.rt ≤ N` holds only for a synchronizing automaton.
Binary automata: letters `a b : S` with `a ≠ b` and every letter `a` or `b`.
-/
import CernyQE.Defs.Automaton
import CernyQE.Defs.Tier
import CernyQE.Defs.Witness
import CernyQE.Defs.Binary
import CernyQE.Defs.Examples
import CernyQE.Proofs.Rows2
import CernyQE.Proofs.Sec3Levels
import CernyQE.Proofs.Sec51
import CernyQE.Proofs.Stationary
import CernyQE.Proofs.Examples1
import CernyQE.Proofs.Examples2
import CernyQE.Proofs.Thm31
import CernyQE.Proofs.Census
import CernyQE.Proofs.PrintedCensus
import CernyQE.Proofs.BinaryBase
import CernyQE.Proofs.Census514
import CernyQE.Proofs.MethNonint
import CernyQE.Proofs.Fig3
import CernyQE.Proofs.Rem34L
import CernyQE.Proofs.MergingRemark
import CernyQE.Proofs.Rem34w
import CernyQE.Proofs.Prop514
import CernyQE.Proofs.PrintedLevels
import CernyQE.Proofs.PrintedCosts
import CernyQE.Proofs.Prop513
import CernyQE.Proofs.Props511
import CernyQE.Proofs.Rows4
import CernyQE.Proofs.Rows5x
import CernyQE.Proofs.Sec5x
import CernyQE.Proofs.Thm59

namespace CernyQE

open Classical Automaton Matrix

universe u v

section General

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-! ## Section 1 (introduction) -/

/-- tex:65-67 and tex:547: `rt(C_n) = (n-1)^2`. -/
theorem intro_rt_cerny (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (cerny n).rt = (((n - 1) ^ 2 : ℕ) : ℕ∞) :=
  intro_rt_cerny_proved n hn

/-- tex:135: a synchronizing degree-one automaton that is not strongly connected: every letter fixes the exceptional
state or `E` is closed, and `rt ≤ 1 + (n-2)(n-1)`. -/
theorem intro_deg1_nonsc (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) (hsc : ¬ A.StronglyConnected) :
    ((∀ b, A.step x b = x) ∨ A.IsClosed W.E) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) :=
  intro_deg1_nonsc_proved A hA hn W x hx hsc

/-- tex:138-139: every strongly connected synchronizing degree-one automaton satisfies the hypothesis of Theorem 3.1,
with the vector of Lemma 4.2: positive, stationary, equal to `1` on `E`. -/
theorem intro_deg1_in_thm31 (hA : A.Synchronizing) (hsc : A.StronglyConnected) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) :
    A.zLoop W.p x < 1 ∧ A.IsStationary W.p (A.alphaDeg1 W.E W.p x) ∧ (∀ q, 0 < A.alphaDeg1 W.E W.p x q) ∧
      ∀ q ∈ W.E, A.alphaDeg1 W.E W.p x q = 1 :=
  intro_deg1_in_thm31_proved A hA hsc W x hx

/-- tex:93-94: for a strongly connected quasi-Eulerian automaton the stationary vector can be taken equal to `1` on
`E` and positive on the exceptional states (Lemma 5.5). -/
theorem intro_statd (hsc : A.StronglyConnected) {d : ℕ} (W : QEWitness A d) :
    ∃ α : Q → ℝ, A.IsStationary W.p α ∧ (∀ q ∈ W.E, α q = 1) ∧ ∀ q, 0 < α q :=
  intro_statd_proved A hsc W

/-- tex:157 and Remark 4.4, tex:561: the one-cluster automata and the family of Theorem 4.1 are incomparable: Example 3.5 is synchronizing
and one-cluster but not quasi-Eulerian of degree one; the 4-state automaton of Remark 4.4 is synchronizing and
quasi-Eulerian of degree one but not one-cluster. -/
theorem intro_incomparable :
    (ex35.Synchronizing ∧ OneCluster ex35 ∧ ¬ QuasiEulerian ex35 1) ∧
      (exIntro4.Synchronizing ∧ QuasiEulerian exIntro4 1 ∧ ¬ OneCluster exIntro4) :=
  intro_incomparable_proved

/-- Remark 4.4, tex:561: the letter `a` of Example 3.5 has the single cycle `0 → 2 → 3 → 4 → 0`. -/
theorem ex_3_5_one_cluster : cycles (fun q => ex35.step q 0) = {{0, 2, 3, 4}} ∧ OneCluster ex35 :=
  ex_3_5_one_cluster_proved

/-- Remark 4.4, tex:561: the 4-state automaton `a = (0,2,1,0)`, `b = (1,3,2,0)` is synchronizing and quasi-Eulerian of degree one
with `X = {3}`, `s = 0`: both edges from `3` end at `0`, and each of `1`, `2` is entered once by each letter. -/
theorem intro_ex4_qe1 :
    exIntro4.Synchronizing ∧ (∀ c, exIntro4.step 3 c = 0) ∧
      (∀ r : Fin 4, r = 1 ∨ r = 2 → ∀ c, (exIntro4.pre {r} [c]).card = 1) ∧
      ∃ W : QEWitness exIntro4 1, W.E = {0, 1, 2} ∧ W.s = 0 :=
  intro_ex4_qe1_proved

/-- Remark 4.4, tex:561: the word `abbabba` resets it. -/
theorem intro_ex4_reset : exIntro4.IsReset [0, 1, 1, 0, 1, 1, 0] :=
  intro_ex4_reset_proved

/-- Remark 4.4, tex:561: `a` has the cycles `(0)` and `(1 2)`, and `b` has `(0 1 3)` and `(2)`. -/
theorem intro_ex4_cycles :
    cycles (fun q => exIntro4.step q 0) = {{0}, {1, 2}} ∧ cycles (fun q => exIntro4.step q 1) = {{0, 1, 3}, {2}} :=
  intro_ex4_cycles_proved

/-- tex:191-192: when `α` is constant (`c > 0`) off one state `x`, a raising word either enlarges the set or moves `x`
across it. -/
theorem meth_raise_enlarge_or_move (α : Q → ℝ) (x : Q) (c : ℝ) (hc : 0 < c) (hα : ∀ q, q ≠ x → α q = c)
    (K : Finset Q) (w : List S) (hw : A.Raises α K w) :
    K.card < (A.pre K w).card ∨ A.MovesAcross x K w :=
  meth_raise_enlarge_or_move_proved A α x c hc hα K w hw

/-- tex:195: if `t - 1` is not an integer, every word that moves `x` across a set changes `α`. -/
theorem meth_move_changes (x : Q) (t : ℝ) (ht : ¬ ∃ z : ℤ, t - 1 = z) (K : Finset Q) (w : List S)
    (hw : A.MovesAcross x K w) : wt (alphaOff x t) (A.pre K w) ≠ wt (alphaOff x t) K :=
  meth_move_changes_proved A x t ht K w hw

/-! ## Section 2 (preliminaries) -/

/-- tex:228. -/
theorem sec2_act_append (q : Q) (u w : List S) : A.act q (u ++ w) = A.act (A.act q u) w :=
  sec2_act_append_proved A q u w

/-- tex:229-230: `K(uv)⁻¹ = (K v⁻¹) u⁻¹`. -/
theorem sec2_pre_append (K : Finset Q) (u w : List S) : A.pre K (u ++ w) = A.pre (A.pre K w) u :=
  sec2_pre_append_proved A K u w

/-- tex:311: `[x ∈ K w⁻¹] = [x.w ∈ K]`. -/
theorem sec2_mem_pre (x : Q) (K : Finset Q) (w : List S) : x ∈ A.pre K w ↔ A.act x w ∈ K :=
  sec2_mem_pre_proved A x K w

/-- tex:232-235: the extension method. -/
theorem sec2_ext_method (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ)
    (hK : ∀ j < J, K (j + 1) = A.pre (K j) (w j)) (hJ : K J = Finset.univ) :
    K J = A.pre (K 0) (((List.range J).reverse.map w).flatten) ∧
      (∀ q, A.act q (((List.range J).reverse.map w).flatten) ∈ K 0) ∧
      ((∃ r, K 0 = {r}) → A.IsReset (((List.range J).reverse.map w).flatten)) ∧
      (∀ (r : Q) (c : S), K 0 = A.pre {r} [c] → A.IsReset (((List.range J).reverse.map w).flatten ++ [c])) :=
  sec2_ext_method_proved A K w J hK hJ

/-- tex:238-239: `M_{uv} = M_u M_v`. -/
theorem sec2_Mw_mul (u w : List S) : A.Mw (u ++ w) = A.Mw u * A.Mw w :=
  sec2_Mw_mul_proved A u w

/-- tex:239: `M_w 1 = 1`. -/
theorem sec2_Mw_one (w : List S) : A.Mw w *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 :=
  sec2_Mw_one_proved A w

/-- tex:239: `M_w 𝟙_K = 𝟙_(K w⁻¹)`. -/
theorem sec2_Mw_ind (w : List S) (K : Finset Q) : A.Mw w *ᵥ ind K = ind (A.pre K w) :=
  sec2_Mw_ind_proved A w K

/-- tex:240: `βᵀ M_w 𝟙_K = β(K w⁻¹)`. -/
theorem sec2_wt_Mw (β : Q → ℝ) (w : List S) (K : Finset Q) : β ⬝ᵥ (A.Mw w *ᵥ ind K) = wt β (A.pre K w) :=
  sec2_wt_Mw_proved A β w K

/-- tex:245: `M` is row-stochastic. -/
theorem sec2_M_stochastic (p : S → ℝ) (hp : IsLetterWeights p) :
    (∀ q q', 0 ≤ A.M p q q') ∧ ∀ q, ∑ q', A.M p q q' = 1 :=
  sec2_M_stochastic_proved A p hp

/-- tex:253, tex:574: every state has out-weight one. -/
theorem sec2_outweight (p : S → ℝ) (hp : IsLetterWeights p) (q : Q) : ∑ q', A.M p q q' = 1 :=
  sec2_outweight_proved A p hp q

/-- tex:248-250, equation (2.1). -/
theorem eq_2_1 (p : S → ℝ) (α : Q → ℝ) (hα : A.IsStationary p α) (T : Finset Q) :
    ∑ b, p b * wt α (A.pre T [b]) = α ⬝ᵥ (A.M p *ᵥ ind T) ∧ α ⬝ᵥ (A.M p *ᵥ ind T) = wt α T :=
  eq_2_1_proved A p α hα T

/-- tex:253: the in-weights add up to `n`. -/
theorem sec2_inW_sum (p : S → ℝ) (hp : IsLetterWeights p) : ∑ q, A.inW p q = (Fintype.card Q : ℝ) :=
  sec2_inW_sum_proved A p hp

/-- tex:253-254: `α = 1` is stationary iff every in-weight is one. -/
theorem sec2_one_stationary_iff [Nonempty Q] (p : S → ℝ) (hp : IsLetterWeights p) :
    A.IsStationary p (fun _ => 1) ↔ ∀ q, A.inW p q = 1 :=
  sec2_one_stationary_iff_proved A p hp

/-- Lemma 2.1 (strong connectivity), tex:256-259. -/
theorem lem_2_1 (hA : A.Synchronizing) (p : S → ℝ) (hp : IsLetterWeights p) (α : Q → ℝ)
    (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) : A.StronglyConnected :=
  lem_2_1_proved A hA p hp α hα hpos

/-- Lemma 2.2(a) (the extension step), tex:268-272: `m` exists and `1 ≤ m ≤ n-1`. -/
theorem lem_2_2_a (hA : A.Synchronizing) (β : Q → ℝ) (K : Finset Q) (hQ : wt β Finset.univ ≠ 0)
    (hK0 : wt β K ≠ 0) (hK1 : wt β K ≠ wt β Finset.univ) :
    1 ≤ A.cost β K ∧ A.cost β K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞) :=
  lem_2_2_a_proved A hA β K hQ hK0 hK1

/-- Lemma 2.2(b), tex:273-274. -/
theorem lem_2_2_b (hA : A.Synchronizing) (β : Q → ℝ) (K : Finset Q) (hQ : wt β Finset.univ ≠ 0)
    (hK0 : wt β K ≠ 0) (hK1 : wt β K ≠ wt β Finset.univ) (m : ℕ) (hm : A.cost β K = m) (p : S → ℝ)
    (hp : IsLetterWeights p)
    (havg : ∀ v : List S, v.length = m - 1 →
      wt β (A.pre K v) ≤ ∑ b, p b * wt β (A.pre (A.pre K v) [b])) :
    ∃ w : List S, w.length = m ∧ A.Raises β K w :=
  lem_2_2_b_proved A hA β K hQ hK0 hK1 m hm p hp havg

/-- Lemma 2.2, last statement, tex:276-278. -/
theorem lem_2_2_last (hA : A.Synchronizing) (p : S → ℝ) (hp : IsLetterWeights p) (α : Q → ℝ)
    (hα : A.IsStationary p α) (hQ : wt α Finset.univ ≠ 0) (K : Finset Q) (hK0 : wt α K ≠ 0)
    (hK1 : wt α K ≠ wt α Finset.univ) :
    (∃ w : List S, w.length ≤ Fintype.card Q - 1 ∧ A.Raises α K w) ∧ minLen (A.Raises α K) = A.cost α K :=
  lem_2_2_last_proved A hA p hp α hα hQ K hK0 hK1

/-- tex:303-306: for `α > 0` and a nonempty proper `K`, `1 ≤ m(K) ≤ n-1`; if `α` is stationary, some word of length
`m(K)` raises `α`. -/
theorem sec2_cost_bounds (hA : A.Synchronizing) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (K : Finset Q)
    (hne : K.Nonempty) (hprop : K ≠ Finset.univ) :
    (1 ≤ A.cost α K ∧ A.cost α K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞)) ∧
      ∀ p : S → ℝ, IsLetterWeights p → A.IsStationary p α →
        ∃ w : List S, (w.length : ℕ∞) = A.cost α K ∧ A.Raises α K w :=
  sec2_cost_bounds_proved A hA α hpos K hne hprop

/-- Lemma 2.3 (orbit lemma), tex:313, the case `x ∈ K`. -/
theorem lem_2_3_in (x : Q) (K : Finset Q) (hfin : A.esc x K ≠ ⊤) (hx : x ∈ K) : A.esc x K ≤ K.card :=
  lem_2_3_in_proved A x K hfin hx

/-- Lemma 2.3, tex:313, the case `x ∉ K`. -/
theorem lem_2_3_out (x : Q) (K : Finset Q) (hfin : A.esc x K ≠ ⊤) (hx : x ∉ K) :
    A.esc x K ≤ ((Fintype.card Q - K.card : ℕ) : ℕ∞) :=
  lem_2_3_out_proved A x K hfin hx

/-- Lemma 2.3, tex:314: finiteness for strongly connected automata. -/
theorem lem_2_3_fin (hsc : A.StronglyConnected) (x : Q) (K : Finset Q) (hne : K.Nonempty)
    (hprop : K ≠ Finset.univ) : A.esc x K ≠ ⊤ :=
  lem_2_3_fin_proved A hsc x K hne hprop

/-- Lemma 2.4 (tier lemma), tex:327-330. -/
theorem lem_2_4 (hA : A.Synchronizing) (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (j : ℕ)
    (hj : 2 ≤ j) (hjn : j ≤ Fintype.card Q) :
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      ((Fintype.card Q - j + 1 : ℕ) : ℕ∞) ≤ A.cost α T)).card ≤ 2 ^ j - 2 :=
  lem_2_4_proved A hA hsc α hpos j hj hjn

/-- Lemma 2.4, tex:330: at most two sets have `m(S) = n-1`. -/
theorem lem_2_4_two (hA : A.Synchronizing) (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) :
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      A.cost α T = ((Fintype.card Q - 1 : ℕ) : ℕ∞))).card ≤ 2 :=
  lem_2_4_two_proved A hA hsc α hpos

/-- Lemma 2.4, tex:330: at most six sets have `m(S) ≥ n-2`. -/
theorem lem_2_4_six (hA : A.Synchronizing) (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q) :
    (Finset.univ.filter (fun T : Finset Q => T.Nonempty ∧ T ≠ Finset.univ ∧
      ((Fintype.card Q - 2 : ℕ) : ℕ∞) ≤ A.cost α T)).card ≤ 6 :=
  lem_2_4_six_proved A hA hsc α hpos

/-- tex:336-341, equation (2.2) (telescope) and `δ_c 1 = 0`. -/
theorem eq_2_2 (α : Q → ℝ) (w : List S) :
    Matrix.vecMul α (A.Mw w) - α =
        ∑ i : Fin w.length, Matrix.vecMul (A.delta α (w.get i)) (A.Mw (w.drop (i.1 + 1))) ∧
      ∀ c : S, A.delta α c ⬝ᵥ (fun _ => (1 : ℝ)) = 0 :=
  eq_2_2_proved A α w

/-- Lemma 2.4, proof step (i), tex:343-346. -/
theorem lem_2_4_i (α : Q → ℝ) (T : Finset Q) (k : ℕ) :
    ((k + 1 : ℕ) : ℕ∞) ≤ A.cost α T ↔ ∀ lam ∈ A.Dk α k, lam ⬝ᵥ ind T = 0 :=
  lem_2_4_i_proved A α T k

/-- Lemma 2.4, proof step (ii), tex:348-355: `dim D_k ≥ min(k, n-1)`. -/
theorem lem_2_4_ii (hA : A.Synchronizing) (hsc : A.StronglyConnected) (α : Q → ℝ) (hpos : ∀ q, 0 < α q)
    (k : ℕ) : min k (Fintype.card Q - 1) ≤ Module.finrank ℝ (A.Dk α k) :=
  lem_2_4_ii_proved A hA hsc α hpos k

/-- Remark 2.5, tex:367-369: `U_{k+1} = ℝ αᵀ ⊕ D_k`. -/
theorem rem_2_5_direct (α : Q → ℝ) (hQ : wt α Finset.univ ≠ 0) (k : ℕ) :
    A.Uk α (k + 1) = (ℝ ∙ α) ⊔ A.Dk α k ∧ Disjoint (ℝ ∙ α) (A.Dk α k) :=
  rem_2_5_direct_proved A α hQ k

/-! ## Section 3 (a stationary vector constant off one state)
Rows after the scaling of tex:386 use `α = alphaOff x t` (`1` off `x`, `t` at `x`). -/

/-- Theorem 3.1, tex:378-382. For some letter weights, the weighted transition matrix has a positive stationary vector constant on the complement of one state. -/
theorem thm_3_1 (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (α : Q → ℝ) (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) (x : Q)
    (hconst : ∀ q q', q ≠ x → q' ≠ x → α q = α q') :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_3_1_proved A hA hn p hp α hα hpos x hconst

/-- tex:386-387: `α(K) = |K| + g [x ∈ K]` and `α(Q) = n - 1 + t`, `g = t - 1`. -/
theorem sec3_alpha_formula (x : Q) (t : ℝ) :
    (∀ K : Finset Q, wt (alphaOff x t) K = K.card + (t - 1) * ein x K) ∧
      wt (alphaOff x t) Finset.univ = Fintype.card Q - 1 + t :=
  sec3_alpha_formula_proved x t

/-- Lemma 3.2(a) (levels), tex:394. -/
theorem lem_3_2_a (x : Q) (t : ℝ) (K K' : Finset Q) :
    wt (alphaOff x t) K' - wt (alphaOff x t) K = ((K'.card : ℝ) - K.card) + (t - 1) * (ein x K' - ein x K) :=
  lem_3_2_a_proved x t K K'

/-- Lemma 3.2(b), tex:395-397. -/
theorem lem_3_2_b (x : Q) (t : ℝ) (hg : ¬ ∃ z : ℤ, t - 1 = z) :
    (∀ K K' : Finset Q, wt (alphaOff x t) K' = wt (alphaOff x t) K ↔ K'.card = K.card ∧ (x ∈ K' ↔ x ∈ K)) ∧
      ∀ K : Finset Q,
        A.cost (alphaOff x t) K = minLen (fun w => (A.pre K w).card ≠ K.card ∨ A.MovesAcross x K w) ∧
          A.cost (alphaOff x t) K ≤ A.esc x K ∧
          ∀ w : List S, (w.length : ℕ∞) = A.cost (alphaOff x t) K → A.Raises (alphaOff x t) K w →
            A.MovesAcross x K w → A.cost (alphaOff x t) K = A.esc x K :=
  lem_3_2_b_proved A x t hg

/-- Lemma 3.2(c), tex:398-400. -/
theorem lem_3_2_c (x : Q) (t : ℝ) (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) (K K' : Finset Q)
    (hlt : wt (alphaOff x t) K < wt (alphaOff x t) K') :
    K.card ≤ K'.card ∧ (K'.card = K.card → (1 < t → x ∉ K ∧ x ∈ K') ∧ (t < 1 → x ∈ K ∧ x ∉ K')) :=
  lem_3_2_c_proved x t h0 h2 h1 K K' hlt

/-- tex:408-410: a raising word that keeps the size of an expensive set moves `x` across it and makes it cheap; a
raising word always enlarges a cheap set. -/
theorem sec3_expensive_cheap (x : Q) (t : ℝ) (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) (K : Finset Q) (w : List S)
    (hw : A.Raises (alphaOff x t) K w) :
    ((A.pre K w).card = K.card → Expensive x t K → A.MovesAcross x K w ∧ ¬ Expensive x t (A.pre K w)) ∧
      (¬ Expensive x t K → K.card < (A.pre K w).card) :=
  sec3_expensive_cheap_proved A x t h0 h2 h1 K w hw

/-- Method, tex:194-196. When the first raising step preserves size, the individual bounds occur in the printed order for t < 1 and in reverse order for t > 1. -/
theorem method_pair_order (hsc : A.StronglyConnected) (x : Q) (t : ℝ)
    (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) (K K' : Finset Q)
    (hne : K.Nonempty) (hp : K ≠ Finset.univ) (hne' : K'.Nonempty) (hp' : K' ≠ Finset.univ)
    (hraise : wt (alphaOff x t) K < wt (alphaOff x t) K') (hsame : K'.card = K.card) :
    (t < 1 → A.cost (alphaOff x t) K ≤ K.card ∧ A.cost (alphaOff x t) K' ≤ ((Fintype.card Q - K.card : ℕ) : ℕ∞)) ∧
    (1 < t → A.cost (alphaOff x t) K ≤ ((Fintype.card Q - K.card : ℕ) : ℕ∞) ∧ A.cost (alphaOff x t) K' ≤ K.card) :=
  method_pair_order_proved A hsc x t h0 h2 h1 K K' hne hp hne' hp' hraise hsame

/-- Proposition 3.3, tex:412-414. -/
theorem prop_3_3 (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p) (x : Q)
    (t : ℝ) (hα : A.IsStationary p (alphaOff x t)) (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) (K : Finset Q)
    (hne : K.Nonempty) (hprop : K ≠ Finset.univ) :
    A.ext K ≤ (Fintype.card Q : ℕ∞) ∧ (¬ Expensive x t K → A.ext K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞)) :=
  prop_3_3_proved A hA hn p hp x t hα h0 h2 h1 K hne hprop

/-- tex:427: a synchronizing automaton with `n ≥ 2` states has a merging letter: `|{q} c⁻¹| ≥ 2`. -/
theorem thm_3_1_merging (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) :
    ∃ (c : S) (q : Q), 2 ≤ (A.pre {q} [c]).card :=
  thm_3_1_merging_proved A hA hn

/-- tex:429-431: the case `t = 1` (Kari's and Steinberg's bound). -/
theorem thm_3_1_case_t1 (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (hα : A.IsStationary p (fun _ => 1)) :
    (∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → A.ext K ≤ ((Fintype.card Q - 1 : ℕ) : ℕ∞)) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) :=
  thm_3_1_case_t1_proved A hA hn p hp hα

/-- tex:433-434: the case `0 < t < 2`, `t ≠ 1`: `rt ≤ 1 + (n-2) n`. -/
theorem thm_3_1_case_A (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (x : Q) (t : ℝ) (hα : A.IsStationary p (alphaOff x t)) (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) :
    A.rt ≤ ((1 + (Fintype.card Q - 2) * Fintype.card Q : ℕ) : ℕ∞) :=
  thm_3_1_case_A_proved A hA hn p hp x t hα h0 h2 h1

/-- tex:436-439 (and tex:201-202): `t` a positive integer: starting from `{x}`, `rt ≤ (n-1)^2`. -/
theorem thm_3_1_case_int (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (x : Q) (k : ℕ) (hk : 1 ≤ k) (hα : A.IsStationary p (alphaOff x k)) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_3_1_case_int_proved A hA hn p hp x k hk hα

/-- tex:441-457: `t > 2` not an integer. -/
theorem thm_3_1_case_nonint (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (x : Q) (t : ℝ) (hα : A.IsStationary p (alphaOff x t)) (h2 : 2 < t)
    (hnz : ¬ ∃ z : ℤ, t = z) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_3_1_case_nonint_proved A hA hn p hp x t hα h2 hnz

/-- tex:199-201 and tex:452-455: in the case `t > 2` not an integer, a lose step and the next gain step of a process
from `{x}` cost at most `n - 2` letters together. -/
theorem thm_3_1_nonint_pair (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ)
    (hp : IsLetterWeights p) (x : Q) (t : ℝ) (hα : A.IsStationary p (alphaOff x t)) (h2 : 2 < t)
    (hnz : ¬ ∃ z : ℤ, t = z) (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ)
    (hP : A.IsProcess (alphaOff x t) K w J) (hK0 : K 0 = {x}) (j j' : ℕ) (hjj : j < j') (hj' : j' < J)
    (hlose : x ∈ K j ∧ x ∉ K (j + 1)) (hfree : ∀ i, j < i → i ≤ j' → x ∉ K i) (hgain : x ∈ K (j' + 1)) :
    (w j).length + (w j').length ≤ Fintype.card Q - 2 :=
  thm_3_1_nonint_pair_proved A hA hn p hp x t hα h2 hnz K w J hP hK0 j j' hjj hj' hlose hfree hgain

/-- tex:199-200 and tex:452-455: in a process for `alphaOff x t`, the move of `x` out of the set (a lose step)
enlarges the set by more than `t - 1` states, and a step with `x` outside both sets (a free step) enlarges the set,
so the set does not shrink before the move back: while `x` stays outside (`K_i`, `j < i ≤ j'`), every `K_i` is at
least as large as `K_{j+1}`. (No condition on `t` is needed.) -/
theorem meth_nonint_steps (x : Q) (t : ℝ) (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ)
    (hP : A.IsProcess (alphaOff x t) K w J) :
    (∀ j < J, x ∈ K j → x ∉ K (j + 1) → t - 1 < ((K (j + 1)).card : ℝ) - (K j).card) ∧
      (∀ j < J, x ∉ K j → x ∉ K (j + 1) → (K j).card < (K (j + 1)).card) ∧
      (∀ j j', j' < J → (∀ i, j < i → i ≤ j' → x ∉ K i) → ∀ i, j < i → i ≤ j' →
        (K (j + 1)).card ≤ (K i).card) :=
  meth_nonint_steps_proved A x t K w J hP

/-- Remark 3.4, tex:463-465: for an integer `t ≥ 1`, the denominators of `α/α(Q)` have least common multiple
`Λ = n - 1 + t`. -/
theorem rem_3_4_L (hn : 2 ≤ Fintype.card Q) (x : Q) (k : ℕ) (hk : 1 ≤ k) :
    Finset.univ.lcm (fun q : Q => (((if q = x then (k : ℚ) else 1)) / ((Fintype.card Q : ℚ) - 1 + k)).den) =
      Fintype.card Q - 1 + k :=
  rem_3_4_L_proved hn x k hk

/-- Remark 3.4, tex:465-466: `1 + (n-1)(Λ-2) = 1 + (n-1)(n+t-3)`; Kari's bound at `t = 1`, `(n-1)^2 + 1` at `t = 2`,
and more for larger `t`. -/
theorem rem_3_4_vals (n : ℕ) (hn : 2 ≤ n) :
    (∀ k : ℕ, 1 ≤ k → (1 + (n - 1) * ((n - 1 + k) - 2) : ℤ) = 1 + (n - 1) * (n + k - 3)) ∧
      (1 + ((n : ℤ) - 1) * (n + 1 - 3) = 1 + (n - 2) * (n - 1)) ∧
      (1 + ((n : ℤ) - 1) * (n + 2 - 3) = (n - 1) ^ 2 + 1) ∧
      ∀ k k' : ℕ, k < k' → (1 + ((n : ℤ) - 1) * (n + k - 3)) < 1 + (n - 1) * (n + k' - 3) :=
  rem_3_4_vals_proved n hn

/-- Remark 3.4, tex:466-468: Berlinkov's level count: a positive stationary vector with integer entries and sum `Λ`
gives `rt ≤ 1 + (n-1)(Λ-2)`. -/
theorem rem_3_4_level_count (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (u : Q → ℕ) (hu : ∀ q, 0 < u q) (hstat : A.IsStationary p (fun q => (u q : ℝ))) :
    A.rt ≤ ((1 + (Fintype.card Q - 1) * (∑ q, u q - 2) : ℕ) : ℕ∞) :=
  rem_3_4_level_count_proved A hA hn p hp u hu hstat

/-- Remark 3.4, tex:472: `W = Λ`: for a positive integer vector with coprime entries and sum `W`, the denominators of
the normalized vector have least common multiple `W`. -/
theorem rem_3_4_w_eq_L {ι : Type*} [Fintype ι] (u : ι → ℕ) (hu : ∀ i, 0 < u i) (hgcd : Finset.univ.gcd u = 1) :
    Finset.univ.lcm (fun i => ((u i : ℚ) / (∑ j, u j : ℕ)).den) = ∑ j, u j :=
  rem_3_4_w_eq_L_proved u hu hgcd

/-- Remark 3.4, tex:472-474: under the hypothesis of Theorem 3.1 with `t = i/j` in lowest terms, the positive integer
stationary vector with coprime entries has sum `W = (n-1) j + i`; `W = n` only for `t = 1`; otherwise `W ≥ n + 1` and
`W² - 3W + 3 ≥ n² - n + 1 > (n-1)²`. -/
theorem rem_3_4_w (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p) (x : Q)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hcop : Nat.Coprime i j)
    (hα : A.IsStationary p (alphaOff x ((i : ℝ) / j))) (u : Q → ℕ) (hu : ∀ q, 0 < u q)
    (hgcd : Finset.univ.gcd u = 1) (hstat : A.IsStationary p (fun q => (u q : ℝ))) :
    ∑ q, u q = (Fintype.card Q - 1) * j + i ∧ (∑ q, u q = Fintype.card Q ↔ i = 1 ∧ j = 1) ∧
      (¬ (i = 1 ∧ j = 1) → Fintype.card Q + 1 ≤ ∑ q, u q ∧
        (Fintype.card Q : ℤ) ^ 2 - Fintype.card Q + 1 ≤ ((∑ q, u q : ℕ) : ℤ) ^ 2 - 3 * (∑ q, u q : ℕ) + 3) ∧
      ((Fintype.card Q : ℤ) - 1) ^ 2 < (Fintype.card Q : ℤ) ^ 2 - Fintype.card Q + 1 :=
  rem_3_4_w_proved A hA hn p hp x i j hi hj hcop hα u hu hgcd hstat

/-! ## Section 4 (degree one)
For a witness `W` of degree one, `x` is its exceptional state: `W.X = {x}`. -/

/-- Theorem 4.1, tex:501-503: the bound. -/
theorem thm_4_1 (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (hqe : QuasiEulerian A 1) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_4_1_proved A hA hn hqe

/-- tex:506-510: the edges leaving `x` end at `x` or at `s`; `in_p(x) = y + z`; `in_p(s) = 2 - y - z`. -/
theorem sec4_inW_xs (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) :
    (∀ b, A.step x b = x ∨ A.step x b = W.s) ∧ A.inW W.p x = A.yIn W.E W.p x + A.zLoop W.p x ∧
      A.inW W.p W.s = 2 - A.yIn W.E W.p x - A.zLoop W.p x :=
  sec4_inW_xs_proved A W x hx

/-- Lemma 4.2, tex:512-514. -/
theorem lem_4_2 (W : QEWitness A 1) (x : Q) (hx : W.X = {x}) (hz : A.zLoop W.p x < 1) :
    A.IsStationary W.p (A.alphaDeg1 W.E W.p x) :=
  lem_4_2_proved A W x hx hz

/-- tex:523-527: the case `z < 1`, `y > 0`; strong connectivity holds exactly in this case. -/
theorem thm_4_1_case_sc (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) :
    (A.zLoop W.p x < 1 → 0 < A.yIn W.E W.p x → A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞)) ∧
      (A.StronglyConnected ↔ A.zLoop W.p x < 1 ∧ 0 < A.yIn W.E W.p x) :=
  thm_4_1_case_sc_proved A hA hn W x hx

/-- tex:529-535: the case `z = 1`. -/
theorem thm_4_1_case_z1 (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) (hz : A.zLoop W.p x = 1) :
    0 < A.yIn W.E W.p x ∧ A.inW W.p x = 1 + A.yIn W.E W.p x ∧ A.inW W.p W.s = 1 - A.yIn W.E W.p x ∧
      (∀ T : Finset Q, x ∈ T → ∑ b, W.p b * ((A.pre T [b]).card : ℝ) = T.card + A.yIn W.E W.p x * (1 - ein W.s T) ∧
        (T.card : ℝ) ≤ ∑ b, W.p b * ((A.pre T [b]).card : ℝ)) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) :=
  thm_4_1_case_z1_proved A hA hn W x hx hz

/-- tex:537-543: the case `z < 1`, `y = 0`. -/
theorem thm_4_1_case_y0 (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (W : QEWitness A 1) (x : Q)
    (hx : W.X = {x}) (hz : A.zLoop W.p x < 1) (hy : A.yIn W.E W.p x = 0) :
    ∃ hE : A.IsClosed W.E, (∀ r, (A.restrict W.E hE).inW W.p r = 1) ∧
      (3 ≤ Fintype.card Q →
        (A.restrict W.E hE).rt ≤ ((1 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞)) ∧
      (3 ≤ Fintype.card Q → A.rt ≤ ((2 + (Fintype.card Q - 3) * (Fintype.card Q - 2) : ℕ) : ℕ∞)) ∧
      A.rt ≤ ((1 + (Fintype.card Q - 2) * (Fintype.card Q - 1) : ℕ) : ℕ∞) :=
  thm_4_1_case_y0_proved A hA hn W x hx hz hy

/-- tex:545-547 (and tex:86): `C_n` with `E = {1, …, n-1}`, `s = 1`, `x = 0` and any weights is a witness of degree
one. -/
theorem thm_4_1_cn_witness (n : ℕ) [NeZero n] (hn : 2 ≤ n) (p : Fin 2 → ℝ) (hp : IsLetterWeights p) :
    ∃ W : QEWitness (cerny n) 1, W.E = Finset.univ.erase 0 ∧ W.s = 1 ∧ W.p = p :=
  thm_4_1_cn_witness_proved n hn p hp

/-- Theorem 4.1, tex:503: the Cerny automata attain the bound. -/
theorem thm_4_1_attained (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (cerny n).Synchronizing ∧ QuasiEulerian (cerny n) 1 ∧ (cerny n).rt = (((n - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_4_1_attained_proved n hn

/-- Remark 4.3, tex:551: for `C_n`, `z = 0`, `y = p_b` and `t = p_b ∈ (0, 1)`. -/
theorem rem_4_3_cn_zyt (n : ℕ) [NeZero n] (hn : 2 ≤ n) (p : Fin 2 → ℝ) (hp : IsLetterWeights p) :
    (cerny n).zLoop p 0 = 0 ∧ (cerny n).yIn (Finset.univ.erase 0) p 0 = p 1 ∧
      (cerny n).yIn (Finset.univ.erase 0) p 0 / (1 - (cerny n).zLoop p 0) = p 1 ∧ 0 < p 1 ∧ p 1 < 1 :=
  rem_4_3_cn_zyt_proved n hn p hp

/-- Remark 4.3, tex:551-552: the bound `1 + (n-2) n` of the case `0 < t < 2` is attained (by `C_n`). -/
theorem rem_4_3_attained (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (cerny n).rt = ((1 + (n - 2) * n : ℕ) : ℕ∞) :=
  rem_4_3_attained_proved n hn

/-- Remark 4.3, tex:552: `K_0 = {1} a⁻¹ = {0, 1}`. -/
theorem rem_4_3_K0 (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (cerny n).pre {1} [0] = {0, 1} :=
  rem_4_3_K0_proved n hn

/-- Remark 4.3, tex:552-556: every chain of extensions of `C_n` from `K_0 = {0, 1}` with `|w_j| = ext(K_j)` yields
the reset word `w_{J-1} ⋯ w_0 a`, has `J = n - 2` steps, each of length exactly `n` and adding exactly one state. -/
theorem rem_4_3_chain (n : ℕ) [NeZero n] (hn : 2 ≤ n) (K : ℕ → Finset (Fin n)) (w : ℕ → List (Fin 2)) (J : ℕ)
    (hK0 : K 0 = {0, 1})
    (hstep : ∀ j < J, K j ≠ Finset.univ ∧ K (j + 1) = (cerny n).pre (K j) (w j) ∧
      ((w j).length : ℕ∞) = (cerny n).ext (K j) ∧ (K j).card < (K (j + 1)).card)
    (hJ : K J = Finset.univ) :
    (cerny n).IsReset ((((List.range J).reverse.map w).flatten) ++ [0]) ∧ J = n - 2 ∧
      ∀ j < J, (w j).length = n ∧ (K (j + 1)).card = (K j).card + 1 :=
  rem_4_3_chain_proved n hn K w J hK0 hstep hJ

/-- Figure 3 (tex:197 "where every bound is attained"; fig_c4_chain_float.tex:8-15 and the row labels of
fig_c4_chain.tex): the chain of preimages of `C_4` as drawn; the merging letter `a`, then `w₀ = abbb`, then
`w₁ = abbb`; the reset word `w₁ w₀ a = abbb abbb a` of length `1 + (n-2) n = 9 = (4-1)^2`; each extension takes
exactly `n = 4` letters; in each extension `x` leaves the start set `K` after exactly `|K|` letters (`{0,1}`: 2,
`{0,1,2}`: 3), and the set then reached, of the same size as `K` (`{2,3}`, `{1,2,3}`), grows after exactly `n - |K|`
further letters (2, 1). The bound "at most `n`" is Proposition 3.3 (row prop_3_3). -/
theorem fig3_c4_chain :
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
      ({1, 2, 3} : Finset (Fin 4)).card = ({0, 1, 2} : Finset (Fin 4)).card :=
  fig3_c4_chain_proved

/-- Remark 4.3, tex:558. A word enlarges the three-state set exactly when it maps Q into that set. -/
theorem rem_4_3_enlarges_iff (w : List (Fin 2)) :
    ({0, 1, 2} : Finset (Fin 4)).card < (ex43.pre {0, 1, 2} w).card ↔
      ex43.img Finset.univ w ⊆ {0, 1, 2} :=
  rem_4_3_enlarges_iff_proved w

/-- Remark 4.3, tex:559. Every word of length at most four has one of these six images, all containing state 3. -/
theorem rem_4_3_images (w : List (Fin 2)) (hw : w.length ≤ 4) :
    ex43.img Finset.univ w ∈
      ({Finset.univ, {0, 1, 3}, {1, 2, 3}, {0, 3}, {2, 3}, {1, 3}} : Finset (Finset (Fin 4))) ∧
      3 ∈ ex43.img Finset.univ w :=
  rem_4_3_images_proved w hw

/-- Remark 4.3, tex:557-561: the 4-state example `a = (0,0,1,3)`, `b = (3,1,3,2)`. The exact reset threshold 7 is supplementary. -/
theorem rem_4_3_t2_example :
    (∃ W : QEWitness ex43 1, W.E = {0, 1, 2} ∧ W.s = 2 ∧ W.p = fun _ => 1 / 2) ∧
      ex43.zLoop (fun _ => 1 / 2) 3 = 1 / 2 ∧ ex43.yIn {0, 1, 2} (fun _ => 1 / 2) 3 = 1 ∧
      ex43.yIn {0, 1, 2} (fun _ => 1 / 2) 3 / (1 - ex43.zLoop (fun _ => 1 / 2) 3) = 2 ∧
      ex43.ext {0, 1, 2} = 5 ∧ ex43.img Finset.univ [0, 0, 1, 0, 1] = {1, 2} ∧
      ex43.Synchronizing ∧ ex43.rt = 7 ∧ ex43.img Finset.univ [0, 0, 1, 0, 1, 0, 0] = {0} :=
  rem_4_3_t2_example_proved

/-- Remark 4.3, tex:556-557: the conclusion of Proposition 3.3 does not extend to `t = 2`: in the example, `t = 2`
(the vector `alphaOff 3 2` is stationary) and an extension of the nonempty proper set `{0, 1, 2}` needs more than
`n = 4` letters. -/
theorem rem_4_3_not_extend :
    ex43.IsStationary (fun _ => 1 / 2) (alphaOff 3 2) ∧ (4 : ℕ∞) < ex43.ext {0, 1, 2} :=
  rem_4_3_not_extend_proved

/-! ## Section 5.1 (automata that are not strongly connected) -/

/-- Theorem 5.1, tex:568-571. -/
theorem thm_5_1 (hA : A.Synchronizing) (hn : 3 ≤ Fintype.card Q) (d : ℕ) (hd : d ≤ 2) (hqe : QuasiEulerian A d)
    (hsc : ¬ A.StronglyConnected) : A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_5_1_proved A hA hn d hd hqe hsc

/-- tex:574-576: a synchronizing automaton has no two disjoint nonempty closed sets, intersections of closed sets are
closed, and there is exactly one minimal nonempty closed set; it lies in every nonempty closed set. -/
theorem sec5_unique_min_closed [Nonempty Q] (hA : A.Synchronizing) :
    (∀ C C' : Finset Q, C.Nonempty → C'.Nonempty → A.IsClosed C → A.IsClosed C' → ¬ Disjoint C C') ∧
      (∀ C C' : Finset Q, A.IsClosed C → A.IsClosed C' → A.IsClosed (C ∩ C')) ∧
      ∃! C : Finset Q, A.IsMinClosed C ∧ ∀ C' : Finset Q, C'.Nonempty → A.IsClosed C' → C ⊆ C' :=
  sec5_unique_min_closed_proved A hA

/-- tex:576-578: `A|_C` is strongly connected and synchronizing, every state reaches `C`, and `R = Q \ C` is nonempty
when `A` is not strongly connected. -/
theorem sec5_restrict (hA : A.Synchronizing) (C : Finset Q) (hmin : A.IsMinClosed C) (hC : A.IsClosed C) :
    (A.restrict C hC).StronglyConnected ∧ (A.restrict C hC).Synchronizing ∧ (∀ q, ∃ w, A.act q w ∈ C) ∧
      (¬ A.StronglyConnected → (Finset.univ \ C).Nonempty) :=
  sec5_restrict_proved A hA C hmin hC

/-- Lemma 5.2 (weight count), tex:580-582 (for a witness of any degree). -/
theorem lem_5_2 {d : ℕ} (W : QEWitness A d) (T : Finset Q) (hT : T ⊆ W.E.erase W.s) (hne : T.Nonempty)
    (hin : ∀ q b, A.step q b ∈ T → q ∈ T) : A.IsClosed T :=
  lem_5_2_proved A W T hT hne hin

/-- Lemma 5.3 (push), tex:590-592, for every nonempty closed set `C` (the text: the minimal one). -/
theorem lem_5_3 (hA : A.Synchronizing) (C : Finset Q) (hne : C.Nonempty) (hC : A.IsClosed C) :
    A.rt ≤ (((Finset.univ \ C).card ^ 2 : ℕ) : ℕ∞) + (A.restrict C hC).rt :=
  lem_5_3_proved A hA C hne hC

/-- tex:595-599 and tex:208-209: a word of length at most `|R|^2` maps `Q` into `C`. -/
theorem lem_5_3_push_word (hA : A.Synchronizing) (C : Finset Q) (hne : C.Nonempty) (hC : A.IsClosed C) :
    ∃ u : List S, u.length ≤ (Finset.univ \ C).card ^ 2 ∧ ∀ q, A.act q u ∈ C :=
  lem_5_3_push_word_proved A hA C hne hC

/-- tex:613-614, tex:209, tex:627: `j² + (n−1−j)² ≤ (n−1)²` for `j ≤ n−1`, with j = |R|. -/
theorem arith_r_sq (n r : ℕ) (hr : r ≤ n - 1) : r ^ 2 + (n - 1 - r) ^ 2 ≤ (n - 1) ^ 2 :=
  arith_r_sq_proved n r hr

/-- tex:619: a synchronizing automaton with two states has reset threshold `1`. -/
theorem sec5_two_state_rt (hA : A.Synchronizing) (h2 : Fintype.card Q = 2) : A.rt = 1 :=
  sec5_two_state_rt_proved A hA h2

/-- Remark 5.4, tex:624-627: any degree `d`, not strongly connected. -/
theorem rem_5_4_a (hA : A.Synchronizing) {d : ℕ} (W : QEWitness A d) (hsc : ¬ A.StronglyConnected)
    (C : Finset Q) (hmin : A.IsMinClosed C) (hC : A.IsClosed C) :
    (C ⊆ W.X ∨ ((Finset.univ \ C) ⊆ W.X ∧ (A.restrict C hC).StronglyConnected ∧
        (QuasiEulerian (A.restrict C hC) (d - (Finset.univ \ C).card) ∨
          (A.restrict C hC).IsStationary W.p (fun _ => 1)))) ∧
      A.rt ≤ (((Finset.univ \ C).card ^ 2 : ℕ) : ℕ∞) + (A.restrict C hC).rt :=
  rem_5_4_a_proved A hA W hsc C hmin hC

end General

section Reduction

/-- Remark 5.4, tex:627-630: the Cerny bound for degree `d` automata that are not strongly connected follows from
Theorem 3.1, the bound for strongly connected automata of degree `1, …, d-1`, and the bound for automata with at most
`d` states. -/
theorem rem_5_4_reduction (S : Type v) [Fintype S] (d : ℕ)
    (H1 : ∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), B.Synchronizing →
      B.StronglyConnected → (∃ d', 1 ≤ d' ∧ d' ≤ d - 1 ∧ QuasiEulerian B d') →
      B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞))
    (H2 : ∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), Fintype.card Q' ≤ d →
      B.Synchronizing → B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞))
    (Q : Type u) [Fintype Q] [DecidableEq Q] (A : Automaton Q S) (hA : A.Synchronizing)
    (hqe : QuasiEulerian A d) (hsc : ¬ A.StronglyConnected) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  rem_5_4_reduction_proved S d H1 H2 Q A hA hqe hsc

/-- Remark 5.4, tex:630: for `d ≤ 2` the hypotheses of `rem_5_4_reduction` hold (Theorem 4.1, and automata with at most
two states). -/
theorem rem_5_4_d2 (S : Type v) [Fintype S] (d : ℕ) (hd : d ≤ 2) :
    (∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), B.Synchronizing →
      B.StronglyConnected → (∃ d', 1 ≤ d' ∧ d' ≤ d - 1 ∧ QuasiEulerian B d') →
      B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞)) ∧
    (∀ (Q' : Type u) [Fintype Q'] [DecidableEq Q'] (B : Automaton Q' S), Fintype.card Q' ≤ d →
      B.Synchronizing → B.rt ≤ (((Fintype.card Q' - 1) ^ 2 : ℕ) : ℕ∞)) :=
  rem_5_4_d2_proved S d hd

end Reduction

section General2

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-! ## Sections 5.2-5.3 (the stationary vector; a congruence) -/

/-- Lemma 5.5, tex:638-643 (for every degree; the text: `d ≥ 1`). The row vector y gives t = y(I−Z)⁻¹. Route without Perron-Frobenius: `I - Z` invertible
by the largest `|u_x|` of a vector with `Z u = u`; positivity as the support of a nonnegative stationary vector is
closed (Proofs/LinAlg.lean). -/
theorem lem_5_5 (hsc : A.StronglyConnected) {d : ℕ} (W : QEWitness A d) :
    IsUnit (1 - A.Zmat W.E W.p) ∧ A.IsStationary W.p (A.alphaStat W.E W.p) ∧ ∀ q, 0 < A.alphaStat W.E W.p q :=
  lem_5_5_proved A hsc W

/-- tex:653-654: for a strongly connected automaton and letter weights, the stationary vectors are the multiples of one
positive vector. -/
theorem lem_5_5_unique (hsc : A.StronglyConnected) [Nonempty Q] (p : S → ℝ) (hp : IsLetterWeights p) :
    ∃ π : Q → ℝ, (∀ q, 0 < π q) ∧ A.IsStationary p π ∧ ∀ α, A.IsStationary p α → ∃ c : ℝ, α = c • π :=
  lem_5_5_unique_proved A hsc p hp

/-- Proposition 5.6, tex:659-662: the first bound. -/
theorem prop_5_6 (hA : A.Synchronizing) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hblock : A.IsBlockPair x₁ x₂) : A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  prop_5_6_proved A hA W x₁ x₂ hX h12 hblock

/-- Proposition 5.6, tex:662: the strongly connected case. -/
theorem prop_5_6_sc (hA : A.Synchronizing) (hsc : A.StronglyConnected) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (hblock : A.IsBlockPair x₁ x₂) :
    A.rt ≤ (((Fintype.card Q - 2) ^ 2 + 1 : ℕ) : ℕ∞) :=
  prop_5_6_sc_proved A hA hsc W x₁ x₂ hX h12 hblock

/-- tex:209-211 and tex:666-676: the quotient automaton is synchronizing, `rt(A) ≤ rt(A') + 1`, and it satisfies the
hypothesis of Theorem 3.1 (a positive stationary vector constant off one state, for the same weights). -/
theorem prop_5_6_quot_hyp (hA : A.Synchronizing) (hsc : A.StronglyConnected) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (hblock : A.IsBlockPair x₁ x₂) :
    (A.blockQuot x₁ x₂ h12).Synchronizing ∧ A.rt ≤ (A.blockQuot x₁ x₂ h12).rt + 1 ∧
      2 ≤ Fintype.card {q : Q // q ≠ x₂} ∧
      ∃ α' : {q : Q // q ≠ x₂} → ℝ, (A.blockQuot x₁ x₂ h12).IsStationary W.p α' ∧ (∀ q, 0 < α' q) ∧
        ∃ x', ∀ q q', q ≠ x' → q' ≠ x' → α' q = α' q' :=
  prop_5_6_quot_hyp_proved A hA hsc W x₁ x₂ hX h12 hblock

/-! ## Section 6 and the general rows of Section 5.4 -/

/-- tex:682-683: for `n ≤ 3` every synchronizing automaton has `rt ≤ (n^3-n)/6 ≤ (n-1)^2` (every alphabet). -/
theorem sec54_small_n (hA : A.Synchronizing) (hn : Fintype.card Q ≤ 3) :
    A.rt ≤ (((Fintype.card Q ^ 3 - Fintype.card Q) / 6 : ℕ) : ℕ∞) ∧
      (Fintype.card Q ^ 3 - Fintype.card Q) / 6 ≤ (Fintype.card Q - 1) ^ 2 :=
  sec54_small_n_proved A hA hn

/-- tex:776-781 (and tex:441-443): from a nonempty proper set an extension process exists. -/
theorem sec54_process_exists (hA : A.Synchronizing) (p : S → ℝ) (hp : IsLetterWeights p) (α : Q → ℝ)
    (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) (K₀ : Finset Q) (hne : K₀.Nonempty) :
    ∃ (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ), K 0 = K₀ ∧ A.IsProcess α K w J :=
  sec54_process_exists_proved A hA p hp α hα hpos K₀ hne

/-- tex:776-781: properties of an extension process: the values rise strictly, no set is visited twice, every visited
set is nonempty, the words map `Q` into `K_0`, and `rt ≤ ∑ m(K)` (`+ 1` from `K_0 = {q} c⁻¹`). -/
theorem sec54_process_props (α : Q → ℝ) (hpos : ∀ q, 0 < α q) (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ)
    (hP : A.IsProcess α K w J) (hne : (K 0).Nonempty) :
    (∀ i j, i < j → j ≤ J → wt α (K i) < wt α (K j)) ∧ (∀ i j, i ≤ J → j ≤ J → K i = K j → i = j) ∧
      (∀ j ≤ J, (K j).Nonempty) ∧ (∀ q, A.act q (((List.range J).reverse.map w).flatten) ∈ K 0) ∧
      ((∃ r, K 0 = {r}) → A.rt ≤ ((∑ j ∈ Finset.range J, (w j).length : ℕ) : ℕ∞)) ∧
      (∀ (r : Q) (c : S), K 0 = A.pre {r} [c] → A.rt ≤ ((∑ j ∈ Finset.range J, (w j).length + 1 : ℕ) : ℕ∞)) :=
  sec54_process_props_proved A α hpos K w J hP hne

/-- Corollary 5.15, tex:946-950: every synchronizing automaton with `n ≥ 7` states that has a positive stationary vector
with integer entries and `α(Q) - max α ≤ n` (for some letter weights) has `rt ≤ n^2 - 3n + 8`, and is strongly
connected (Lemma 2.1). -/
theorem rem_5_15_general (hA : A.Synchronizing) (hn : 7 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (u : Q → ℕ) (hu : ∀ q, 0 < u q) (hstat : A.IsStationary p (fun q => (u q : ℝ)))
    (hmax : ∃ q₀, ∑ q, u q ≤ Fintype.card Q + u q₀) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧ A.StronglyConnected :=
  rem_5_15_general_proved A hA hn p hp u hu hstat hmax

/-- Corollary 5.15, tex:947-951: over every alphabet, a synchronizing strongly connected automaton with `n ≥ 7` states and
a witness of degree two in an integer class `{2, k}`: the vector of Lemma 5.5 has integer entries, `α(Q) - max α ≤ n`,
and `rt ≤ (n-1)^2`. -/
theorem rem_5_15_2k (hA : A.Synchronizing) (hsc : A.StronglyConnected) (hn : 7 ≤ Fintype.card Q)
    (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (k : ℕ) (hk : 1 ≤ k)
    (hcl : (A.alphaStat W.E W.p x₁ = 2 ∧ A.alphaStat W.E W.p x₂ = k) ∨
      (A.alphaStat W.E W.p x₁ = k ∧ A.alphaStat W.E W.p x₂ = 2)) :
    (∀ q, ∃ m : ℕ, A.alphaStat W.E W.p q = m) ∧
      (∃ q₀, wt (A.alphaStat W.E W.p) Finset.univ ≤ Fintype.card Q + A.alphaStat W.E W.p q₀) ∧
      A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  rem_5_15_2k_proved A hA hsc hn W x₁ x₂ hX h12 k hk hcl

/-- Corollary 5.15, tex:950. The proper levels lie between the starting maximum and the total minus one. Every step increases the value by at least one. -/
theorem cor_5_15_levels (u : Q → ℕ) (hu : ∀ q, 0 < u q) (q₀ : Q)
    (K : ℕ → Finset Q) (w : ℕ → List S) (J : ℕ) (hK : K 0 = {q₀})
    (hP : A.IsProcess (fun q => (u q : ℝ)) K w J) (hmax : (∑ q, u q) - u q₀ ≤ Fintype.card Q) :
    (∀ j < J, u q₀ ≤ ∑ q ∈ K j, u q ∧ (∑ q ∈ K j, u q) ≤ (∑ q, u q)-1) ∧
      J ≤ (∑ q, u q)-u q₀ ∧ (∑ q, u q)-u q₀ ≤ Fintype.card Q :=
  cor_5_15_levels_proved A u hu q₀ K w J hK hP hmax

/-- Corollary 5.15, tex:951. In class {2,k}, the maximum is max(2,k) and subtracting it from the total leaves at most n. -/
theorem cor_5_15_mass (hn : 7 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁,x₂}) (h12 : x₁ ≠ x₂) (k : ℕ) (hk : 1 ≤ k)
    (hcl : (A.alphaStat W.E W.p x₁ = 2 ∧ A.alphaStat W.E W.p x₂ = k) ∨
      (A.alphaStat W.E W.p x₁ = k ∧ A.alphaStat W.E W.p x₂ = 2)) :
    let α := A.alphaStat W.E W.p
    ∃ q₀, (∀ q, α q ≤ α q₀) ∧ α q₀ = max 2 (k : ℝ) ∧
      wt α Finset.univ - α q₀ = Fintype.card Q + k - max 2 (k : ℝ) ∧
      wt α Finset.univ - α q₀ ≤ Fintype.card Q :=
  cor_5_15_mass_proved A hn W x₁ x₂ hX h12 k hk hcl

/-- Corollary 5.15, tex:946-950. Comparison of the two bounds for seven or more states. -/
theorem cor_5_15_comparison (n : ℕ) (hn : 7 ≤ n) : n ^ 2 + 8 - 3 * n ≤ (n - 1) ^ 2 :=
  Prop514.arith_seven n hn

/-- Corollary 5.15, tex:946-950. Both bounds for each integer class {2,k}. -/
theorem cor_5_15_2k_bound (hA : A.Synchronizing) (hsc : A.StronglyConnected) (hn : 7 ≤ Fintype.card Q)
    (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (k : ℕ) (hk : 1 ≤ k)
    (hcl : (A.alphaStat W.E W.p x₁ = 2 ∧ A.alphaStat W.E W.p x₂ = k) ∨
      (A.alphaStat W.E W.p x₁ = k ∧ A.alphaStat W.E W.p x₂ = 2)) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧
      Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q ≤ (Fintype.card Q - 1) ^ 2 :=
  cor_5_15_2k_bound_proved A hA hsc hn W x₁ x₂ hX h12 k hk hcl

/-- tex:973: every automaton with `n ≥ 2` states over a nonempty alphabet is quasi-Eulerian of degree `n - 1`
(with `E = {s}`). -/
theorem sec6_qe_n_minus_1 [Nonempty S] (hn : 2 ≤ Fintype.card Q) : QuasiEulerian A (Fintype.card Q - 1) :=
  sec6_qe_n_minus_1_proved A hn

/-- tex:980: Theorem 3.1 answers the second question of Question 6.1 when one of the two values is taken at a single
state. -/
theorem sec6_thm31_answers (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p)
    (α : Q → ℝ) (hα : A.IsStationary p α) (hpos : ∀ q, 0 < α q) (v₁ v₂ : ℝ)
    (hrange : ∀ q, α q = v₁ ∨ α q = v₂) (hone : (Finset.univ.filter (fun q => α q = v₁)).card = 1) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  sec6_thm31_answers_proved A hA hn p hp α hα hpos v₁ v₂ hrange hone

end General2

/-- tex:972-973: at `d = n - 1` the general cubic bound is smaller than Berlinkov's: `(n^3 - n)/6 < 2^d (n-d+1)(n-1)`. -/
theorem sec6_cubic_smaller (n : ℕ) (hn : 2 ≤ n) :
    (n ^ 3 - n) / 6 < 2 ^ (n - 1) * (n - (n - 1) + 1) * (n - 1) :=
  sec6_cubic_smaller_proved n hn

/-- Prop 5.12, tex:854: `∑_{j=1}^{ℓ} max(j, ℓ-j) ≤ (ℓ-1)^2 + ℓ`. -/
theorem prop_5_12_sum (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑ j ∈ Finset.Icc 1 ℓ, max j (ℓ - j) ≤ (ℓ - 1) ^ 2 + ℓ :=
  prop_5_12_sum_proved ℓ hℓ

/-- Corollary 5.15, tex:943-944: Berlinkov's Corollary 1 in the classes `{2,2}`, `{2,3}`, `{2,4}`: `Λ = n - 2 + t₁ + t₂`
for the vector `1` on `E` and `t₁, t₂` (entries coprime as `1` occurs), and `1 + (n-1)(n+t₁+t₂-4)` is `n^2-n+1`,
`n^2`, `n^2+n-1`. -/
theorem rem_5_15_berlinkov (n : ℕ) (hn : 3 ≤ n) :
    (1 + ((n : ℤ) - 1) * (n + 2 + 2 - 4) = n ^ 2 - n + 1) ∧ (1 + ((n : ℤ) - 1) * (n + 2 + 3 - 4) = n ^ 2) ∧
      (1 + ((n : ℤ) - 1) * (n + 2 + 4 - 4) = n ^ 2 + n - 1) :=
  rem_5_15_berlinkov_proved n hn

/-- Corollary 5.15, tex:943: the denominators of the normalized vector have least common multiple `Λ = α(Q)` when one
entry is `1` (here `Λ = n - 2 + t₁ + t₂`). -/
theorem rem_5_15_L {ι : Type*} [Fintype ι] (u : ι → ℕ) (hu : ∀ i, 0 < u i) (h1 : ∃ i, u i = 1) :
    Finset.univ.lcm (fun i => ((u i : ℚ) / (∑ j, u j : ℕ)).den) = ∑ j, u j :=
  rem_5_15_L_proved u hu h1

/-! ## Section 5.4: finite facts on configurations (codes `0 = x₁`, `1 = x₂`, `2 = s`) -/

/-- tex:712-714: `3^4 · 5 = 405` choices. -/
theorem sec54_405 : choices.card = 405 :=
  sec54_405_proved

/-- Lemma 5.8, tex:716-719 (renamings keep the choices, validity and the class). -/
theorem lem_5_8 :
    (choices.filter Config.Valid).card = 179 ∧ ((choices.filter Config.Valid).image Config.renamings).card = 49 ∧
      (choices.filter Config.Valid).image Config.cls = tableClasses ∧ tableClasses.card = 14 ∧
      ∀ c ∈ choices, ∀ c' ∈ c.renamings, c' ∈ choices ∧ (c'.Valid ↔ c.Valid) ∧ (c.Valid → c'.cls = c.cls) :=
  lem_5_8_proved

/-- Table 2, tab_configs_float.tex:10-23 (included at tex:745). A printed (x1.a, x1.b, x2.a, x2.b; nu1, nu2) is the Config with these fields in this order; targets coded 0 = x_1, 1 = x_2, 2 = s (Defs/Binary.lean). -/
theorem table_2_configs :
    let orbits := table2Rows.map (fun r => r.1.renamings)
    table2Rows.length = 49 ∧ (∀ r ∈ table2Rows, r.1 ∈ choices ∧ r.1.Valid ∧ r.1.cls = r.2) ∧
      orbits.Nodup ∧ orbits.toFinset = (choices.filter Config.Valid).image Config.renamings ∧
      (orbits.filter (fun o => o.card = 1)).length = 1 ∧
      (orbits.filter (fun o => o.card = 2)).length = 7 ∧
      (orbits.filter (fun o => o.card = 4)).length = 41 ∧ 1 + 7 * 2 + 41 * 4 = 179 :=
  table_2_configs_proved

/-- Lemma 5.8, proof_classes.tex:4-9 (included at tex:719). The determinant, its zeros, the two coordinates of t, and their positivity. -/
theorem lem_5_8_delta :
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
  lem_5_8_delta_proved

/-- Lemma 5.8, proof_classes.tex:8-10 (included at tex:719). Counts of targets, including each of the five boundary pairs. -/
theorem lem_5_8_target_counts :
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
  lem_5_8_target_counts_proved

/-- Lemma 5.8, proof_classes.tex:4-7 (included at tex:719). The expanded determinants agree with matrix determinants. -/
theorem lem_5_8_determinants (cf : Config) :
    ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) - Matrix.of cf.G).det = cf.delta ∧
      (1 - cf.Z).det = cf.det ∧ cf.delta = 4 * cf.det :=
  lem_5_8_determinants_proved cf

/-- Lemma 5.8, proof_classes.tex:9-11 (included at tex:719). The two renamings are commuting involutions, and their four composites act distinctly. -/
theorem lem_5_8_renaming_action :
    (∀ cf ∈ choices, cf.swapX.swapX = cf ∧ cf.swapL.swapL = cf ∧ cf.swapX.swapL = cf.swapL.swapX) ∧
      (∃ cf ∈ table2Rows, cf.1.renamings.card = 4) :=
  lem_5_8_renaming_action_proved

/-- Table 1, tex:726-745: configurations per class (up to renaming), and the block / excluded counts of the classes
`{1/3,2/3}`, `{2/3,4/3}`, `{1/2,1/2}`, `{1/2,3/2}`. -/
theorem table_1 :
    (∀ e ∈ [((1, 1), 13), ((1/2, 1), 6), ((1, 2), 7), ((1/4, 1/2), 1), ((1/2, 3/4), 1), ((1/3, 2/3), 2),
        ((2/3, 4/3), 2), ((1/2, 2), 1), ((3/2, 2), 1), ((2, 2), 5), ((2, 3), 2), ((2, 4), 2), ((1/2, 1/2), 4),
        ((1/2, 3/2), 2)],
      ((choices.filter (fun c => c.Valid ∧ c.cls = (e : (ℚ × ℚ) × ℕ).1)).image Config.renamings).card = e.2) ∧
    (∀ e ∈ [((1/3, 2/3), 1), ((2/3, 4/3), 1), ((1/2, 1/2), 2), ((1/2, 3/2), 1)],
      ((choices.filter (fun c => c.Valid ∧ c.IsBlock ∧ c.cls = (e : (ℚ × ℚ) × ℕ).1)).image Config.renamings).card
        = e.2) ∧
    (∀ e ∈ [((1/2, 1/2), 2), ((1/2, 3/2), 1)],
      (openConfigs.filter (fun c => c.cls = (e : (ℚ × ℚ) × ℕ).1)).card = e.2) :=
  table_1_proved

/-- tex:760-762: the block configurations outside the classes in which some `t_i = 1`, up to renaming: the five listed,
in the stated classes. -/
theorem sec54_block_list :
    (choices.filter (fun c => c.Valid ∧ c.IsBlock ∧ c.t 0 ≠ 1 ∧ c.t 1 ≠ 1)).image Config.renamings =
        ({⟨2, 2, 2, 2, 1, 1⟩, ⟨2, 0, 2, 0, 0, 1⟩, ⟨2, 1, 2, 0, 0, 1⟩, ⟨2, 1, 2, 0, 0, 2⟩, ⟨2, 0, 2, 0, 1, 1⟩} :
          Finset Config).image Config.renamings ∧
      (⟨2, 2, 2, 2, 1, 1⟩ : Config).cls = (1/2, 1/2) ∧ (⟨2, 0, 2, 0, 0, 1⟩ : Config).cls = (1/2, 1/2) ∧
      (⟨2, 1, 2, 0, 0, 1⟩ : Config).cls = (1/3, 2/3) ∧ (⟨2, 1, 2, 0, 0, 2⟩ : Config).cls = (2/3, 4/3) ∧
      (⟨2, 0, 2, 0, 1, 1⟩ : Config).cls = (1/2, 3/2) :=
  sec54_block_list_proved

/-- tex:762-764: besides the classes with some `t_i = 1`, the block configurations, the three excluded ones and the nine of
the integer classes, exactly six configurations remain (up to renaming): those of Propositions 5.11-5.13. -/
theorem thm_5_9_remaining_six :
    ((choices.filter (fun c => c.Valid ∧ c.t 0 ≠ 1 ∧ c.t 1 ≠ 1 ∧ ¬ c.IsBlock ∧
        (∀ o ∈ openConfigs, c ∉ o.renamings) ∧ c.cls ∉ ({(2, 2), (2, 3), (2, 4)} : Finset (ℚ × ℚ)))).image
        Config.renamings) =
      ({⟨2, 2, 2, 0, 1, 1⟩, ⟨2, 2, 2, 0, 0, 1⟩, ⟨2, 1, 0, 2, 0, 1⟩, ⟨2, 1, 0, 2, 0, 2⟩, ⟨1, 1, 2, 1, 1, 1⟩,
        ⟨1, 1, 2, 0, 1, 1⟩} : Finset Config).image Config.renamings ∧
      ((choices.filter (fun c => c.Valid ∧
        c.cls ∈ ({(2, 2), (2, 3), (2, 4)} : Finset (ℚ × ℚ)))).image Config.renamings).card = 9 :=
  thm_5_9_remaining_six_proved

/-- tex:51, 124, 143-145: Theorem 5.9 covers 46 of the 49 configurations up to renaming. -/
theorem count_46_of_49 :
    (((choices.filter Config.Valid).image Config.renamings).filter
        (fun o => ∀ c ∈ openConfigs, c.renamings ≠ o)).card = 46 ∧
      (openConfigs.image Config.renamings).card = 3 :=
  count_46_of_49_proved

/-- tex:124, 145: the excluded configurations lie in two classes, so every configuration of 12 of the 14 classes is
covered. -/
theorem count_12_classes :
    (tableClasses.filter (fun k => ∀ c ∈ openConfigs, c.cls ≠ k)).card = 12 :=
  count_12_classes_proved

/-- Theorem 5.9, tex:749-751: the three excluded configurations are valid; two lie in `{1/2,1/2}`, one in
`{1/2,3/2}`. -/
theorem sec6_three_configs :
    (∀ c ∈ openConfigs, c ∈ choices ∧ c.Valid) ∧ (⟨2, 0, 0, 2, 0, 1⟩ : Config).cls = (1/2, 1/2) ∧
      (⟨2, 2, 0, 0, 0, 1⟩ : Config).cls = (1/2, 1/2) ∧ (⟨2, 0, 0, 2, 1, 1⟩ : Config).cls = (1/2, 3/2) :=
  sec6_three_configs_proved

/-- Proposition 5.11, tex:812-815: each of the two classes has one configuration; after renaming
`x₁.a = x₁.b = x₂.a = s`, `x₂.b = x₁`; the boundary edges and `(t₁, t₂)`. -/
theorem prop_5_11_config :
    (choices.filter (fun c => c.Valid ∧ c.cls = (1/2, 3/4))).image Config.renamings =
        {(⟨2, 2, 2, 0, 1, 1⟩ : Config).renamings} ∧
      (choices.filter (fun c => c.Valid ∧ c.cls = (1/4, 1/2))).image Config.renamings =
        {(⟨2, 2, 2, 0, 0, 1⟩ : Config).renamings} ∧
      (⟨2, 2, 2, 0, 1, 1⟩ : Config).t = ![3/4, 1/2] ∧ (⟨2, 2, 2, 0, 0, 1⟩ : Config).t = ![1/4, 1/2] ∧
      ∀ cf ∈ ({⟨2, 2, 2, 0, 1, 1⟩, ⟨2, 2, 2, 0, 0, 1⟩} : Finset Config),
        (∀ i, -1 < cf.t i - 1 ∧ cf.t i - 1 < 0) ∧
        ∀ g ∈ ({cf.t 0 - 1, cf.t 1 - 1, cf.t 0 - 1 + (cf.t 1 - 1), cf.t 0 - 1 - (cf.t 1 - 1)} : Finset ℚ),
          ¬ ∃ z : ℤ, g = z :=
  prop_5_11_config_proved

/-- Proposition 5.11, tex:826: a merging letter alone would not do: `{s} a⁻¹` may be `X`, with `α(X) = 3/4 < 1`
(an automaton of the class `{1/4, 1/2}`: `a = (0,0,1,1)`, `b = (1,3,1,2)`, `s = 1`, `x₁ = 2`, `x₂ = 3`). -/
theorem prop_5_11_merging_remark :
    ∃ W : QEWitness (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]) 2, W.E = {0, 1} ∧ W.s = 1 ∧
      (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).Synchronizing ∧ (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).StronglyConnected ∧
      (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).configOf 0 1 {0, 1} 2 3 = ⟨2, 2, 2, 0, 0, 1⟩ ∧
      (ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).pre {1} [0] = {2, 3} ∧ W.X = {2, 3} ∧
      wt ((ofLists ![0, 0, 1, 1] ![1, 3, 1, 2]).alphaStat {0, 1} (fun _ => 1 / 2)) {2, 3} = 3 / 4 :=
  prop_5_11_merging_remark_proved

/-- Proposition 5.12, tex:844-848: `(g₁, g₂)` and `g₁ + g₂` in the two configurations. -/
theorem prop_5_12_config :
    (⟨2, 1, 0, 2, 0, 1⟩ : Config).t = ![1/3, 2/3] ∧ (⟨2, 1, 0, 2, 0, 2⟩ : Config).t = ![2/3, 4/3] ∧
      (⟨2, 1, 0, 2, 0, 1⟩ : Config).cls = (1/3, 2/3) ∧ (⟨2, 1, 0, 2, 0, 2⟩ : Config).cls = (2/3, 4/3) ∧
      (⟨2, 1, 0, 2, 0, 1⟩ : Config).t 0 - 1 + ((⟨2, 1, 0, 2, 0, 1⟩ : Config).t 1 - 1) = -1 ∧
      (⟨2, 1, 0, 2, 0, 2⟩ : Config).t 0 - 1 + ((⟨2, 1, 0, 2, 0, 2⟩ : Config).t 1 - 1) = 0 ∧
      ∀ cf ∈ ({⟨2, 1, 0, 2, 0, 1⟩, ⟨2, 1, 0, 2, 0, 2⟩} : Finset Config),
        ∀ g ∈ ({cf.t 0 - 1, cf.t 1 - 1, cf.t 0 - 1 - (cf.t 1 - 1)} : Finset ℚ), ¬ ∃ z : ℤ, g = z :=
  prop_5_12_config_proved

/-- Proposition 5.13, tex:871-876 (Lean u = printed x₂, v = printed x₁): each of the two classes has one configuration: `u.a = u.b = v`, one boundary edge at
`u` and one at `v`, `v.a = s`, and `v.b = v` (`{1/2,2}`) or `v.b = u` (`{3/2,2}`). -/
theorem prop_5_13_config :
    (choices.filter (fun c => c.Valid ∧ c.cls = (1/2, 2))).image Config.renamings =
        {(⟨1, 1, 2, 1, 1, 1⟩ : Config).renamings} ∧
      (choices.filter (fun c => c.Valid ∧ c.cls = (3/2, 2))).image Config.renamings =
        {(⟨1, 1, 2, 0, 1, 1⟩ : Config).renamings} ∧
      (⟨1, 1, 2, 1, 1, 1⟩ : Config).t = ![1/2, 2] ∧ (⟨1, 1, 2, 0, 1, 1⟩ : Config).t = ![3/2, 2] :=
  prop_5_13_config_proved

section Binary

variable {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)

/-! ## Section 5.4: binary automata (letters `a ≠ b`, every letter `a` or `b`; weights `(1/2, 1/2)`) -/

/-- Lemma 5.7(a), tex:687: the weights `(1/2, 1/2)` are admissible for `(E, s)`. -/
theorem lem_5_7_a (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) :
    ∃ W' : QEWitness A 2, W'.E = W.E ∧ W'.s = W.s ∧ W'.p = fun _ => 1 / 2 :=
  lem_5_7_a_proved A a b hab hS W

/-- Lemma 5.7(b), tex:688-691: exactly two edges lead from `E` into `X ∪ {s}`; `Z` and `y` (weights `1/2`) are those of
the configuration, `ν₁ + ν₂ ≤ 2`; for a strongly connected automaton `t` is the configuration's. -/
theorem lem_5_7_b (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    ((W.E ×ˢ ({a, b} : Finset S)).filter (fun e => A.step e.1 e.2 ∈ insert W.s W.X)).card = 2 ∧
      (∀ i j : Fin 2, A.zPair (fun _ => 1 / 2) (![x₁, x₂] i) (![x₁, x₂] j) =
        ((A.configOf a b W.E x₁ x₂).Z i j : ℝ)) ∧
      (∀ i : Fin 2, A.yIn W.E (fun _ => 1 / 2) (![x₁, x₂] i) = ((A.configOf a b W.E x₁ x₂).y i : ℝ)) ∧
      (A.configOf a b W.E x₁ x₂).nu1 + (A.configOf a b W.E x₁ x₂).nu2 ≤ 2 ∧
      (A.StronglyConnected → ∀ i : Fin 2,
        A.alphaStat W.E (fun _ => 1 / 2) (![x₁, x₂] i) = ((A.configOf a b W.E x₁ x₂).t i : ℝ)) :=
  lem_5_7_b_proved A a b hab hS W x₁ x₂ hX h12

/-- Lemma 5.7(a), tex:700-705. Count the edges labelled c into the n−3 ordinary states when N of them receive k edges and the rest receive one. -/
theorem lem_5_7_edge_count (W : QEWitness A 2) (c : S) (B : Finset Q) (k : ℕ)
    (hB : B ⊆ W.E.erase W.s) (hbig : ∀ r ∈ B, (A.pre {r} [c]).card = k)
    (hsmall : ∀ r ∈ W.E.erase W.s, r ∉ B → (A.pre {r} [c]).card = 1) :
    let n := Fintype.card Q
    let N := B.card
    let total := (n-3-N) + N*k
    (W.E.erase W.s).card = n-3 ∧ (∑ r ∈ W.E.erase W.s, (A.pre {r} [c]).card) = total ∧
      total + 2 ≤ n ∧ (1 ≤ N → 3 ≤ k → total + 2 = n-1 + N*(k-1) ∧ n+1 ≤ total+2) :=
  lem_5_7_edge_count_proved A W c B k hB hbig hsmall

/-- tex:713-714: `(ν₁, ν₂) = (0, 0)` makes `E` closed, so the automaton is not strongly connected. -/
theorem sec54_nu_ne_00 (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) (h0 : (A.configOf a b W.E x₁ x₂).nu1 = 0)
    (h0' : (A.configOf a b W.E x₁ x₂).nu2 = 0) : A.IsClosed W.E ∧ ¬ A.StronglyConnected :=
  sec54_nu_ne_00_proved A a b hab hS W x₁ x₂ hX h12 h0 h0'

/-- tex:721-722: the configuration of every witness of degree two of a strongly connected binary automaton is among the
valid ones of Lemma 5.8. -/
theorem sec54_config_valid (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂) :
    A.configOf a b W.E x₁ x₂ ∈ choices ∧ (A.configOf a b W.E x₁ x₂).Valid :=
  sec54_config_valid_proved A a b hab hS hsc W x₁ x₂ hX h12

/-- Theorem 5.9, tex:747-753. Some witness has a configuration other than the three listed, up to renaming. -/
theorem thm_5_9 (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected)
    (hW : ∃ (W : QEWitness A 2) (x₁ x₂ : Q), W.X = {x₁, x₂} ∧ x₁ ≠ x₂ ∧
      ∀ o ∈ openConfigs, A.configOf a b W.E x₁ x₂ ∉ o.renamings) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  thm_5_9_proved A a b hab hS hA hsc hW

/-- tex:769-771: `α(K) = |K| + g₁ e₁(K) + g₂ e₂(K)` for the vector `α` of Lemma 5.5 with the weights `(1/2, 1/2)`. -/
theorem sec54_alpha_formula (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (K : Finset Q) :
    wt (A.alphaStat W.E (fun _ => 1 / 2)) K = K.card + (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) * ein x₁ K +
      (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) * ein x₂ K :=
  sec54_alpha_formula_proved A W x₁ x₂ hX h12 K

/-- tex:783-784: `e_i(K c⁻¹) = [x_i.c ∈ K]` with `x_i.c ∈ X ∪ {s}`, so the change of `(e₁, e₂)` under a letter depends
only on the pattern. -/
theorem sec54_change_depends_on_pattern (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (c : S) (K K' : Finset Q) (hP : pattern x₁ x₂ W.s K = pattern x₁ x₂ W.s K') :
    (∀ x ∈ ({x₁, x₂} : Finset Q), (x ∈ A.pre K [c] ↔ A.step x c ∈ K) ∧ A.step x c ∈ insert W.s W.X) ∧
      ein x₁ (A.pre K [c]) - ein x₁ K = ein x₁ (A.pre K' [c]) - ein x₁ K' ∧
      ein x₂ (A.pre K [c]) - ein x₂ K = ein x₂ (A.pre K' [c]) - ein x₂ K' :=
  sec54_change_depends_on_pattern_proved A W x₁ x₂ hX h12 c K K' hP

/-- tex:784-786: "some (equivalently, every) set K with this pattern", and a good pattern gives `m(K) = 1`. -/
theorem sec54_good_cost1 (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (P : Bool × Bool × Bool) :
    (Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P ↔
      ∃ c : S, ∀ K : Finset Q, pattern x₁ x₂ W.s K = P → ¬ ∃ z : ℤ,
        (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) * (ein x₁ (A.pre K [c]) - ein x₁ K) +
          (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) * (ein x₂ (A.pre K [c]) - ein x₂ K) = z) ∧
      (Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P →
        ∀ K : Finset Q, pattern x₁ x₂ W.s K = P → A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K = 1) :=
  sec54_good_cost1_proved A W x₁ x₂ hX h12 P

/-- tex:786-787: aligned patterns are never good (for any numbers `g₁, g₂`). -/
theorem sec54_aligned_not_good (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (g₁ g₂ : ℝ) (P : Bool × Bool × Bool) (hP : Aligned P) : ¬ Good A x₁ x₂ W.s g₁ g₂ P :=
  sec54_aligned_not_good_proved A W x₁ x₂ hX h12 g₁ g₂ P hP

/-- Lemma 5.10 (joint orbit), tex:790-791, the pattern `(1,1,1)`. -/
theorem lem_5_10_a (hsc : A.StronglyConnected) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ)
    (hP : pattern x₁ x₂ W.s K = (true, true, true)) :
    A.esc W.s K ≤ ((K.card - 2 : ℕ) : ℕ∞) ∧
      (∀ w : List S, (w.length : ℕ∞) ≤ A.esc W.s K → A.act x₁ w ∈ K ∧ A.act x₂ w ∈ K) ∧
      (Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1)
          (true, true, false) →
        A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ ((K.card - 1 : ℕ) : ℕ∞)) :=
  lem_5_10_a_proved A hsc W x₁ x₂ hX h12 K hne hprop hP

/-- Lemma 5.10, tex:791-792, the pattern `(0,0,0)`. -/
theorem lem_5_10_b (hsc : A.StronglyConnected) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂) (K : Finset Q) (hne : K.Nonempty) (hprop : K ≠ Finset.univ)
    (hP : pattern x₁ x₂ W.s K = (false, false, false)) :
    A.esc W.s K ≤ ((Fintype.card Q - K.card - 2 : ℕ) : ℕ∞) ∧
      (Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1)
          (false, false, true) →
        A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ ((Fintype.card Q - K.card - 1 : ℕ) : ℕ∞)) :=
  lem_5_10_b_proved A hsc W x₁ x₂ hX h12 K hne hprop hP

/-- tex:802-803: passing to the complement changes the sign of every change of `e₁`, `e₂`; so a pattern is good iff
the complementary pattern is. -/
theorem lem_5_10_compl_good (x₁ x₂ s : Q) (g₁ g₂ : ℝ) (b₁ b₂ b₃ : Bool) :
    Good A x₁ x₂ s g₁ g₂ (b₁, b₂, b₃) ↔ Good A x₁ x₂ s g₁ g₂ (!b₁, !b₂, !b₃) :=
  lem_5_10_compl_good_proved A x₁ x₂ s g₁ g₂ b₁ b₂ b₃

/-- Proposition 5.11, tex:806-808. If the witness has class {1/2,3/4} or {1/4,1/2}, the bound is 1+(n−2)n. -/
theorem prop_5_11 (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((1 + (Fintype.card Q - 2) * Fintype.card Q : ℕ) : ℕ∞) :=
  prop_5_11_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 hcl

/-- Proposition 5.11, tex:817-819: in these classes every pattern that is not aligned is good. -/
theorem prop_5_11_good (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 3/4), (3/4, 1/2), (1/4, 1/2), (1/2, 1/4)} : Finset (ℝ × ℝ)))
    (P : Bool × Bool × Bool) (hP : ¬ Aligned P) :
    Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P :=
  prop_5_11_good_proved A a b hab hS hsc hn W x₁ x₂ hX h12 hcl P hP

/-- Proposition 5.12, tex:835-841. -/
theorem prop_5_12 (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcf : A.configOf a b W.E x₁ x₂ ∈ (⟨2, 1, 0, 2, 0, 1⟩ : Config).renamings ∪
      (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧
      Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q ≤ (Fintype.card Q - 1) ^ 2 :=
  prop_5_12_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 hcf

/-- Proposition 5.12, tex:857-863. The class {1/3,2/3} has at most 2(n−2) noninteger values in [1,n−1). -/
theorem prop_5_12_first_levels (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁,x₂}) (h12 : x₁ ≠ x₂) (h1 : A.alphaStat W.E (fun _ => 1/2) x₁ = 1/3)
    (h2 : A.alphaStat W.E (fun _ => 1/2) x₂ = 2/3) :
    (nonintegerWeights (A.alphaStat W.E (fun _ => 1/2)) 1 ((Fintype.card Q : ℝ) - 1)).card ≤
      2 * (Fintype.card Q - 2) :=
  prop_5_12_first_levels_proved A hn W x₁ x₂ hX h12 h1 h2

/-- Proposition 5.12, tex:851-855. Name the exceptional states by weights 2/3 and 4/3. The noninteger levels are exactly k ± 1/3 for 2 ≤ k ≤ n−1. -/
theorem prop_5_12_levels (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q)
    (hX : W.X = {x₁,x₂}) (h12 : x₁ ≠ x₂)
    (h1 : A.alphaStat W.E (fun _ => 1/2) x₁ = 2/3) (h2 : A.alphaStat W.E (fun _ => 1/2) x₂ = 4/3) :
    let n := Fintype.card Q
    let α := A.alphaStat W.E (fun _ => 1/2)
    (∀ K : Finset Q, ¬ (x₁ ∈ K ↔ x₂ ∈ K) → K.card ≤ n - 1) ∧
      (∀ z : ℝ, z ∈ thirdLevels n ↔ 5/3 ≤ z ∧ z < n ∧ (¬ ∃ i : ℤ, z = i) ∧ ∃ K : Finset Q, wt α K = z) ∧
      (thirdLevels n).card = 2 * (n - 2) :=
  prop_5_12_levels_proved A hn W x₁ x₂ hX h12 h1 h2

/-- Proposition 5.12, tex:851-855. The sharper bound for the second configuration and its renamings. -/
theorem prop_5_12_sharp (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcf : A.configOf a b W.E x₁ x₂ ∈ (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 4 - 3 * Fintype.card Q : ℕ) : ℕ∞) :=
  prop_5_12_sharp_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 hcf

/-- Proposition 5.12, tex:845-849: in these configurations every pattern that is not aligned is good. -/
theorem prop_5_12_good (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂}) (h12 : x₁ ≠ x₂)
    (hcf : A.configOf a b W.E x₁ x₂ ∈ (⟨2, 1, 0, 2, 0, 1⟩ : Config).renamings ∪
      (⟨2, 1, 0, 2, 0, 2⟩ : Config).renamings)
    (P : Bool × Bool × Bool) (hP : ¬ Aligned P) :
    Good A x₁ x₂ W.s (A.alphaStat W.E (fun _ => 1 / 2) x₁ - 1) (A.alphaStat W.E (fun _ => 1 / 2) x₂ - 1) P :=
  prop_5_12_good_proved A a b hab hS hsc hn W x₁ x₂ hX h12 hcf P hP

/-- Proposition 5.13, tex:866-868. If the witness has class {1/2,2} or {3/2,2}, the bound is n²−3n+5. -/
theorem prop_5_13 (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 2), (2, 1/2), (3/2, 2), (2, 3/2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q : ℕ) : ℕ∞) ∧
      Fintype.card Q ^ 2 + 5 - 3 * Fintype.card Q ≤ (Fintype.card Q - 1) ^ 2 :=
  prop_5_13_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 hcl

/-- Proposition 5.13, tex:890-898: in the class `{1/2, 2}`, `rt ≤ n^2 - 3n + 4` for every `n ≥ 4`. -/
theorem prop_5_13_half (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(1/2, 2), (2, 1/2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 4 - 3 * Fintype.card Q : ℕ) : ℕ∞) :=
  prop_5_13_half_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 hcl

/-- Proposition 5.13, proof steps (i)-(iii), tex:878-886 and tab_costs_float.tex:12-20, with Lean u = printed x₂ and v = printed x₁, `t_u ∈ {1/2, 3/2}`,
`t_v = 2`. -/
theorem prop_5_13_steps (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2 ∨ A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) :
    (∀ K : Finset Q, A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ A.esc u K) ∧
      (∀ P : Bool × Bool × Bool, Good A u v W.s (A.alphaStat W.E (fun _ => 1 / 2) u - 1)
          (A.alphaStat W.E (fun _ => 1 / 2) v - 1) P ↔ P.1 ≠ P.2.1) ∧
      ∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ → (u ∈ K ↔ v ∈ K) →
        A.esc u K = 1 + A.esc v K ∧
        ((W.s ∈ K ↔ v ∉ K) → A.esc v K = 1 ∧ A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ 2) ∧
        (Aligned (pattern u v W.s K) → A.esc v K = 1 + A.esc W.s K ∧
          A.cost (A.alphaStat W.E (fun _ => 1 / 2)) K ≤ 2 + A.esc W.s K ∧
          (pattern u v W.s K = (true, true, true) → 2 + A.esc W.s K ≤ K.card) ∧
          (pattern u v W.s K = (false, false, false) → 2 + A.esc W.s K ≤ ((Fintype.card Q - K.card : ℕ) : ℕ∞))) :=
  prop_5_13_steps_proved A a b hab hS hsc hn W u v hX huv hu hv

/-- Proposition 5.13, tex:896. A set of exceptional part (0,0) omits two distinct states. -/
theorem prop_5_13_missing_pair {x₁ x₂ : Q} (h12 : x₁ ≠ x₂) (K : Finset Q)
    (h1 : x₁ ∉ K) (h2 : x₂ ∉ K) : K.card ≤ Fintype.card Q - 2 :=
  prop_5_13_missing_pair_proved h12 K h1 h2

/-- Table 3, tab_costs_float.tex:12-15 (included at tex:888). Lean u = printed x₂, v = printed x₁. With equal membership of u and v, alignment means s has that membership too. -/
theorem table_3_half (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 1/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) (K : Finset Q) (hne : K.Nonempty)
    (hprop : K ≠ Finset.univ) (hgt : 2 < wt (A.alphaStat W.E (fun _ => 1 / 2)) K) :
    let n := Fintype.card Q
    let α := A.alphaStat W.E (fun _ => 1 / 2)
    let m := A.cost α K
    (v ∉ K → u ∉ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N ∧ K.card = N ∧
      (W.s ∉ K → N ≤ n - 3 ∧ m ≤ ((n - N : ℕ) : ℕ∞)) ∧ (W.s ∈ K → m ≤ 2)) ∧
    (v ∈ K → u ∉ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N ∧ K.card = N - 1 ∧ m = 1) ∧
    (v ∉ K → u ∈ K → ∃ N : ℕ, 2 ≤ N ∧ N ≤ n - 1 ∧ wt α K = N + 1/2 ∧ K.card = N + 1 ∧ m = 1) ∧
    (v ∈ K → u ∈ K → ∃ N : ℕ, 2 ≤ N ∧ N ≤ n - 1 ∧ wt α K = N + 1/2 ∧ K.card = N ∧
      (W.s ∈ K → 3 ≤ N ∧ m ≤ (N : ℕ∞)) ∧ (W.s ∉ K → m ≤ 2)) :=
  table_3_half_proved A a b hab hS hsc hn W u v hX huv hu hv K hne hprop hgt

/-- Table 3, tab_costs_float.tex:17-20 (included at tex:888). Lean u = printed x₂, v = printed x₁. With equal membership of u and v, alignment means s has that membership too. -/
theorem table_3_three_halves (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hsc : A.StronglyConnected)
    (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (u v : Q) (hX : W.X = {u, v}) (huv : u ≠ v)
    (hu : A.alphaStat W.E (fun _ => 1 / 2) u = 3/2)
    (hv : A.alphaStat W.E (fun _ => 1 / 2) v = 2) (K : Finset Q) (hne : K.Nonempty)
    (hprop : K ≠ Finset.univ) (hgt : 2 < wt (A.alphaStat W.E (fun _ => 1 / 2)) K) :
    let n := Fintype.card Q
    let α := A.alphaStat W.E (fun _ => 1 / 2)
    let m := A.cost α K
    (v ∉ K → u ∉ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N ∧ K.card = N ∧
      (W.s ∉ K → N ≤ n - 3 ∧ m ≤ ((n - N : ℕ) : ℕ∞)) ∧ (W.s ∈ K → m ≤ 2)) ∧
    (v ∈ K → u ∉ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N ∧ K.card = N - 1 ∧ m = 1) ∧
    (v ∉ K → u ∈ K → ∃ N : ℕ, 2 ≤ N ∧ N ≤ n ∧ wt α K = N + 1/2 ∧ K.card = N ∧ m = 1) ∧
    (v ∈ K → u ∈ K → ∃ N : ℕ, 3 ≤ N ∧ N ≤ n ∧ wt α K = N + 1/2 ∧ K.card = N - 1 ∧
      (W.s ∈ K → 4 ≤ N ∧ m ≤ ((N - 1 : ℕ) : ℕ∞)) ∧ (W.s ∉ K → m ≤ 2)) :=
  table_3_three_halves_proved A a b hab hS hsc hn W u v hX huv hu hv K hne hprop hgt

/-- Proposition 5.14, tex:912-915: the bound `(n-1)^2`. -/
theorem prop_5_14 (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 4 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ (((Fintype.card Q - 1) ^ 2 : ℕ) : ℕ∞) :=
  prop_5_14_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 hcl

/-- Proposition 5.14, tex:915-916: `rt ≤ n^2 - 3n + 8` if `n ≥ 7`. -/
theorem prop_5_14_big (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (hA : A.Synchronizing)
    (hsc : A.StronglyConnected) (hn : 7 ≤ Fintype.card Q) (W : QEWitness A 2) (x₁ x₂ : Q) (hX : W.X = {x₁, x₂})
    (h12 : x₁ ≠ x₂)
    (hcl : (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
      ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ))) :
    A.rt ≤ ((Fintype.card Q ^ 2 + 8 - 3 * Fintype.card Q : ℕ) : ℕ∞) :=
  prop_5_14_big_proved A a b hab hS hA hsc hn W x₁ x₂ hX h12 hcl

/-- Lemma 5.7, tex:705-708 (also used in the proof of Proposition 5.14): every state of `E \ {s}` is entered by exactly two edges, all from `E`. -/
theorem prop_5_14_entry (a b : S) (hab : a ≠ b) (hS : ∀ c, c = a ∨ c = b) (W : QEWitness A 2) (r : Q)
    (hr : r ∈ W.E) (hrs : r ≠ W.s) :
    (A.pre {r} [a]).card + (A.pre {r} [b]).card = 2 ∧ A.pre {r} [a] ⊆ W.E ∧ A.pre {r} [b] ⊆ W.E :=
  prop_5_14_entry_proved A a b hab hS W r hr hrs

end Binary

/-- Supplement to Proposition 5.14, tex:932, 939-940: for `n = 4, 5, 6` the largest reset thresholds in the three integer classes are
`8`, `13` and `19` (an upper bound for every such automaton, attained by one). -/
theorem prop_5_14_max (n : ℕ) (hn : n = 4 ∨ n = 5 ∨ n = 6) :
    (∀ (Q : Type u) [Fintype Q] [DecidableEq Q] (A : Automaton Q (Fin 2)), Fintype.card Q = n →
      A.Synchronizing → A.StronglyConnected → ∀ (W : QEWitness A 2) (x₁ x₂ : Q), W.X = {x₁, x₂} → x₁ ≠ x₂ →
      (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
        ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ)) →
      A.rt ≤ ((if n = 4 then 8 else if n = 5 then 13 else 19 : ℕ) : ℕ∞)) ∧
    ∃ (A : Automaton (Fin n) (Fin 2)) (W : QEWitness A 2) (x₁ x₂ : Fin n), W.X = {x₁, x₂} ∧ x₁ ≠ x₂ ∧
      A.Synchronizing ∧ A.StronglyConnected ∧
      (A.alphaStat W.E (fun _ => 1 / 2) x₁, A.alphaStat W.E (fun _ => 1 / 2) x₂) ∈
        ({(2, 2), (2, 3), (3, 2), (2, 4), (4, 2)} : Finset (ℝ × ℝ)) ∧
      A.rt = ((if n = 4 then 8 else if n = 5 then 13 else 19 : ℕ) : ℕ∞) :=
  prop_5_14_max_proved n hn

/-- Corollary 5.15, tex:944: the level count alone (every step at most `n - 1` letters) gives `rt ≤ n(n-1)` for a positive
integer stationary vector with `α(Q) - max α ≤ n`. -/
theorem rem_5_15_level {Q : Type u} {S : Type v} [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S)
    (hA : A.Synchronizing) (hn : 2 ≤ Fintype.card Q) (p : S → ℝ) (hp : IsLetterWeights p) (u : Q → ℕ)
    (hu : ∀ q, 0 < u q) (hstat : A.IsStationary p (fun q => (u q : ℝ)))
    (hmax : ∃ q₀, ∑ q, u q ≤ Fintype.card Q + u q₀) :
    A.rt ≤ ((Fintype.card Q * (Fintype.card Q - 1) : ℕ) : ℕ∞) :=
  rem_5_15_level_proved A hA hn p hp u hu hstat hmax

/-- Supplement to Section 6 (the circular example was removed): some automata with an excluded configuration are circular (a letter permutes all states in one cycle):
`a = (1,2,3,0)`, `b = (0,0,2,1)`, `s = 1`, `x₁ = 0`, `x₂ = 3`, configuration `(s,x₁,x₁,s;1,1)`. -/
theorem sec6_some_circular :
    ∃ W : QEWitness (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]) 2, W.E = {1, 2} ∧ W.s = 1 ∧
      (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).Synchronizing ∧ (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).StronglyConnected ∧
      (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).configOf 0 1 {1, 2} 0 3 ∈ openConfigs ∧
      Function.Bijective (fun q => (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).step q 0) ∧
      cycles (fun q => (ofLists ![1, 2, 3, 0] ![0, 0, 2, 1]).step q 0) = {Finset.univ} :=
  sec6_some_circular_proved

/-! ## Examples 3.5 and 3.6 (letters `a = 0`, `b = 1`) -/

/-- Example 3.5, tex:478-481: with `p = (1/2, 1/2)` the vector `(1,1,1,1,2)` is stationary: `0` and `1` are entered only
from `4` (by `a`, by `b`), `2` and `3` by two edges from `{0,1,2,3}` each, and `4` by four such edges. -/
theorem ex_3_5_stationary :
    ex35.IsStationary (fun _ => 1 / 2) ![1, 1, 1, 1, 2] ∧
      ex35.pre {0} [0] = {4} ∧ ex35.pre {0} [1] = ∅ ∧ ex35.pre {1} [0] = ∅ ∧ ex35.pre {1} [1] = {4} ∧
      (∀ r : Fin 5, r = 2 ∨ r = 3 →
        (ex35.pre {r} [0]).card + (ex35.pre {r} [1]).card = 2 ∧ ex35.pre {r} [0] ∪ ex35.pre {r} [1] ⊆ {0, 1, 2, 3}) ∧
      (ex35.pre {4} [0]).card + (ex35.pre {4} [1]).card = 4 ∧ ex35.pre {4} [0] ∪ ex35.pre {4} [1] ⊆ {0, 1, 2, 3} :=
  ex_3_5_stationary_proved

/-- Example 3.5, tex:481: Theorem 3.1 applies with `x = 4` and `t = 2`. -/
theorem ex_3_5_in_thm31 :
    ex35.Synchronizing ∧ IsLetterWeights (fun _ : Fin 2 => (1 / 2 : ℝ)) ∧
      ex35.IsStationary (fun _ => 1 / 2) (alphaOff 4 2) :=
  ex_3_5_in_thm31_proved

/-- Example 3.5, tex:482-483: `0` and `1` are entered by one edge each and `4` by two edges of each letter, so for no
letter weights do they have in-weight one. -/
theorem ex_3_5_inedges (p : Fin 2 → ℝ) (hp : IsLetterWeights p) :
    ex35.inW p 0 ≠ 1 ∧ ex35.inW p 1 ≠ 1 ∧ ex35.inW p 4 ≠ 1 :=
  ex_3_5_inedges_proved p hp

/-- Example 3.5, tex:481-484: not quasi-Eulerian of degree one or two (for any real weights). -/
theorem ex_3_5_not_qe12 : ¬ QuasiEulerian ex35 1 ∧ ¬ QuasiEulerian ex35 2 :=
  ex_3_5_not_qe12_proved

/-- Example 3.5, tex:484-485: `Q.(abaab) = {4}`. Supplementary minimum: `rt = 5`. -/
theorem ex_3_5_rt : ex35.rt = 5 ∧ ex35.img Finset.univ [0, 1, 0, 0, 1] = {4} :=
  ex_3_5_rt_proved

/-- Example 3.6, tex:492-494: a stationary vector `1` off `2` and `t` at `2` exists exactly when `p_a(2+t) = 1` and
`p_b(1+t) = 1`, that is, when `t^2 + t - 1 = 0`; then `t = (√5-1)/2` and `p_a = (3-√5)/2`; these weights work. -/
theorem ex_3_6_x2 :
    (∀ (p : Fin 2 → ℝ), IsLetterWeights p → ∀ t : ℝ,
      (ex36.IsStationary p ![1, 1, t] ↔ p 0 * (2 + t) = 1 ∧ p 1 * (1 + t) = 1) ∧
      (p 0 * (2 + t) = 1 ∧ p 1 * (1 + t) = 1 →
        t ^ 2 + t - 1 = 0 ∧ t = (Real.sqrt 5 - 1) / 2 ∧ p 0 = (3 - Real.sqrt 5) / 2)) ∧
    IsLetterWeights ![(3 - Real.sqrt 5) / 2, (Real.sqrt 5 - 1) / 2] ∧
      ex36.IsStationary ![(3 - Real.sqrt 5) / 2, (Real.sqrt 5 - 1) / 2] ![1, 1, (Real.sqrt 5 - 1) / 2] :=
  ex_3_6_x2_proved

/-- Example 3.6, tex:494: with the state `1` in the role of `x`: `t = √2` and `p_b = 1/√2`. -/
theorem ex_3_6_x1 :
    (∀ (p : Fin 2 → ℝ), IsLetterWeights p → ∀ t : ℝ, ex36.IsStationary p ![1, t, 1] →
      t = Real.sqrt 2 ∧ p 1 = 1 / Real.sqrt 2) ∧
    IsLetterWeights ![1 - 1 / Real.sqrt 2, 1 / Real.sqrt 2] ∧
      ex36.IsStationary ![1 - 1 / Real.sqrt 2, 1 / Real.sqrt 2] ![1, Real.sqrt 2, 1] :=
  ex_3_6_x1_proved

/-- Example 3.6, tex:494-495: the state `0` admits no such weights. -/
theorem ex_3_6_x0 (p : Fin 2 → ℝ) (hp : IsLetterWeights p) (t : ℝ) : ¬ ex36.IsStationary p ![t, 1, 1] :=
  ex_3_6_x0_proved p hp t

/-- Example 3.6, tex:495-496: every choice of `x` needs irrational weights. -/
theorem ex_3_6_irrational (x : Fin 3) (p : Fin 2 → ℝ) (hp : IsLetterWeights p) (t : ℝ)
    (hα : ex36.IsStationary p (alphaOff x t)) : Irrational (p 0) ∧ Irrational (p 1) :=
  ex_3_6_irrational_proved x p hp t hα

/-- Example 3.6, tex:495: the automaton is (trivially) synchronizing: `a` is a reset word. -/
theorem ex_3_6_sync : ex36.IsReset [0] ∧ ex36.rt = 1 :=
  ex_3_6_sync_proved

/-- Lemma 2.4, proof step (iii), tex:358-360: a subspace of dimension `ρ` contains at most `2^ρ` vectors with entries
in `{0, 1}`. -/
theorem lem_2_4_zeroOne {ι : Type*} [Fintype ι] (V : Submodule ℝ (ι → ℝ)) :
    {ξ : ι → ℝ | ξ ∈ V ∧ ∀ i, ξ i = 0 ∨ ξ i = 1}.ncard ≤ 2 ^ Module.finrank ℝ V :=
  lem_2_4_zeroOne_proved V

end CernyQE
