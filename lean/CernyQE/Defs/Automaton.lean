/-
CernyQE/Defs/Automaton.lean — automata, words, preimages, reset words, the lengths rt, ext, esc and the cost, letter
weights, weighted matrices, stationary vectors, closed sets, strong connectivity, and quasi-Eulerian witnesses.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
## version 0.31 - 20261118 — source references use the paper metadata recorded in the audit notes and claim map.
## version 0.01 - 20261105 — first.
Paper = the paper's frozen text; a pointer "tex:N" is line N of its main source file (AUDIT_NOTES.md names the version and its SHA-256).
Lengths that may be infinite (rt, ext, esc, the cost) are values in `ℕ∞`: the least length of a word with the property,
and `⊤` if no word has it (tex:236, tex:313).
-/
import Mathlib

namespace CernyQE

open Finset

/-- The least length of a word with property `P`, in `ℕ∞`; it is `⊤` (infinite) if no word has `P`. -/
noncomputable def minLen {S : Type*} (P : List S → Prop) : ℕ∞ :=
  ⨅ (w : List S) (_ : P w), (w.length : ℕ∞)

/-- A (complete deterministic) automaton `(Q, Σ)` (tex:63-64): every letter `b` maps every state `q` to the state
`q.b = step q b`; `q → q.b` is an edge with label `b`. -/
structure Automaton (Q : Type*) (S : Type*) where
  step : Q → S → Q

variable {Q S : Type*}

/-- Letter weights: numbers `p_b > 0` with `∑_b p_b = 1`; they need not be rational (tex:244). -/
def IsLetterWeights [Fintype S] (p : S → ℝ) : Prop := (∀ b, 0 < p b) ∧ ∑ b, p b = 1

/-- The weight `β(K) = ∑_{q ∈ K} β_q` of a set `K` (tex:241). -/
noncomputable def wt (β : Q → ℝ) (K : Finset Q) : ℝ := ∑ q ∈ K, β q

/-- The indicator column vector `𝟙_K` of a set `K` (tex:239); `𝟙_Q = 1`. -/
noncomputable def ind [DecidableEq Q] (K : Finset Q) : Q → ℝ := fun q => if q ∈ K then 1 else 0

namespace Automaton

variable (A : Automaton Q S)

/-- Words act on the right: `q.(uv) = (q.u).v` (tex:228). -/
def act (q : Q) (w : List S) : Q := w.foldl A.step q

/-- The preimage `K w⁻¹ = {q ∈ Q : q.w ∈ K}` (tex:229). -/
def pre [Fintype Q] [DecidableEq Q] (K : Finset Q) (w : List S) : Finset Q :=
  Finset.univ.filter (fun q => A.act q w ∈ K)

/-- The image `K.w = {q.w : q ∈ K}`; `Q.w` is `img univ w`. -/
def img [DecidableEq Q] (K : Finset Q) (w : List S) : Finset Q :=
  K.image (fun q => A.act q w)

/-- `w` is a reset word: it maps all states to one state (tex:64). -/
def IsReset (w : List S) : Prop := ∃ r : Q, ∀ q : Q, A.act q w = r

/-- `A` is synchronizing: some word is a reset word (tex:64). -/
def Synchronizing : Prop := ∃ w : List S, A.IsReset w

/-- The reset threshold `rt(A)`, the least length of a reset word (tex:64-65); `⊤` if `A` is not synchronizing. -/
noncomputable def rt : ℕ∞ := minLen A.IsReset

/-- `ext(K)`: the least length of a word `w` with `|K w⁻¹| > |K|`, infinite if there is none (tex:235-236). -/
noncomputable def ext [Fintype Q] [DecidableEq Q] (K : Finset Q) : ℕ∞ :=
  minLen (fun w => K.card < (A.pre K w).card)

/-- `w` moves `x` across `K`: `x` lies in exactly one of the sets `K` and `K w⁻¹`, that is,
`[x.w ∈ K] ≠ [x ∈ K]` (tex:310-311). -/
def MovesAcross [DecidableEq Q] (x : Q) (K : Finset Q) (w : List S) : Prop :=
  decide (A.act x w ∈ K) ≠ decide (x ∈ K)

/-- `esc_x(K)`: the least length of a word that moves `x` across `K`, infinite if there is none (tex:311-313). -/
noncomputable def esc [DecidableEq Q] (x : Q) (K : Finset Q) : ℕ∞ :=
  minLen (A.MovesAcross x K)

/-- A set `K` is closed if `K.b ⊆ K` for every letter `b` (tex:231). -/
def IsClosed (K : Finset Q) : Prop := ∀ q ∈ K, ∀ b : S, A.step q b ∈ K

/-- `A` is strongly connected: `∅` and `Q` are its only closed sets (tex:231-232). -/
def StronglyConnected [Fintype Q] : Prop :=
  ∀ K : Finset Q, A.IsClosed K → K = ∅ ∨ K = Finset.univ

/-- A letter `c` is merging if it is not injective (tex:427). -/
def Merging (c : S) : Prop := ¬ Function.Injective (fun q => A.step q c)

/-- The automaton `A|_C` obtained by restricting the letters to a closed set `C` (tex:537-538, tex:576). -/
def restrict (C : Finset Q) (hC : A.IsClosed C) : Automaton C S where
  step q b := ⟨A.step q.1 b, hC q.1 q.2 b⟩

/-- The two states `x₁, x₂` form a block of a congruence: every letter maps them to one state or to the pair itself
(tex:99-100, tex:661). -/
def IsBlockPair [DecidableEq Q] (x₁ x₂ : Q) : Prop :=
  ∀ b : S, A.step x₁ b = A.step x₂ b ∨ ({A.step x₁ b, A.step x₂ b} : Finset Q) = {x₁, x₂}

section Weights

variable [Fintype Q] [DecidableEq Q] [Fintype S]

/-- The `Q × Q` matrix `M_w` of a word: `(M_w)_{q,q'} = 1` if `q.w = q'` and `0` otherwise (tex:238). -/
noncomputable def Mw (w : List S) : Matrix Q Q ℝ := fun q q' => if A.act q w = q' then 1 else 0

/-- The weighted matrix `M = ∑_b p_b M_b` (tex:245). -/
noncomputable def M (p : S → ℝ) : Matrix Q Q ℝ := ∑ b, p b • A.Mw [b]

/-- A stationary vector for the weights `p`: a nonzero `α ∈ ℝ^Q` with `αᵀ M = αᵀ` (tex:246-247). -/
def IsStationary (p : S → ℝ) (α : Q → ℝ) : Prop := α ≠ 0 ∧ Matrix.vecMul α (A.M p) = α

/-- The in-weight `in_p(q) = ∑_b p_b |{q} b⁻¹|`, the total weight of the edges that end at `q` (tex:251-252). -/
noncomputable def inW (p : S → ℝ) (r : Q) : ℝ := ∑ b, p b * ((A.pre {r} [b]).card : ℝ)

/-- The cost of `K` for a vector `β` (tex:269-270, tex:303-304): the least length of a word `w` with
`β(K w⁻¹) ≠ β(K)`, infinite if there is none. -/
noncomputable def cost (β : Q → ℝ) (K : Finset Q) : ℕ∞ :=
  minLen (fun w => wt β (A.pre K w) ≠ wt β K)

/-- `w` raises `α` (for `K`) if `α(K w⁻¹) > α(K)` (tex:303). -/
def Raises (α : Q → ℝ) (K : Finset Q) (w : List S) : Prop := wt α K < wt α (A.pre K w)

end Weights

end Automaton

/-- A witness `(E, s, p)` that the automaton `A` is quasi-Eulerian of degree `d` (Definition 1.1, tex:76-84):
`|E| = n - d`, `s ∈ E`, and letter weights `p` (real, `p_b > 0`, `∑ p_b = 1`) such that
(a) every edge that starts in `X = Q \ E` ends in `X ∪ {s}`, and (b) every state `r ∈ E \ {s}` has in-weight one. -/
structure QEWitness [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (d : ℕ) where
  E : Finset Q
  s : Q
  p : S → ℝ
  card_E : E.card = Fintype.card Q - d
  s_mem : s ∈ E
  weights : IsLetterWeights p
  edge_X : ∀ q, q ∉ E → ∀ b, A.step q b ∉ E ∨ A.step q b = s
  inW_one : ∀ r ∈ E, r ≠ s → A.inW p r = 1

/-- The exceptional states `X = Q \ E` of a witness (tex:83). -/
def QEWitness.X [Fintype Q] [DecidableEq Q] [Fintype S] {A : Automaton Q S} {d : ℕ} (W : QEWitness A d) :
    Finset Q :=
  Finset.univ \ W.E

/-- `A` is quasi-Eulerian of degree `d` (Definition 1.1, tex:77): it has a witness of degree `d`. -/
def QuasiEulerian [Fintype Q] [DecidableEq Q] [Fintype S] (A : Automaton Q S) (d : ℕ) : Prop :=
  Nonempty (QEWitness A d)

/-- The Černý automaton `C_n` (tex:65-67, tex:545): states `{0, …, n-1}`, letters `a = 0` and `b = 1`; the letter `a`
maps `0` to `1` and fixes every other state, and `b` maps `q` to `q + 1 mod n`. -/
def cerny (n : ℕ) [NeZero n] : Automaton (Fin n) (Fin 2) where
  step q c := if c = 0 then (if q = 0 then 1 else q) else q + 1

/-- The cycles of a map `f : Q → Q` (tex:156 and Remark 4.4, tex:561): the orbit sets `{q, f q, f² q, …}` of its periodic points `q`
(a point is periodic if `f^k q = q` for some `1 ≤ k ≤ |Q|`). -/
def cycles [Fintype Q] [DecidableEq Q] (f : Q → Q) : Finset (Finset Q) :=
  (Finset.univ.filter (fun q => ∃ k ∈ Finset.range (Fintype.card Q), f^[k + 1] q = q)).image
    (fun q => (Finset.range (Fintype.card Q)).image (fun k => f^[k] q))

/-- `A` is one-cluster: some letter has only one cycle (tex:156). -/
def OneCluster [Fintype Q] [DecidableEq Q] (A : Automaton Q S) : Prop :=
  ∃ b : S, (cycles (fun q => A.step q b)).card = 1

end CernyQE
