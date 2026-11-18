/-
CernyQE/Proofs/Census514/Search.lean — the computable search behind the census of Proposition 5.14 (Lean core only).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
-/

/-!
An automaton on the states `0, …, n-1` with the letters `0, 1` is given by a table `tbl`: the images of `0, …, n-1` under
the letter `0`, then under the letter `1`. A member of the census is checked by a breadth-first search over subsets
(bitmasks) that returns a candidate reset word; the word is then re-checked directly. If no word of length `≤ M` is
found, a set of pairs closed under both letters and off the diagonal is searched for and checked (a certificate that
the automaton is not synchronizing). Only the two checks `isResetB` and `nonSyncB` are trusted (they are proved sound
in `ImageSearch.lean`); the searches themselves need no proof. `allSeq` runs over all edge assignments with
prescribed in-degrees. Everything uses structural recursion on `Nat` and lists, so the kernel evaluates it quickly.
-/

namespace CernyQE
namespace Census514

/-! ### Tables and the two trusted checks -/

/-- The image of the state `q` under the letter `c` (reduced mod `n`, so that it is always a state). -/
def stp (n : Nat) (tbl : List Nat) (q c : Nat) : Nat := tbl.getD (c * n + q) 0 % n

/-- The state reached from `q` by the word `w`. -/
def run (n : Nat) (tbl : List Nat) (q : Nat) (w : List (Fin 2)) : Nat :=
  w.foldl (fun q c => stp n tbl q c.val) q

/-- `w` maps every state to the image of `0`. -/
def isResetB (n : Nat) (tbl : List Nat) (w : List (Fin 2)) : Bool :=
  (List.range n).all (fun q => Nat.beq (run n tbl q w) (run n tbl 0 w))

/-- Membership of the pair `(p, q)` in a list of pairs. -/
def memP : List (Nat × Nat) → Nat → Nat → Bool
  | [], _, _ => false
  | x :: rest, p, q => (Nat.beq x.1 p && Nat.beq x.2 q) || memP rest p q

/-- The pair `pq` is off the diagonal, consists of states, and both letters map it into `P`. -/
def pairOK (n : Nat) (tbl : List Nat) (P : List (Nat × Nat)) (pq : Nat × Nat) : Bool :=
  !(Nat.beq pq.1 pq.2) && Nat.blt pq.1 n && Nat.blt pq.2 n &&
    memP P (stp n tbl pq.1 0) (stp n tbl pq.2 0) && memP P (stp n tbl pq.1 1) (stp n tbl pq.2 1)

/-- A certificate that the automaton is not synchronizing: a nonempty set of pairs, off the diagonal, closed under
both letters. -/
def nonSyncB (n : Nat) (tbl : List Nat) (P : List (Nat × Nat)) : Bool :=
  !P.isEmpty && P.all (pairOK n tbl P)

/-! ### The untrusted searches -/

/-- The letter `0`. -/
def l0 : Fin 2 := ⟨0, by decide⟩
/-- The letter `1`. -/
def l1 : Fin 2 := ⟨1, by decide⟩

/-- Bit `q` of `S`. -/
def mem (S q : Nat) : Bool := Nat.beq ((S >>> q) % 2) 1

/-- The image of the subset (bitmask) `S` under a letter given by its list of images (states `q, q+1, …`). -/
def imgFrom (S : Nat) : List Nat → Nat → Nat → Nat
  | [], _, acc => acc
  | t :: ts, q, acc => imgFrom S ts (q + 1) (bif mem S q then acc ||| (1 <<< t) else acc)

/-- `S` has exactly one bit. -/
def isSingleton (S : Nat) : Bool := !(Nat.beq S 0) && Nat.beq (S &&& (S - 1)) 0

/-- One breadth-first layer: the new frontier (subset, reversed word) and the visited set (a bitmask of subsets). -/
def layer (fa fb : List Nat) : List (Nat × List (Fin 2)) → List (Nat × List (Fin 2)) → Nat →
    List (Nat × List (Fin 2)) × Nat
  | [], acc, vis => (acc, vis)
  | (S, w) :: rest, acc, vis =>
    let Sa := imgFrom S fa 0 0
    let p : List (Nat × List (Fin 2)) × Nat :=
      bif mem vis Sa then (acc, vis) else ((Sa, l0 :: w) :: acc, vis ||| (1 <<< Sa))
    let Sb := imgFrom S fb 0 0
    let p : List (Nat × List (Fin 2)) × Nat :=
      bif mem p.2 Sb then p else ((Sb, l1 :: w) :: p.1, p.2 ||| (1 <<< Sb))
    layer fa fb rest p.1 p.2

/-- The word of a singleton in the frontier, if any. -/
def findSingle : List (Nat × List (Fin 2)) → Option (List (Fin 2))
  | [] => none
  | (S, w) :: rest => bif isSingleton S then some w.reverse else findSingle rest

/-- Breadth-first search for a singleton image, at most `fuel` layers deep. -/
def bfs (fa fb : List Nat) : Nat → List (Nat × List (Fin 2)) → Nat → Option (List (Fin 2))
  | 0, front, _ => findSingle front
  | k + 1, front, vis =>
    match findSingle front with
    | some w => some w
    | none => let p := layer fa fb front [] vis; bfs fa fb k p.1 p.2

/-- The list of images of a letter. -/
def letterList (n : Nat) (tbl : List Nat) (c : Nat) : List Nat := (List.range n).map (fun q => stp n tbl q c)

/-- A candidate reset word of length at most `M`. -/
def findWord (n M : Nat) (tbl : List Nat) : Option (List (Fin 2)) :=
  bfs (letterList n tbl 0) (letterList n tbl 1) M [(2 ^ n - 1, [])] (1 <<< (2 ^ n - 1))

/-- The closure of a set of pairs under both letters (`none` if it meets the diagonal). -/
def pairClose (n : Nat) (tbl : List Nat) : Nat → List (Nat × Nat) → List (Nat × Nat) → Option (List (Nat × Nat))
  | 0, _, seen => some seen
  | _ + 1, [], seen => some seen
  | k + 1, pq :: queue, seen =>
    bif Nat.beq pq.1 pq.2 then none else
    let x := (stp n tbl pq.1 0, stp n tbl pq.2 0)
    let y := (stp n tbl pq.1 1, stp n tbl pq.2 1)
    let p : List (Nat × Nat) × List (Nat × Nat) :=
      bif memP seen x.1 x.2 then (queue, seen) else (x :: queue, x :: seen)
    let p : List (Nat × Nat) × List (Nat × Nat) :=
      bif memP p.2 y.1 y.2 then p else (y :: p.1, y :: p.2)
    pairClose n tbl k p.1 p.2

/-- The closure of the first pair whose closure stays off the diagonal. -/
def firstClosed (n : Nat) (tbl : List Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | pq :: rest =>
    match pairClose n tbl (n * n + 1) [pq] [pq] with
    | some P => P
    | none => firstClosed n tbl rest

/-- The pairs `(p, q)` with `p < q < n`. -/
def pairsLT (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun p => ((List.range n).filter (fun q => Nat.blt p q)).map (fun q => (p, q)))

/-- A candidate certificate that the automaton is not synchronizing. -/
def findPairs (n : Nat) (tbl : List Nat) : List (Nat × Nat) := firstClosed n tbl (pairsLT n)

/-- One member is fine: it has a (checked) reset word of length `≤ M`, or it is (certifiably) not synchronizing. -/
def memberOK (n M : Nat) (tbl : List Nat) : Bool :=
  match findWord n M tbl with
  | some w => Nat.ble w.length M && isResetB n tbl w
  | none => nonSyncB n tbl (findPairs n tbl)

/-! ### The enumeration -/

/-- `leaf (pre ++ σ)` for every list `σ` of length `k` that uses each value `v < n` at most `cnt[v]` times. -/
def allSeq (n : Nat) (leaf : List Nat → Bool) : Nat → List Nat → List Nat → Bool
  | 0, _, pre => leaf pre
  | k + 1, cnt, pre =>
    (List.range n).all (fun v => Nat.beq (cnt.getD v 0) 0 ||
      allSeq n leaf k (cnt.set v (cnt.getD v 0 - 1)) (pre ++ [v]))

/-- The state of a target code `0 = x₁`, `1 = x₂`, `2 = s`, with `s = 0`, `x₁ = n-2`, `x₂ = n-1`. -/
def code (n k : Nat) : Nat := if k = 0 then n - 2 else if k = 1 then n - 1 else 0

/-- The table of the automaton with the raw configuration `t = [x₁.a, x₁.b, x₂.a, x₂.b, ν₁, ν₂]` whose edges from
`E = {0, …, n-3}` are `σ = [0.a, …, (n-3).a, 0.b, …, (n-3).b]`. -/
def tblOf (n : Nat) (t σ : List Nat) : List Nat :=
  σ.take (n - 2) ++ [code n (t.getD 0 0), code n (t.getD 2 0)] ++ σ.drop (n - 2) ++
    [code n (t.getD 1 0), code n (t.getD 3 0)]

/-- The in-degrees from `E`: `2 - ν₁ - ν₂` at `s = 0`, `2` on `E \ {s}`, `ν₁` at `x₁`, `ν₂` at `x₂`. -/
def cntOf (n : Nat) (t : List Nat) : List Nat :=
  (List.range n).map (fun v => if v = 0 then 2 - t.getD 4 0 - t.getD 5 0 else if v = n - 2 then t.getD 4 0
    else if v = n - 1 then t.getD 5 0 else 2)

/-- The leaf check of the census. -/
def leafOf (n M : Nat) (t : List Nat) (σ : List Nat) : Bool := memberOK n M (tblOf n t σ)

/-- One chunk: the edge assignments whose first two entries (`0.a`, `1.a`) are `v₁`, `v₂`. -/
def chunk (n M : Nat) (t : List Nat) (v₁ v₂ : Nat) : Bool :=
  Nat.beq ((cntOf n t).getD v₁ 0) 0 ||
    (Nat.beq (((cntOf n t).set v₁ ((cntOf n t).getD v₁ 0 - 1)).getD v₂ 0) 0 ||
      allSeq n (leafOf n M t) (2 * (n - 2) - 2)
        (((cntOf n t).set v₁ ((cntOf n t).getD v₁ 0 - 1)).set v₂
          (((cntOf n t).set v₁ ((cntOf n t).getD v₁ 0 - 1)).getD v₂ 0 - 1)) ([] ++ [v₁] ++ [v₂]))

/-- The nine configurations of the integer classes up to renaming `x₁ ↔ x₂` and `a ↔ b`, as raw lists
`[x₁.a, x₁.b, x₂.a, x₂.b, ν₁, ν₂]`. -/
def canonCfgs : List (List Nat) :=
  [[0, 1, 0, 2, 0, 2], [0, 1, 0, 2, 1, 1], [0, 1, 0, 2, 2, 0], [0, 1, 1, 2, 2, 0], [0, 1, 2, 0, 0, 2],
    [0, 1, 2, 0, 1, 1], [0, 1, 2, 0, 2, 0], [0, 1, 2, 1, 2, 0], [1, 1, 0, 2, 2, 0]]

end Census514
end CernyQE
