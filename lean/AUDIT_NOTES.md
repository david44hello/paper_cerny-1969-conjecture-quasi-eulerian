# AUDIT_NOTES — Lean formalization of "The Cerny (1969) conjecture holds for quasi-Eulerian automata of degree one"
## version 0.51 - 20261110 — (e): no axiom declared (not "Cited/ is empty": the published folder has no Cited/).
## version 0.41 - 20261110 — eq_2_1: any real p (not only letter weights).
## version 0.31 - 20261110 — final read: (c) a nonempty state set (sec2_one_stationary_iff) and the positive c of the Method; (d) the full list.
## version 0.21 - 20261110 — two more rows stated more generally (d); Proposition 5.14's small cases named as a proof; (e) axioms.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

Text: the frozen version 4.40, quasi_eulerian_cerny_4.40_fd11aad2.tex (1022 lines; SHA-256 cebb6529b11a9c3573814b7b276cf2aa3d445e19376d33c055138ea66a29dbfc). Figure 3, the proof of Lemma 5.8 and Tables 2 and 3 are read from the separate files listed in CLAIM_MAP.tsv. Every printed claim is a row of
CernyQE/Paper/Statements.lean; CLAIM_MAP.tsv maps every claim of the text to its row(s). No result is cited as an
axiom: the lower bound rt(C_n) = (n-1)^2 for the Cerny automata is proved (CernyQE/Proofs/CernyLower.lean).
C_n is synchronizing and rt(C_n) = (n-1)^2 (Cerny 1964, cited in the paper) are PROVED in Lean (sec4_cn_sync,
cerny_rt_ge); nothing from [Cer64] is assumed.

## (a) Conventions
1. Lengths (rt, ext, esc, cost) are `minLen` values in ℕ∞, equal to ⊤ when no word has the property. So `A.rt ≤ N`
   holds only for a synchronizing automaton.
2. Values that the text leaves undefined (y/(1-z) at z = 1; (I - Z)⁻¹ for a singular I - Z) take Lean's junk value 0.
   No row depends on such a value: each row that uses one carries z < 1 or strong connectivity, under which the value
   is the printed one.
3. Binary automata: letters `a b : S` with `a ≠ b` and every letter `a` or `b`.

## (b) Proof routes that differ from the text (the statements are the printed ones)
1. Lemma 5.5 (tex:638-655) without the Perron-Frobenius theorem. The text uses it twice: for "I - Z singular gives
   Zη = η with η ≥ 0", and for "M irreducible, so its stationary vectors are the multiples of one positive vector".
   The Lean proof (CernyQE/Proofs/Stationary.lean) shows that I - Z is invertible with any real u in the kernel,
   taking the states where |u| is largest (the closed-set argument of the text then applies unchanged), and shows
   positivity and uniqueness from the fact that the support of a nonnegative stationary vector is closed
   (CernyQE/Proofs/LinAlg.lean).
2. Theorem 3.1, the case t > 2 not an integer (tex:452-455, and the Method, tex:199-201). The text pairs each move of x
   out of the set with the later move back. The Lean proof (CernyQE/Proofs/Thm31.lean) instead proves one invariant
   by strong induction on the number of sets of larger value: from a set K with x ∈ K the remaining cost is at most
   (n-1)(n-|K|), and from a set K with x ∉ K at most (n-1)(n-|K|+h) + n-|K|, where h = ⌊t-1⌋. The pairing claim itself
   is also a row (thm_3_1_nonint_pair), proved, and so are the two step facts of the Method (meth_nonint_steps).
3. Proposition 5.14 for 4 ≤ n ≤ 6 (the row prop_5_14_max, and the proof prop_5_14_small_proved that the row prop_5_14
   uses for n = 4, 5, 6) is established in the text from the published computation at tex:932,939-940. Lean supplies its own finite check of all binary automata of these sizes in the integer classes, done by
   `decide` in the kernel (CernyQE/Proofs/Census514/, ImageSearch.lean).

## (c) Hypotheses
1. tex:973 "every automaton with n ≥ 2 states is quasi-Eulerian of degree n-1": the row sec6_qe_n_minus_1 has
   `[Nonempty S]`. With an empty alphabet there are no letter weights (they must sum to 1), so no witness exists;
   the text's automata always have letters.
2. tex:253-254 "α = 1 is stationary if and only if every in-weight is one": the row sec2_one_stationary_iff has
   `[Nonempty Q]`. With no states the only vector is 0, which is not stationary (a stationary vector is nonzero,
   tex:246), while every in-weight is one vacuously; the text's automata always have states.
3. tex:191 "When α is constant off one state x": the row meth_raise_enlarge_or_move has `0 < c` for that constant. The
   Method describes the positive vector of Theorem 3.1 (tex:194: "Scale α so that α = 1 off x"), so the value is
   positive in the text's setting; for c < 0 a raising word may shrink the set.
4. Hypotheses that the Lean proofs show unused (the rows keep the printed hypotheses): thm_3_1_nonint_pair needs
   neither K_0 = {x} nor the move back; thm_3_1_case_int does not need n ≥ 2; prop_5_14_max (and the proof prop_5_14_small_proved)
   do not need strong connectivity (every synchronizing automaton of the census is strongly connected); rem_4_3_K0 does not
   need n ≥ 2 (it holds for every n ≥ 1); rem_5_15_2k does not need k ≥ 1.

## (d) Rows stated more generally than printed (checked against the text)
1. lem_5_2 (weight count, tex:580-582): for a witness of any degree; the text works in Section 5.1, degree at most two.
2. lem_5_3 (push, tex:590-592): for every nonempty closed set C of any synchronizing automaton; the text: the minimal
   closed set of an automaton of Section 5.1.
3. lem_5_5 (tex:638-643): for every degree d; the text: d ≥ 1.
4. meth_nonint_steps (tex:199-200): for every t; the text: t > 2 not an integer.
5. thm_3_1_case_int (tex:436-439): for every integer t = k ≥ 1; the text: t ≥ 2 an integer.
6. lem_5_10_a, lem_5_10_b (joint orbit, tex:789-793): strong connectivity and a witness of degree two only; the
   standing assumptions of Section 5.4 (tex:681-682: Σ = {a,b}, synchronizing, n ≥ 4) are not needed.
7. lem_2_4_i: for any set T and any α; the text: a nonempty proper S. lem_2_4_two, lem_2_4_six: for every n. eq_2_1:
   for any real p, not only letter weights. ex_3_6_x0, ex_3_6_irrational: for any real t; the text: t > 0.
8. sec54_process_exists (K_0 may be Q), sec54_process_props (no stationarity needed), lem_5_10_compl_good (any numbers
   g1, g2), rem_5_4_reduction (its premise H1 only over the same alphabet).
Other rows of Section 5.4 also leave out standing assumptions of tex:681-682 that their proofs do not use (lem_5_7_a,
lem_5_7_b, prop_5_14_entry, sec54_alpha_formula, sec54_change_depends_on_pattern, sec54_good_cost1,
sec54_aligned_not_good); each such row implies the printed claim once the assumptions are added.

## (e) Axioms
Lean's `#print axioms` for every row (scripts/audit.py; the table is AUDIT.md): each of the rows depends only
on Lean's three standard axioms, propext, Classical.choice and Quot.sound. The project declares no axiom (no result
of another paper is cited as one), and no row takes a computer check or a published result as a hypothesis: the
finite checks are proved in Lean by `decide`.
