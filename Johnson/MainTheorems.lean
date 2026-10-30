/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Delay

/-!
  The main theorems in one place.  Each statement is copied from `Johnson/Challenge.lean` and proved by the internal theorem in
  one line.  The `#guard_msgs` checks make `lake build` fail if one of them depends on an axiom other than `propext`,
  `Classical.choice` and `Quot.sound` (in particular on `sorryAx`).

  To trust these theorems, read `Johnson/Challenge.lean`, which states them with the same names and `sorry`, and the definitions it
  uses, in `Johnson/Exec.lean`; `CheckChallenge.lean` checks that the statements here and there match.

  Everything else in the library is proof, checked by Lean.
-/

namespace Johnson

/-- soundness (Johnson's Corollary 1): every output is a simple s-t path -/
theorem soundness {n : Nat} (G : Graph n) (s t : Fin n) (hst : s ≠ t) : ∀ p ∈ outputs (johnson G s t), G.SimplePath s t p :=
  johnson_sound G s t hst

/-- completeness (Johnson's Lemma 2): every simple s-t path is output exactly once -/
theorem completeness {n : Nat} (G : Graph n) (s t : Fin n) (hG : G.WF) (hst : s ≠ t) : ∀ p, G.SimplePath s t p → (outputs (johnson G s t)).count p = 1 :=
  johnson_complete_once G s t hG hst

/-- worst-case delay (Johnson's Lemma 3): consecutive observable events (start, outputs, termination) are at most 4n + 5m steps apart -/
theorem worst_case_delay {n : Nat} (G : Graph n) (s t : Fin n) (hst : s ≠ t) :
    ∀ x ∈ (obsSteps (johnson G s t)).zip (obsSteps (johnson G s t)).tail, x.2 - x.1 ≤ 4 * n + 5 * G.m :=
  johnson_worst_case_delay G s t hst

/-- total time (Johnson's Corollary 2): the τ-th observable event happens after at most τ(4n + 5m) steps -/
theorem total_time {n : Nat} (G : Graph n) (s t : Fin n) (hst : s ≠ t) :
    ∀ τ (hτ : τ < (obsSteps (johnson G s t)).length), (obsSteps (johnson G s t))[τ] ≤ τ * (4 * n + 5 * G.m) :=
  johnson_total_time G s t hst

/-- the depth guards never fire: the run has no `abort` event, so it is the run of Johnson's algorithm without them -/
theorem guards_vacuous {n : Nat} (G : Graph n) (s t : Fin n) (hst : s ≠ t) : ∀ e ∈ johnson G s t, e.isAbort = false :=
  johnson_guards_vacuous G s t hst

/-! ## Axioms -/

/-- info: 'Johnson.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms soundness

/-- info: 'Johnson.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completeness

/-- info: 'Johnson.worst_case_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worst_case_delay

/-- info: 'Johnson.total_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms total_time

/-- info: 'Johnson.guards_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guards_vacuous

end Johnson
