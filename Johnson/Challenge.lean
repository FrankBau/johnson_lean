/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson.Exec

/-!
  The main theorems, stated with `sorry` in place of their proofs.  This file and its import are all you have to read:
  `Johnson/Exec.lean` contains definitions only: `Graph`, `Graph.WF`, `Graph.m`, `johnson` (with `search`, `unblock` and the step
  counter), `outputs`, `obsSteps`, `Ev.isAbort` and `Graph.SimplePath`.

  The same theorems, with the same names and statements, are proved in `Johnson/MainTheorems.lean`; `comparator.json` lets the
  comparator tool check that the statements match, and `CheckChallenge.lean` checks the same without it.
  Nothing imports this file, so `lake build` skips it; build it with `lake build Johnson.Challenge`.
-/

namespace Johnson

/-- soundness (Johnson's Corollary 1): every output is a simple s-t path -/
theorem soundness {n : Nat} (G : Graph n) (s t : Fin n) (hst : s ≠ t) : ∀ p ∈ outputs (johnson G s t), G.SimplePath s t p :=
  sorry

/-- completeness (Johnson's Lemma 2): every simple s-t path is output exactly once -/
theorem completeness {n : Nat} (G : Graph n) (s t : Fin n) (hG : G.WF) (hst : s ≠ t) : ∀ p, G.SimplePath s t p → (outputs (johnson G s t)).count p = 1 :=
  sorry

/-- worst-case delay (Johnson's Lemma 3): consecutive observable events (start, outputs, termination) are at most 4n + 5m steps apart -/
theorem worst_case_delay {n : Nat} (G : Graph n) (s t : Fin n) (hst : s ≠ t) :
    ∀ x ∈ (obsSteps (johnson G s t)).zip (obsSteps (johnson G s t)).tail, x.2 - x.1 ≤ 4 * n + 5 * G.m :=
  sorry

/-- total time (Johnson's Corollary 2): the τ-th observable event happens after at most τ(4n + 5m) steps -/
theorem total_time {n : Nat} (G : Graph n) (s t : Fin n) (hst : s ≠ t) :
    ∀ τ (hτ : τ < (obsSteps (johnson G s t)).length), (obsSteps (johnson G s t))[τ] ≤ τ * (4 * n + 5 * G.m) :=
  sorry

/-- the depth guards never fire: the run has no `abort` event, so it is the run of Johnson's algorithm without them -/
theorem guards_vacuous {n : Nat} (G : Graph n) (s t : Fin n) (hst : s ≠ t) : ∀ e ∈ johnson G s t, e.isAbort = false :=
  sorry

end Johnson
