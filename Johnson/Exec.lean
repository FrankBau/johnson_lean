/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
/-
  Johnson's algorithm for simple s-t paths (no length bound) as an executable, tick-instrumented Lean 4 function.

  CIRCUIT and UNBLOCK of Johnson (1975) with the target t in place of the root s: the closing edge (v, t) is tested
  inline, before the blocked test, as `w = s` is in CIRCUIT.  Line-by-line transcription of Python/johnson_traced.py:
  same cost model, same event schema, every event stamped with the step counter *after* the step it represents.
  Core Lean only (no Mathlib).  The definitions at the end say what the proofs are about.

  Cost model, counted at exactly these sites:
    search call at v    : 1 (entry) + 1 per scanned successor (L1)
    producing an output : |path| = h + 2
    failed return at v  : 1 per successor (L2: the test v ∉ B[w], counted as one step, and the insertion)
    unblock call at u   : 1 (the call) + 1 per entry of B[u]

  Two depth guards, which Python does not have, give Lean its termination measures: a call of `search` at depth h + 1
  needs h + 1 < n, a nested call of `unblock` at depth d + 1 needs d + 1 < n.  They never fail (`guards_vacuous`); if
  one did, the run would emit an `abort` event.
-/

namespace Johnson

/-- directed graph on `Fin n`, as successor lists (Johnson needs no predecessor lists) -/
structure Graph (n : Nat) where
  succ : Fin n → List (Fin n)

/-- well-formed digraph: no duplicate edges (self-loops are harmless) -/
def Graph.WF {n : Nat} (G : Graph n) : Prop := ∀ u, (G.succ u).Nodup

/-- the number of edges -/
def Graph.m {n : Nat} (G : Graph n) : Nat := ((List.finRange n).map fun v => (G.succ v).length).sum

/-- the event schema of johnson_traced.py, plus `abort` for a failed depth guard -/
inductive Ev (n : Nat) where
  | start   (step : Nat)
  | enter   (step : Nat) (v : Fin n) (h : Nat)
  | exit    (step : Nat) (v : Fin n) (found : Bool)
  | output  (step : Nat) (path : List (Fin n))
  | unblock (step : Nat) (u : Fin n) (L : List (Fin n))
  | abort   (step : Nat)
  | term    (step : Nat)
  deriving DecidableEq

/-- algorithm state: blocked flags, B-lists, stack S, step counter, recorded trace -/
structure St (n : Nat) where
  blocked : Vector Bool n
  B       : Vector (List (Fin n)) n
  S       : Array (Fin n)
  steps   : Nat
  trace   : Array (Ev n)

abbrev M (n : Nat) := StateM (St n)

namespace M
variable {n : Nat}
def tick (c : Nat := 1) : M n Unit := modify fun st => { st with steps := st.steps + c }
def steps : M n Nat := return (← get).steps
def emit (e : Ev n) : M n Unit := modify fun st => { st with trace := st.trace.push e }
def isBlocked (x : Fin n) : M n Bool := return (← get).blocked[x]
def setBlocked (x : Fin n) (val : Bool) : M n Unit := modify fun st => { st with blocked := st.blocked.set x.1 val x.2 }
def blist (x : Fin n) : M n (List (Fin n)) := return (← get).B[x]
def setBlist (x : Fin n) (L : List (Fin n)) : M n Unit := modify fun st => { st with B := st.B.set x.1 L x.2 }
def stack : M n (Array (Fin n)) := return (← get).S
def push (v : Fin n) : M n Unit := modify fun st => { st with S := st.S.push v }
def pop : M n Unit := modify fun st => { st with S := st.S.pop }
end M
open M

variable {n : Nat}

/-- UNBLOCK(u): unblock u, then every blocked vertex on the B-list of u, recursively; the B-list of u is emptied.
    The depth d is an explicit argument because the termination measure n - d must be visible to Lean. -/
def unblock (u : Fin n) (d : Nat) : M n Unit := do
  setBlocked u false
  tick
  let L ← blist u
  setBlist u []
  emit (.unblock (← steps) u L)
  for w in L do
    tick
    if (← isBlocked w) then
      if hd : d + 1 < n then
        unblock w (d + 1)
      else
        emit (.abort (← steps))
termination_by n - d

/-- CIRCUIT(v) with target t; returns whether a path was found.  The depth h = |S| is an explicit argument because
    the termination measure n - h must be visible to Lean. -/
def search (G : Graph n) (t : Fin n) (v : Fin n) (h : Nat) : M n Bool := do
  push v                                                    -- stack v
  setBlocked v true
  tick
  emit (.enter (← steps) v h)
  let mut found := false
  for w in G.succ v do                                      -- L1
    tick
    if w = t then
      tick (h + 2)
      emit (.output (← steps) ((← stack).toList ++ [t]))
      found := true
    else if !(← isBlocked w) then
      if hh : h + 1 < n then
        let r ← search G t w (h + 1)
        found := found || r
      else
        emit (.abort (← steps))
  if found then                                             -- L2
    unblock v 0
  else
    for w in G.succ v do
      tick
      if v ∉ (← blist w) then
        setBlist w ((← blist w) ++ [v])
  emit (.exit (← steps) v found)
  pop                                                       -- unstack v
  return found
termination_by n - h

/-- the complete event trace of a run from s to t -/
def johnson (G : Graph n) (s t : Fin n) : List (Ev n) :=
  let run : M n Unit := do
    emit (.start (← steps))
    let _ ← search G t s 0
    emit (.term (← steps))
  (Id.run (run.run { blocked := Vector.replicate n false, B := Vector.replicate n [], S := #[], steps := 0, trace := #[] })).2.trace.toList

/-! ## What the proofs are about -/

/-- the outputs, in order -/
def outputs (tr : List (Ev n)) : List (List (Fin n)) :=
  tr.filterMap fun | .output _ p => some p | _ => none

/-- step stamps of the observable events o_0 = start, o_1 .. o_T = outputs, o_{T+1} = term -/
def obsSteps (tr : List (Ev n)) : List Nat :=
  tr.filterMap fun | .start s | .output s _ | .term s => some s | _ => none

/-- a failed depth guard -/
def Ev.isAbort : Ev n → Bool
  | .abort _ => true
  | _ => false

/-- p is a simple s-t path (node list) in G -/
def Graph.SimplePath (G : Graph n) (s t : Fin n) (p : List (Fin n)) : Prop :=
  p.head? = some s ∧ p.getLast? = some t ∧ p.Nodup ∧ ∀ e ∈ p.zip p.tail, e.2 ∈ G.succ e.1

end Johnson
