/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Johnson

open Johnson

-- The following statements assert that the proofs of the main claims rely only on the standard axioms

/-- info: 'Johnson.johnson_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms johnson_sound

/-- info: 'Johnson.johnson_complete_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms johnson_complete_once

/-- info: 'Johnson.johnson_guards_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms johnson_guards_vacuous

/-- info: 'Johnson.johnson_worst_case_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms johnson_worst_case_delay

/-- info: 'Johnson.johnson_total_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms johnson_total_time

/-! Smoke-test driver: reads cases.txt, prints the trace of `johnson` per case in Python repr format
    (nodes as indices), for a plain `diff` against johnson_traced.py. -/

def pyNode {n : Nat} (v : Fin n) : String := toString v.val

def pyBool (b : Bool) : String := if b then "True" else "False"

/-- a Python tuple of nodes: `()`, `(a,)`, `(a, b)` -/
def pyTuple {n : Nat} (p : List (Fin n)) : String :=
  match p with
  | [v] => s!"({pyNode v},)"
  | _ => s!"({", ".intercalate (p.map pyNode)})"

def pyEv {n : Nat} : Ev n → String
  | .start s         => s!"('start', {s})"
  | .enter s v h     => s!"('enter', {s}, {pyNode v}, {h})"
  | .exit s v f      => s!"('exit', {s}, {pyNode v}, {pyBool f})"
  | .output s p      => s!"('output', {s}, {pyTuple p})"
  | .unblock s u L   => s!"('unblock', {s}, {pyNode u}, {pyTuple L})"
  | .abort s         => s!"('abort', {s})"
  | .term s          => s!"('term', {s})"

def nats (line : String) : List Nat := ((line.splitOn " ").filter (· ≠ "")).map String.toNat!

def runCase (n s t : Nat) (succL : Array (List Nat)) : List String :=
  if hs : s < n then
    if ht : t < n then
      let toFin (xs : List Nat) : List (Fin n) := xs.filterMap fun x => if h : x < n then some ⟨x, h⟩ else none
      let succA : Array (List (Fin n)) := succL.map toFin
      let G : Graph n := { succ := fun v => succA[v.1]! }
      (johnson G ⟨s, hs⟩ ⟨t, ht⟩).map pyEv
    else ["bad t"]
  else ["bad s"]

def main (args : List String) : IO Unit := do
  let lines ← IO.FS.lines (args.headD "cases.txt")
  let out ← IO.getStdout
  let mut i := 0
  while i < lines.size do
    let hdr := (lines[i]!.splitOn " ").filter (· ≠ "")
    let name := hdr[1]!
    let n := hdr[2]!.toNat!
    let s := hdr[3]!.toNat!
    let t := hdr[4]!.toNat!
    let succL := (lines.extract (i + 1) (i + 1 + n)).map nats
    out.putStrLn s!"case {name}"
    for e in runCase n s t succL do
      out.putStrLn e
    i := i + 1 + n
