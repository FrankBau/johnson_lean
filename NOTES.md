# Johnson formalization: notes

## State (2026-10-30)
- Plan: phase 0 (executable and smoke test) and phase A (soundness, completeness) done; phase B (worst-case delay, Johnson's Lemma 3,
  and total time, Corollary 2) not started.
- `Johnson/Exec.lean`: executable, tick-instrumented transcription of `Python/johnson_traced.py`. Core only.
- Smoke test: byte-identical traces on 1015 instances (graphs Z, Y, Y2, complete digraphs K3..K6, stride-2 ladders L1..L4, dead
  cliques D2..D5, the 1000 path-mode random instances of the BS-DFS smoke test), 1,218,327 events, 271,372 outputs, no `abort`.
- `Python/selfcheck.py`: on 16,000 random digraphs (n = 2..9), `johnson_traced.py` has the outputs of `johnson_paths` in
  `../johnson.py` and of a plain DFS, in the same order, and the same search calls as `johnson_paths` (without its calls of
  search(t)). Largest interval between observable events: 0.66 (4n + 5m), the bound expected for phase B.
- `lake build`: no `sorry`, no warnings; `#guard_msgs` in `Main.lean`: the three theorems use `propext`, `Classical.choice`,
  `Quot.sound`. `lake env leanchecker --fresh Johnson.Complete`: passes (about 40 s).

## Deviations from the Python code (all deliberate)
1. The closing edge (v, t) is tested inline, before the blocked test, as `w = s` in Johnson's CIRCUIT. johnson.py calls search(t)
   instead; same outputs, same calls at the other vertices (selfcheck).
2. Depth guards for termination: `search` calls `search w (h + 1)` only if h + 1 < n, `unblock` calls `unblock w (d + 1)` only if
   d + 1 < n; otherwise it emits `abort`. `johnson_guards_vacuous`: never.
3. B-lists are lists, appended at the end and popped from the front (Johnson's ALGOL), so the trace is deterministic; johnson.py pops
   a `set` in hash order. The order does not change which vertices get unblocked (Lemma 1).
4. Cost model: the membership test `v ∉ B[w]` counts as one step, as the stack test does in BS-DFS (O(1) with a bit matrix or a hash
   set). The Lean program itself tests membership by a linear scan.

## The invariant (Johnson/Invariant.lean)
Between steps, for the stack S: (A) stack vertices are blocked, (T) t is never blocked, (B) a blocked vertex off the stack is on the
B-list of each successor, (D) B-lists hold predecessors, (E) stale entries, (F) only blocked vertices have nonempty B-lists, (N) no
duplicates in B-lists.
- Johnson's Lemma 1 (ii) is not a clause but `Inv.dead`, from (B), (F), (T): a blocked vertex off the stack has only blocked
  successors, so a walk avoiding the stack stays blocked up to t.
- (E) has no counterpart in the paper: UNBLOCK(u) empties only B(u), so a vertex unblocked through one list stays on the lists of its
  other successors and may be back on the stack when one of them is emptied. (E): if x ∈ B[w] is on the stack, then w is on the
  stack up to x, or off the stack and cannot reach t avoiding the stack up to x. In the chain of v, a vertex u that the chain
  unblocks reaches t avoiding the stack below v, so by (E) no entry of B[u] is on the stack below v (`child_pos`). This is the step
  that Johnson's proof of Lemma 1, Case 2 (and the write-up's) leaves implicit (my reading).

## How it went
- `mvcgen` as in BS-DFS. The unblock chain (`unblock_spec`, 6 VCs) and the search (`search_spec`, 12 VCs) were closed by step lemmas
  proved separately, one per VC; both mvcgen proofs passed on the first run.
- Friction: ghost variables of a spec must be fixed by equations at the front of the precondition. The list of enclosing unblock calls
  (for the depth guard) has no such equation, so it is existential in `UPre.deep`. The loop of the failed return quantifies the
  B-lists at its start existentially in its invariant, to avoid naming the outer state.
- `lake clean` fails on this OneDrive folder (permission denied on `.lake/build/bin`); `lake env lean <file>` per module re-checks
  everything instead.

## Paper results and their Lean names
| Johnson 1975 (path version) | Lean name (file) |
|---|---|
| Lemma 1 (ii) | `Inv.dead` (Invariant) |
| Lemma 1, for UNBLOCK at L2 | `lemma1` (Complete), from `unblock_spec` (Unblock) and `Inv.chain` (Invariant) |
| Corollary 1 (only elementary circuits / simple paths) | `johnson_sound` (Complete) |
| Lemma 2 (every circuit / path exactly once) | `johnson_complete_once` (Complete), Call Completeness in `search_spec` |
| Lemma 3 (O(n + e) between outputs) | phase B |
| Corollary 2 (O((n + e)(c + 1)) total) | phase B |

## Working agreements with Frank
- No expensive tests or long runs without asking first; small smoke tests and tool installs are fine.
- Code in natural line width, no forced line breaks.
- Mark conjectures and unverified claims explicitly.
