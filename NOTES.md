# Johnson formalization: notes

## State (2026-10-30)
- All main theorems proved for s ≠ t, no `sorry`: `soundness`, `completeness`, `worst_case_delay` (4n + 5m),
  `total_time` (τ(4n + 5m)), `guards_vacuous` (`Johnson/MainTheorems.lean`, statements in `Johnson/Challenge.lean`). Axioms
  `propext`, `Classical.choice`, `Quot.sound` only (`#guard_msgs`); `lake env leanchecker --fresh Johnson.MainTheorems` passes
  (about 40 s); `CheckChallenge.lean`: 5 statements and the 53 constants of `Johnson` they depend on agree.
- `Johnson/Exec.lean`: executable, tick-instrumented transcription of `Python/johnson_traced.py`. Core only. About 3,600 lines in all.
- Smoke test: byte-identical traces on 1015 instances (graphs Z, Y, Y2, complete digraphs K3..K6, stride-2 ladders L1..L4, dead
  cliques D2..D5, the 1000 path-mode random instances of the BS-DFS smoke test), 1,218,327 events, 271,372 outputs, no `abort`.
- `Python/selfcheck.py`: on 16,000 random digraphs (n = 2..9), `johnson_traced.py` has the outputs of `johnson_paths` in
  `../johnson.py` and of a plain DFS, in the same order, and the same search calls as `johnson_paths` (without its calls of
  search(t)). Largest interval between observable events: 0.66 (4n + 5m).

## Deviations from the Python code (all deliberate)
1. The closing edge (v, t) is tested inline, before the blocked test, as `w = s` in Johnson's CIRCUIT. johnson.py calls search(t)
   instead; same outputs, same calls at the other vertices (selfcheck).
2. Depth guards for termination: `search` calls `search w (h + 1)` only if h + 1 < n, `unblock` calls `unblock w (d + 1)` only if
   d + 1 < n; otherwise it emits `abort`. `guards_vacuous`: never.
3. B-lists are lists, appended at the end, emptied at the start of `unblock` and walked from the front, so the trace is deterministic;
   johnson.py pops a `set` in hash order. The order does not change which vertices get unblocked (Lemma 1). Johnson's ALGOL and
   johnson.py delete each entry just before handling it, which takes the same steps (argued, not in Lean; AllSimplePaths.md, section 10).
4. Cost model: the membership test `v ∉ B[w]` counts as one step, as the stack test does in BS-DFS (worst-case O(1) and O(n + m) space with per-edge records, see
   AllSimplePaths.md). The Lean program itself tests membership by a linear scan, so the theorems say nothing about the Lean program's own time.

## Soundness and completeness (Johnson/Invariant.lean, Unblock.lean, Complete.lean)
Invariant between steps, for the stack S: (A) stack vertices are blocked, (T) t is never blocked, (B) a blocked vertex off the stack
is on the B-list of each successor, (D) B-lists hold predecessors, (E) stale entries, (F) only blocked vertices have nonempty
B-lists, (N) no duplicates in B-lists.
- Johnson's Lemma 1 (ii) is not a clause but `Inv.dead`, from (B), (F), (T): a blocked vertex off the stack has only blocked
  successors, so a walk avoiding the stack stays blocked up to t.
- (E) has no counterpart in the paper: UNBLOCK(u) empties only B(u), so a vertex unblocked through one list stays on the lists of its
  other successors and may be back on the stack when one of them is emptied. (E): if x ∈ B[w] is on the stack, then w is on the
  stack up to x, or off the stack and cannot reach t avoiding the stack up to x. In the chain of v, a vertex u that the chain
  unblocks reaches t avoiding the stack below v, so by (E) no entry of B[u] is on the stack below v (`child_pos`). This is the step
  that Johnson's proof of Lemma 1, Case 2 (and the write-up's) leaves implicit (my reading).
- `lemma1`: UNBLOCK(v) unblocks exactly the blocked vertices off the stack that reach t avoiding the stack below v, and none of them
  reaches t avoiding the whole stack.

## Delay (Johnson/Trace.lean, Tally.lean, RunFacts.lean, RunSearch.lean, Delay.lean)
The architecture of the BS-DFS delay proof, with a different counting.
- `Tally.lean`: charges entry 1 + |succ|, failed exit |succ| (the B-list insertions), unblock 1 + |B[u]|, output |P|; the steps between
  two observable events are at most the charges in between plus the scans owed by the spine (`tally`). The cost specs carry h < n
  (d < n) instead of the invariant, which makes the specs of the recursive calls vacuous when a guard would fail.
- `RunFacts.lean`, `RunSearch.lean`: facts at every position of the run (`RunOK`), from trace-extended versions of `unblock_spec` and
  `search_spec` (same `mvcgen` cases, the same step lemmas): the event's facts (`EvOK`; the stack and blocked flags are replays of the
  trace), Call Completeness and the return value per frame (`CallOK`), the frame of every exit, and for every unblock event the
  chain it belongs to (`ChainAt`: the chain runs to the fruitful exit of the top frame and has unblock events only).
- `Delay.lean`, per interval (a, c]:
  - every chain in (a, c] belongs to a frame entered before a (`chain_open`);
  - Johnson's Part 1, no vertex is unblocked twice (`unblock_twice`): after the first unblock of u at q₁, u has a simple path W to t
    avoiding the stack; u is entered again before the second unblock; the first vertex z of W entered after the chain of q₁ has W's
    suffix from z avoiding the stack, so its frame outputs (Call Completeness); that frame nests in the frame of the second chain,
    which is the top there, so the output lies inside (a, c);
  - entries and unblocks alternate (`balance`, via the replay of the blocked flags): at most two entries per vertex, one if it is
    on the stack at a; failed exits ≤ entries (`fail_le`); |B[u]| ≤ indeg(u);
  - per vertex 3 + 4·outdeg + indeg, plus the output at c (≤ n): 4n + 5m (`interval_bound`). No well-formedness needed.
- Friction: (1) `nsum` is an abbreviation of `lsum (List.finRange n)`, but `rw` and `omega` treat `nsum f` and
  `lsum (List.finRange n) f` (and `fun z => f z` and `f`) as different; unfold or state with the same form; (2) `by tac, ...` inside
  an anonymous constructor swallows the comma (`cases he, fun ...`); parenthesize; (3) bash heredocs choke on Lean primes, so edits
  of Lean text go through script files; (4) `lake clean` fails on this OneDrive folder (permission denied on `.lake/build/bin`).

## Paper results and their Lean names
| Johnson 1975 (path version) | Lean name (file) |
|---|---|
| Lemma 1 (ii) | `Inv.dead` (Invariant) |
| Lemma 1, for UNBLOCK at L2 | `lemma1` (Complete), from `unblock_spec` (Unblock) and `Inv.chain` (Invariant) |
| Corollary 1 (only elementary circuits / simple paths) | `soundness` (MainTheorems), `johnson_sound` (Complete) |
| Lemma 2 (every circuit / path exactly once) | `completeness` (MainTheorems), `johnson_complete_once` (Complete) |
| Lemma 3, Part 1 (no vertex unblocked twice between outputs) | `RunOK.unblock_twice`, `RunOK.unblock_once` (Delay) |
| Lemma 3, Part 2 (O(n + e) charges) | `RunOK.interval_bound` (Delay), with `tally` (Tally) |
| Lemma 3 | `worst_case_delay` (MainTheorems), `johnson_worst_case_delay` (Delay) |
| Corollary 2 (O((n + e)(c + 1)) total) | `total_time` (MainTheorems), `johnson_total_time` (Delay) |

## Working agreements with Frank
- No expensive tests or long runs without asking first; small smoke tests and tool installs are fine.
- Code in natural line width, no forced line breaks.
- Mark conjectures and unverified claims explicitly.
