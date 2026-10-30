# Johnson's Algorithm for Simple s-t Paths in Lean

Lean 4 code for Johnson's algorithm that enumerates all simple s-t paths of a directed graph, without a length bound: CIRCUIT
and UNBLOCK of D. B. Johnson, *Finding All the Elementary Circuits of a Directed Graph*, SIAM J. Comput. 4 (1975), with the target t
in place of the root s. Proved, for s ≠ t:

- **soundness** (Johnson's Corollary 1): every output is a simple s-t path,
- **completeness** (Johnson's Lemma 2): every simple s-t path is output exactly once,
- **worst-case delay** (Johnson's Lemma 3): consecutive observable events (start, outputs, termination) are at most 4n + 5m steps
  apart, n nodes, m edges,
- **total time** (Johnson's Corollary 2): the τ-th observable event happens after at most τ(4n + 5m) steps,
- **the depth guards never fire**: the Lean function needs them for termination, but the run is the run of Johnson's algorithm.

A **step** is a node visit (a call of search or of UNBLOCK), the output of one node of a path, or the scan of one list entry
(a successor, a successor rescanned at a failed return, an entry of a B-list). Each step can be executed in O(1) time, given an
O(1) test `v ∈ B[w]`.

Check for yourself, in this folder:

```bash
lake build                                            # checks all proofs; fails if a main theorem uses sorry or a non-standard axiom
lake build Johnson.Challenge                          # the statements alone, with sorry
lake env lean --run CheckChallenge.lean               # Challenge.lean and MainTheorems.lean state the same theorems on the same definitions
lake env leanchecker --fresh Johnson.MainTheorems     # replays everything through the Lean kernel, from scratch (about 40 s)
./smoke_test.sh                                       # the Lean executable and Python/johnson_traced.py produce identical traces
python Python/selfcheck.py                            # johnson_traced.py against johnson.py and a plain DFS (needs networkx)
```

What you have to read and trust is `Johnson/Challenge.lean`, which states the main theorems with `sorry`, and its import
`Johnson/Exec.lean` (about 150 lines, definitions only: `Graph`, `johnson`, `outputs`, `obsSteps`, `Graph.SimplePath`).
`Johnson/MainTheorems.lean` proves the same statements under the same names, each with its axiom check.

[Lean Core](https://lean-lang.org/) version 4.34.1, no other libraries. Parts of the proof infrastructure (walks, the loop cursor
of `mvcgen`, the trace replays, the tally and the sums) are adapted from the BS-DFS formalization,
https://github.com/FrankBau/bsdfs_lean. Details about the code are in [NOTES.md](NOTES.md).
