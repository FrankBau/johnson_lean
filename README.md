# Johnson's Algorithm for Simple s-t Paths in Lean

Lean 4 code for Johnson's algorithm that enumerates all simple s-t paths of a directed graph, without a length bound: CIRCUIT
and UNBLOCK of D. B. Johnson, *Finding All the Elementary Circuits of a Directed Graph*, SIAM J. Comput. 4 (1975), with the target t
in place of the root s. Proved, for s ≠ t:

- **soundness** (`johnson_sound`, Johnson's Corollary 1): every output is a simple s-t path,
- **completeness** (`johnson_complete_once`, Johnson's Lemma 2): every simple s-t path is output exactly once,
- **the depth guards never fire** (`johnson_guards_vacuous`): the run is the run of Johnson's algorithm,
- **Johnson's Lemma 1** for the UNBLOCK chain (`lemma1`, internal).

Not yet proved: the worst-case delay (Johnson's Lemma 3), see [NOTES.md](NOTES.md).

Check for yourself, in this folder:

```bash
lake build                                       # checks all proofs; Main.lean checks the axioms of the theorems
lake env leanchecker --fresh Johnson.Complete    # replays everything again through the Lean kernel, from scratch (about 40 s)
./smoke_test.sh                                  # the Lean executable and Python/johnson_traced.py produce identical traces
python Python/selfcheck.py                       # johnson_traced.py against johnson.py and a plain DFS (needs networkx)
```

What you have to read and trust is `Johnson/Exec.lean` (about 150 lines, definitions only: `Graph`, `johnson`, `outputs`,
`Graph.SimplePath`) and the statements at the end of `Johnson/Complete.lean`.

[Lean Core](https://lean-lang.org/) version 4.34.1, no other libraries. Parts of the proof infrastructure (walks, the loop cursor
of `mvcgen`) are copied from the BS-DFS formalization, https://github.com/FrankBau/bsdfs_lean.
