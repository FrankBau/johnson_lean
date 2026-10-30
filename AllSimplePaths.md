# Johnson's Algorithm for All Simple Paths (no length bound)

This note describes Johnson's algorithm for enumerating all simple s-t paths of a directed graph, and sketches the proofs of soundness, completeness and worst-case delay. The algorithm is CIRCUIT and UNBLOCK of D. B. Johnson, *Finding All the Elementary Circuits of a Directed Graph*, SIAM J. Comput. 4 (1975), with a target t in place of the root s.

Every lemma and theorem below is proved in Lean in this repository, unless it is marked otherwise. The sketches follow the Lean proofs, and each section names the Lean theorems and their files (under `Johnson/`). Section 10 says where this differs from Johnson's own arguments.

## 1. The algorithm

```python
def johnson_paths(G, s, t):
    stack = []
    blocked = {v: False for v in G.nodes}
    B = {v: [] for v in G.nodes}

    def unblock(u):
        blocked[u] = False
        L, B[u] = B[u], []
        for w in L:
            if blocked[w]:
                unblock(w)

    def search(v):
        stack.append(v)
        blocked[v] = True
        found = False
        for w in G.successors(v):             # L1
            if w == t:
                yield stack + [t]
                found = True
            elif not blocked[w]:
                if (yield from search(w)):
                    found = True
        if found:                             # L2
            unblock(v)
        else:
            for w in G.successors(v):
                if v not in B[w]:
                    B[w].append(v)
        stack.pop()
        return found

    yield from search(s)
```

We assume s ≠ t. The graph has n nodes and m edges, m being the total length of the successor lists.

- `blocked[v]` is true while v is on the stack, and it stays true after a failed call until an UNBLOCK reaches v. There is no separate test for "w is on the stack".
- `B[w]` holds vertices that failed with w as a successor. They wait for w: when w is unblocked, they are unblocked too.
- The test `w == t` comes first, as `w = s` does in CIRCUIT. So t is never entered and never blocked, and the successors of t are never scanned. s stays on the stack until the end, so no edge into s is ever followed.

A **step** is a call of `search` or `unblock`, the output of one node of a path, or the scan of one list entry: a successor in L1, a successor in L2 (including the test `v not in B[w]`), or an entry of a B-list. Each step takes O(1) time, provided the test `v not in B[w]` does.

**The membership test.** A bit matrix would need n² bits, more than the O(n + m) space of section 9, and a hash set is O(1) only in expectation. A worst-case O(1) test with O(n + m) space uses a record per edge. Entries never leave a B-list one by one, because UNBLOCK always empties the whole list. So the record of the edge (v, w) can itself be the entry of v in B[w], with a next pointer and one bit for "on B[w]". L2 tests and sets the bit, and UNBLOCK clears it while it walks the list. Nothing is allocated during the run. This is an implementation note, not part of the Lean model: the code above and `Exec.lean` keep plain lists and count the test as one step. (Checked with a Python prototype on 12,000 random digraphs, not proved: the bit agreed with `v in B[w]` at every test, and the traces were those of `johnson_traced.py`.)

**The Lean model.** `Exec.lean` is a line-by-line transcription of `Python/johnson_traced.py`, which is this code with a step counter and an event trace. It differs in one point: Lean needs termination measures, so `search` carries its depth h and `unblock` a depth d, and the recursive calls are guarded by h + 1 < n and d + 1 < n. A failing guard would emit an `abort` event; `guards_vacuous` proves that this never happens. That Lean and Python produce the same traces is tested (1015 instances), not proved. The delay theorems count the step counter. The Lean program itself tests `v ∉ B[w]` by a linear scan, so they say nothing about its own running time.

**Results** (`MainTheorems.lean`, all for s ≠ t):

| Johnson 1975 | Statement | Lean | Needs |
|---|---|---|---|
| Corollary 1 | every output is a simple s-t path | `soundness` | |
| Lemma 2 | every simple s-t path is output exactly once | `completeness` | no duplicate edges |
| Lemma 3 | consecutive observable events (start, outputs, termination) are at most 4n + 5m steps apart | `worst_case_delay` | |
| Corollary 2 | the τ-th observable event happens after at most τ(4n + 5m) steps | `total_time` | |
| | the depth guards never fire | `guards_vacuous` | |

## 2. Notation

- A stack is a list, bottom first. S·v is S with v on top. L·x is a prefix of S if S starts with L followed by x.
- `Reach(X, x)` says: there is a walk x = x₀, x₁, …, x_l = t in G with x₁, …, x_l ∉ X. The start x itself is exempt, so Reach(S, v) makes sense for a vertex v just above the stack S. (`Graph.Reach`, Paths)
- Three facts about Reach. If X ⊆ Y, then Reach(Y, x) implies Reach(X, x) (`Reach.mono`). If y is a successor of x, y ∉ X and Reach(X, y), then Reach(X, x) (`Reach.step`). A walk contains a simple path with the same ends whose nodes after x avoid the same set (`Walk.path`).
- A **stack path** is a list that starts with s, has no repeated vertex, does not contain t, and whose consecutive vertices are edges (`StackPath`, Paths).

## 3. The invariant

For the stack S, the blocked flags and the B-lists, between steps (`Inv`, Invariant):

| | Clause | Lean field |
|---|---|---|
| (A) | every vertex on S is blocked | `stack` |
| (T) | t is not blocked | `target` |
| (B) | a blocked vertex x off S is on B[w], for every successor w of x | `reg` |
| (D) | if x ∈ B[w], then w is a successor of x | `edge` |
| (E) | if x ∈ B[w] and L·x is a prefix of S, then w ∈ L·x, or w ∉ S and not Reach(L·x, w) | `stale` |
| (F) | if B[w] is nonempty, then w is blocked | `wait` |
| (N) | no B-list has a repeated vertex | `nodup` |

**Lemma A** (`Inv.dead`; Johnson's Lemma 1 (ii)). A blocked vertex x off S cannot reach t avoiding S: not Reach(S, x).

*Sketch.* Take a walk x, x₁, …, t with x₁, … ∉ S. By (B), x ∈ B[x₁], so x₁ is blocked by (F). As x₁ is off S, the same argument applies to x₁, and so on along the walk. So t is blocked, against (T).

**(E) is about stale entries.** UNBLOCK(u) empties only B[u]. A vertex x unblocked through one B-list stays on the B-lists of its other successors, and it can be back on the stack while such an entry exists. An example, with successor lists s: u, x; u: x, t; x: u, w; w: none. Under the stack s u, x fails, because u is on the stack and w is a dead end, so x goes on B[u] and B[w]. After the output s u t, UNBLOCK(u) unblocks x through B[u], but x stays on B[w]. Then s calls x, and x is on the stack with an entry in B[w]. If UNBLOCK(w) ran now, it would unblock a vertex on the stack and soundness would be lost. (E) rules this out: w cannot reach t avoiding the stack up to x, while everything that UNBLOCK reaches can (section 4).

The invariant is kept by the three changes of the stack.

**Entering v** (`Inv.push`), with v unblocked, v ∉ S, v ≠ t. The stack becomes S·v and v gets blocked; the B-lists stay. All clauses but (E) are immediate. For (E), let x ∈ B[w] and let L·x be a prefix of S·v. By (F), w is blocked, so w ≠ v. If L·x is a prefix of S, the old (E) applies, and w ≠ v keeps w off the longer stack. Otherwise x = v and L = S: this is a stale entry of v itself. If w ∈ S, the first alternative holds. If not, w is blocked and off S, so not Reach(S, w) by Lemma A, hence not Reach(S·v, w).

**Failed return of v** (`Inv.fail`), from the stack S·v, with v ∉ S and every successor of v blocked (section 5). v goes on B[w] for each successor w, then the stack becomes S. (A), (T) and (D) are immediate, and (N) holds because v is appended only if absent. (B) holds for v because it was just registered, and for the others because entries stay. (F) holds for the new entries because the successors of v are blocked. (E): if L·x is a prefix of S, then x ≠ v, so the entry is old, and L·x is also a prefix of S·v.

**Fruitful return of v**: section 4.

## 4. UNBLOCK and Lemma 1

Let v return with `found` true, from the stack S·v. The invariant holds for S·v. v made an output, which continues S·v by a simple path to t, so Reach(S, v) (`loop_upre`, Complete).

**Chain lemma** (`unblock_spec`, `ChainPost`; Unblock, Invariant). UNBLOCK(v) has this effect:

1. Nothing gets blocked, and v gets unblocked (`mono`, `top`).
2. Every other vertex it unblocks is off S·v and has Reach(S, ·) (`off`). So no vertex of S gets unblocked.
3. If it unblocks u, then every vertex on the old B[u] is unblocked afterwards (`closed`).
4. The B-lists of the vertices it unblocks are empty, and the others are unchanged (`cleared`, `kept`).

*Sketch.* Induction over the nested calls, by a spec of `unblock u d` relative to the state at its call. Precondition: u is blocked; u = v, or u is off S·v with Reach(S, u); v is unblocked unless u = v; and (T), (D), (E), (F), (N) hold (`UPre`). The call unblocks u and empties B[u], which keeps those clauses, then goes through the old list. Entries that are already unblocked need nothing. A blocked entry w gets a nested call, and its precondition holds (`child_pos`):

- w ≠ v, since v is unblocked by now.
- Reach(S, w): by (D), u is a successor of w; u ∉ S; and Reach(S, u).
- w ∉ S. Suppose w ∈ S, so that L·w is a prefix of S. Apply (E) to the entry w ∈ B[u]. Either u ∈ L·w, which contradicts u ∉ S, or not Reach(L·w, u), which contradicts Reach(S, u), because L·w ⊆ S.

A vertex that is not yet unblocked still has its B-list, because only its own `unblock` changes it (`kept`). After the loop all entries of the old list are unblocked, and they stay so, as nothing gets blocked. This gives 3.

The depth guard: at a nested call from `unblock u d`, the d + 1 vertices of the open calls are distinct and unblocked, and the next vertex is blocked, so together they have no repetition and d + 2 ≤ n (`UPre.deep`, `UPre.depth`).

**The invariant after the return** (`Inv.chain`), for the stack S. (A) holds by 2. (T) holds by 1. (B): let x still be blocked and off S. Then x ≠ v, and x was blocked before, so x was on B[w] for every successor w. If the chain had unblocked w, then x would be unblocked by 3. So B[w] is unchanged by 4, and x is still on it. (D), (E), (N): B-lists only lost entries, and a prefix of S is also a prefix of S·v. (F): a nonempty B-list belongs to a vertex that stayed blocked.

**Lemma 1** (`lemma1`, Complete). Let x be blocked at L2 of v and off S·v. Then:

- UNBLOCK(v) unblocks x if and only if Reach(S, x);
- not Reach(S·v, x). So every walk from x to t that avoids S passes through v.

*Sketch.* If x gets unblocked, Reach(S, x) by 2. If x stays blocked, the invariant holds for S afterwards and Lemma A gives not Reach(S, x). The last claim is Lemma A for S·v.

In Johnson's words, Reach(S, x) is condition (i), a path through v on which only v is on the stack, and the second claim is condition (ii). So UNBLOCK is neither too weak nor too strong: it frees exactly the blocked vertices whose way to t depends on v. At a failed return nothing gets unblocked, and by the invariant for S together with Lemma A, no blocked vertex off S has Reach(S, ·), so no vertex is missed there either. (This failed case is not a separate Lean theorem, it is `Inv.fail` with `Inv.dead`.)

## 5. The search

**Spec of a call** (`search_spec`, Complete; induction on n - h). Let `search(v)` be called with stack S, where S·v is a stack path, v is unblocked, and the invariant holds for S. When it returns, the stack is S again, and with N the outputs of this call:

- every path in N is a simple s-t path that starts with S·v (`sound`);
- every simple s-t path that starts with S·v is in N (`complete`, Call Completeness);
- it returns true if and only if N is nonempty (`ret`);
- the invariant holds for S (`inv`);
- if it returns false, nothing was unblocked during the call, and v is blocked (`fail`);
- if G has no duplicate edges, N has no repetitions (`nodup`).

*Sketch.* Entering v gives the invariant for S·v (`Inv.push`). The loop keeps, after the scanned successors (`LoopInv`): the invariant for S·v; the first three clauses above for the scanned successors; and, while `found` is false, that nothing was unblocked since the entry and that all scanned successors are blocked. One scan of a successor w:

- **w = t** (`loop_output`). The output is S·v·t. It is the only simple path that starts with S·v·t, as t is its last vertex.
- **w blocked** (`loop_blocked`). If w ∈ S·v, no simple path starts with S·v·w. If not, the rest of such a path would be a walk from w avoiding S·v, against Lemma A. So nothing is missed.
- **w unblocked** (`loop_child_pre`, `loop_child_post`). By (A), w ∉ S·v, so S·v·w is a stack path and the guard h + 1 < n holds. The spec of the recursive call applies. If it returns false, nothing was unblocked and w is blocked, so the clause for `found` false survives.

At the end of the loop every simple path that starts with S·v is covered, because it continues with some successor of v (`LoopInv.complete'`). If `found` is true, section 4 gives the invariant for S (`post_found`). If not, nothing was unblocked since the entry and all successors are blocked, so `Inv.fail` applies (`post_fail`, with the loop invariant `FailInv`).

The root call has empty stack, nothing blocked and empty B-lists, where the invariant is trivial (`root_pre`).

## 6. Corollary 1: only simple paths

**Theorem** (`johnson_sound`, Complete). Every output is a simple s-t path.

*Sketch.* An output is S·v·t, where S·v is the stack. The stack is a stack path: when `search(w)` is called, w is a successor of v, w ≠ t by the first test, and w ∉ S·v by (A), since w is unblocked. t ∉ S·v, so S·v·t has no repetition.

This is where Johnson's algorithm needs its invariant: BS-DFS tests `w not in S` explicitly, here (A) does that job, and (A) rests on the chain lemma. The same fact gives the guard of `search`: S·v·w has no repetition, so h + 2 ≤ n. With the guard of `unblock` (section 4), no `abort` is ever emitted (`johnson_guards_vacuous`, Complete).

## 7. Lemma 2: every path exactly once

**Theorem** (`johnson_complete_once`, Complete). If G has no duplicate edges, every simple s-t path is output exactly once.

*Sketch.* Every simple s-t path starts with s, so Call Completeness of the root call puts it into the outputs. No path is output twice: the outputs of different successors of v differ at the position after v, and the successors of v are distinct. The hypothesis is needed: a successor listed twice would be searched again after a fruitful return, and its paths would be output again.

## 8. Lemma 3: worst-case delay

**Theorem** (`johnson_worst_case_delay`, Delay). Consecutive observable events (start, outputs, termination) are at most 4n + 5m steps apart.

Positions are indices into the event list of the run. The events are `enter`, `output`, `unblock`, `exit`, and `start` and `term` at the ends (`Exec.lean`). The stack and the blocked flags at a position are replays of the events before it (`stk`, `blk`, Trace). A **frame** (e, x) is a call, entered at position e and exited at x. An **interval** (a, c] lies between two consecutive observable events at positions a and c.

**Steps against charges** (`tally`, Tally). Charge every event as follows:

| Event | Charge |
|---|---|
| entry of v | 1 + outdeg(v) (the entry and all its L1 scans, in advance) |
| failed exit of v | outdeg(v) (the L2 scans) |
| unblock of u with list L | 1 + len(L) |
| output P | len(P) |

A call spends exactly what its events are charged (`search_cost`, `unblock_cost`). At an observable event only the open frames are behind: they still owe their remaining L1 scans, at most outdeg per frame. So the steps in (a, c] are at most the charges in (a, c] plus the out-degrees of the stack at a.

**Facts about the run** (`RunOK`, RunFacts). These hold at every position, proved by the specs of sections 4 and 5 extended with the trace (`unblock_spec_tr`, `search_spec_tr`, `johnson_runOK`; RunSearch):

- An entered vertex is unblocked before its entry, is off the stack, and extends the stack to a stack path.
- An output is the stack followed by t, without repetition, and the stack is blocked at that moment.
- The vertex u of an unblock event is blocked before it, is not on the stack below the top, and has Reach(stack below the top, u). Its list L has no repetition and holds predecessors of u.
- Every entry and every exit has its frame. A frame exits with `found` true if and only if it contains an output. Call Completeness holds per frame.
- An unblock event belongs to the chain of the top frame: that frame exits with `found` true, and from the event up to its exit there are only unblock events (`ChainAt`).
- `start` is at position 0, and the stack is empty at `term`.

**Chains belong to old frames** (`chain_open`). An unblock event in (a, c] belongs to a frame entered before a. The frame exits fruitful, so it contains an output. The output lies before the event, because from the event on the frame has only unblock events. It is not strictly inside (a, c), so it is at a or earlier, and the frame was entered before it.

**Part 1: no vertex is unblocked twice in an interval** (`unblock_twice`, `unblock_once`). Suppose u is unblocked at q₁ < q₃ in (a, c].

1. u is unblocked right after q₁ and blocked before q₃, so u is entered at some q₂ between them.
2. At q₁, u has Reach(S₁, u), and u ∉ S₁, where S₁ is the stack below the top. Take a simple path W from u to t that avoids S₁. The chain of q₁ runs to the exit of the top frame, which pops the top, so the stack is S₁ right after that exit. q₂ comes after it.
3. Take the first position q after that exit where a vertex z of W is entered; q ≤ q₂, since u is on W. No vertex of W is on the stack at q: they were off it after the exit, and none has been entered since.
4. So the stack at q, followed by the part of W from z on, is a simple s-t path, and it starts with the stack of the frame of z. By Call Completeness that frame outputs it.
5. That frame closes before q₃. By `chain_open`, the chain of q₃ belongs to a frame F entered before a, so F is open at q. F is the top frame at q₃, so the frame of z, entered inside F, has closed by then.
6. So an output lies strictly inside (a, c). Contradiction.

u itself may be entered while the frame of z is open, and it may even fail there. The argument does not depend on that.

**Entries** (`balance`, `enter_le`). The blocked flag of z goes from false to true only at an entry of z, and from true to false only at an unblock of z. So in (a, c], with E entries and U unblocks of z, we have E + [z blocked after a] = U + [z blocked after c]. With U ≤ 1 this gives E + [z blocked after a] ≤ 2. A vertex on the stack at a is blocked there, so it has at most one entry.

**Failed exits** (`fail_le`). A failed exit in (a, c] closes a frame entered in (a, c]. A frame entered before a would contain position a, which would have to be an output (`obs_in_frame`), and that frame would be fruitful. So failed exits of z ≤ entries of z.

**B-lists** (`length_le_indeg`, `Graph.indeg_sum`). A list L at an unblock of u has no repetition and holds predecessors of u, so len(L) ≤ indeg(u). The in-degrees sum to at most m.

**Part 2: the sum** (`vertex_bound`, `interval_bound`). Fix z, with d = outdeg(z), i = indeg(z), and S = 1 if z is on the stack at a, else 0. Then E ≤ 2, E + S ≤ 2, F ≤ E, U ≤ 1, and its charges plus what it owes at a are

(1 + d)·E + d·F + (1 + i)·U + d·S ≤ 3 + 4d + i.

The sum over all z is at most 3n + 4m + m. Only the event at c can be an output, of at most n nodes (`out_le`). In total 4n + 5m.

Per vertex this is 2 entries and 1 unblock. Per edge (x, y) it is at most 2 scans in L1 (x entered, or on the stack at a), at most 2 scans in L2, and 1 pop of x from B[y]. No hypothesis on G is needed.

**Example: an edge with 5 charges.** Successor lists s: v, u; v: u, x; u: v, t; x: v. Between the outputs s v u t and s u t, x is entered under v and fails; UNBLOCK(v) unblocks x; then x is entered again with the stack s u v, and fails again. The edge (x, v) gets 2 scans in L1, 2 scans in L2 and 1 pop. (This was checked by running it; it shows that the count per edge is reached, not the total.) On 16,000 random digraphs with n ≤ 9, the largest interval was 0.66 (4n + 5m) (measured by `Python/selfcheck.py`, not a theorem).

## 9. Corollary 2: total time

**Theorem** (`johnson_total_time`, Delay). The τ-th observable event happens after at most τ(4n + 5m) steps.

*Sketch.* The first observable event has stamp 0 (`johnson_head`); the rest is Lemma 3, summed. With P outputs the run takes at most (P + 1)(4n + 5m) steps. The space is O(n + m) plus the output: by (D) and (N) the B-lists hold at most m entries at any moment, and the stack at most n vertices. (The space bound follows directly from the invariant, but it is not stated as a theorem.)

## 10. Relation to Johnson 1975

**The algorithm.** Johnson runs CIRCUIT from each root s, on a strong component, and closes a circuit by `w = s`. Here there is one call with a target t, and no strong components. Simple s-t paths also correspond one-to-one to the elementary circuits through s in G minus the in-edges of s, minus the out-edges of t, plus the edge (t, s). (This reduction is not formalized.) With s = t the code is CIRCUIT(s) on the whole graph, but the theorems assume s ≠ t.

**UNBLOCK.** Johnson's UNBLOCK deletes each entry from B(u) just before handling it, as `johnson.py` does. The code here empties B[u] first and walks the old list. The two do the same work. While UNBLOCK(u) walks its list, only nested UNBLOCK calls run, and they leave B(u) alone: no `search` returns, so nothing is added to a B-list, and UNBLOCK(u) is not called again, because u is unblocked from its first statement on and nothing gets blocked during a chain. So only the walk itself reads the rest of the list. Taken front to back, both forms make the same nested calls at 1 + |B(u)| steps. This is an argument, not a Lean theorem: `Exec.lean` has only the form above, so the theorems reach Johnson's form through this argument. (Checked with a Python version of his form on 12,000 random digraphs, half of them with self-loops added: the traces, step counts included, were those of `johnson_traced.py`.) The form here also keeps (F) true at every nested call. In his form u is unblocked with a nonempty B(u) during those calls, so (F) would need an exception.

**The proofs.** The two parts of Lemma 3 and the use of Lemma 1 in Lemma 2 are Johnson's. Different are:

- **Lemma 1.** Johnson argues by contradiction at the earliest L2 where the lemma fails. Here it follows from an invariant kept by every step. His condition (ii) becomes Lemma A, which holds between all steps, not only at L2. That is what the proof of Lemma 2 needs, because a blocked successor is met during L1.
- **Stale entries.** Clause (E) has no counterpart in the paper. As we read it, Case 2 of his proof does not spell out why a stale entry never unblocks a vertex on the stack. This is a reading of the paper, not a formal statement. That the formal proof needs (E) does not show that his argument is wrong.
- **Lemma 3, Part 1.** Johnson says that no vertex on the path is unstacked until the next output. As we read it, this holds for the part of the path from the first re-entered vertex on, but not for the vertices before it, which may be entered and fail in between. That includes u itself, as in the example of section 8. The formal argument instead locates the second chain in a frame entered before the interval (`chain_open`) and lets the frame of z close before it.
- **Lemma 3, Part 2.** Johnson charges a unit per vertex passed to a call, and a unit per edge considered in L1 without a call, and bounds all other work by "a constant times the number of units". Hence his "each edge at most twice". Here every step is counted, including the L2 scans and the B-list pops, which gives the explicit 3 per vertex and 5 per edge. The paper does not say how the test `v ∉ B(w)` is done in constant time.
