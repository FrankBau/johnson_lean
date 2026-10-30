"""Johnson's algorithm for simple s-t paths (no length bound) -- reference implementation with event callback.

The algorithm is CIRCUIT and UNBLOCK of Johnson (1975) with the target t in place of the root s: the closing edge
(v, t) is tested inline, before the blocked test, as `w = s` is in CIRCUIT.  It makes the same search calls and
the same outputs as johnson_paths in johnson.py, which calls search(t) instead.  The B-lists are Python lists,
so that UNBLOCK pops them in a fixed order (johnson.py pops a set in hash order).  Instrumentation is one
`emit(...)` call per event and one `steps += ...` per cost-model site.  Pass `emit=list.append` of a list to
record a trace.

Cost model, counted at exactly these sites:
    search call at v    : 1 (entry) + 1 per scanned successor (L1)
    producing an output : |path|
    failed return at v  : 1 per successor (L2: the test v in B[w], counted as one step, and the insertion)
    unblock call at u   : 1 (the call) + 1 per entry of B[u]

Event schema -- every event carries the step counter *after* the step it represents:

    ('start',   0)                   o_0, before any step
    ('enter',   step, v, h)          after the entry step, h = |S| - 1
    ('output',  step, path)          o_tau, path as a tuple
    ('unblock', step, u, L)          after the call step; L = B[u] at the call, as a tuple, and B[u] is emptied
    ('exit',    step, v, found)      before the pop
    ('term',    step)                o_{T+1}, after the last step

The Lean transcription has a seventh event, ('abort', step), emitted only by the depth guards that Lean needs
for termination; they never fire.
"""


def johnson_traced(G, s, t, emit):
    """Emits events; returns the total step count."""
    blocked = {x: False for x in G.nodes}
    B = {x: [] for x in G.nodes}
    S = []
    steps = 0

    def unblock(u):
        nonlocal steps
        blocked[u] = False
        steps += 1                                                  # instr
        L = B[u]
        B[u] = []
        emit(("unblock", steps, u, tuple(L)))                      # instr
        for w in L:
            steps += 1                                              # instr
            if blocked[w]:
                unblock(w)

    def search(v):
        nonlocal steps
        S.append(v)
        h = len(S) - 1
        blocked[v] = True
        steps += 1                                                  # instr
        emit(("enter", steps, v, h))                                # instr
        found = False
        for w in G.successors(v):
            steps += 1                                              # instr
            if w == t:
                steps += h + 2                                      # instr
                emit(("output", steps, tuple(S) + (t,)))
                found = True
            elif not blocked[w]:
                if search(w):
                    found = True
        if found:
            unblock(v)
        else:
            for w in G.successors(v):
                steps += 1                                          # instr
                if v not in B[w]:
                    B[w].append(v)
        emit(("exit", steps, v, found))                             # instr
        S.pop()
        return found

    emit(("start", steps))
    search(s)
    emit(("term", steps))
    return steps


if __name__ == "__main__":
    import networkx as nx

    # graph Z of the BS-DFS smoke test
    Z = nx.parse_adjlist(['s a d', 'a c t', 'b a', 'c b z', 'd t z', 'z b c', 't'], create_using=nx.DiGraph)
    trace = []
    steps = johnson_traced(Z, 's', 't', trace.append)
    print(f"graph edges: {list(Z.edges)}")
    for event in trace:
        print(event)
    print(f"steps: {steps}")
