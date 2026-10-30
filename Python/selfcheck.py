"""Self-check of johnson_traced.py: on random digraphs (s != t) its outputs equal, in order, those of a plain DFS
over simple paths and those of johnson_paths in ../../johnson.py (if that file is there); its search calls equal
those of johnson_paths without the calls of search(t); and its step count is at most (P + 1)(4n + 5m), P outputs."""
import os
import random
import sys

import networkx as nx

from johnson_traced import johnson_traced

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
try:
    from johnson import johnson_paths                    # the reference of the write-up, search(t) is a call there
except ImportError:
    johnson_paths = None


def simple_paths(G, s, t):
    """plain DFS over simple paths, successors in adjacency order"""
    S = []

    def dfs(v):
        S.append(v)
        for w in G.successors(v):
            if w == t:
                yield S + [t]
            elif w not in S:
                yield from dfs(w)
        S.pop()

    yield from dfs(s)


def johnson_calls(G, s, t):
    """the search calls of johnson_paths, as stacks, without the calls of search(t)"""
    calls = []
    stack = []
    blocked = {v: False for v in G.nodes}
    B = {v: set() for v in G.nodes}

    def unblock(u):
        blocked[u] = False
        while B[u]:
            w = B[u].pop()
            if blocked[w]:
                unblock(w)

    def search(v):
        if v != t:
            calls.append(tuple(stack) + (v,))
        found = False
        stack.append(v)
        if v == t:
            found = True
        else:
            blocked[v] = True
            for w in G.successors(v):
                if not blocked[w]:
                    if search(w):
                        found = True
        if found:
            unblock(v)
        else:
            for w in G.successors(v):
                B[w].add(v)
        stack.pop()
        return found

    search(s)
    return calls


def main():
    runs = paths = 0
    worst = 0.0
    for n in range(2, 10):
        for run in range(2000):
            rng = random.Random(1000 * n + run)
            p = rng.uniform(0, 1)
            G = nx.gnp_random_graph(n, p, directed=True, seed=rng)
            s, t = rng.sample(range(n), 2)
            trace = []
            steps = johnson_traced(G, s, t, trace.append)
            got = [list(e[2]) for e in trace if e[0] == "output"]
            assert got == list(simple_paths(G, s, t)), (s, t, sorted(G.edges))
            if johnson_paths is not None:
                assert got == [list(p) for p in johnson_paths(G, s, t)], (s, t, sorted(G.edges))
            stacks = []
            S = []
            for e in trace:
                if e[0] == "enter":
                    S.append(e[2])
                    stacks.append(tuple(S))
                elif e[0] == "exit":
                    S.pop()
            assert stacks == johnson_calls(G, s, t), (s, t, sorted(G.edges))
            obs = [e[1] for e in trace if e[0] in ("start", "output", "term")]
            bound = 4 * n + 5 * G.number_of_edges()
            for a, c in zip(obs, obs[1:]):
                assert c - a <= bound, (s, t, sorted(G.edges), a, c, bound)
                worst = max(worst, (c - a) / bound)
            runs += 1
            paths += len(got)
    ref = "johnson_paths and plain DFS" if johnson_paths is not None else "plain DFS (johnson.py not found)"
    print(f"{runs} random digraphs (n = 2..9), {paths} paths: same outputs as {ref}, same calls as johnson_paths; largest interval {worst:.2f} (4n + 5m)")


if __name__ == "__main__":
    main()
