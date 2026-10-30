#!/usr/bin/python3

# Generates cases.txt (graphs as index-based succ lists in NetworkX scan order) and expected.txt (johnson_traced events, nodes as indices)
import random
import networkx as nx
from johnson_traced import johnson_traced

def ladder(r):
    """stride-2 ladder: s->v1->...->vr->t, s->t, vr->x1->...->x2r (x1 scanned before t), x(2r-2j)->v(r-j) for j = 0..r-1"""
    G = nx.DiGraph()
    v = [f"v{i}" for i in range(1, r + 1)]
    x = [f"x{i}" for i in range(1, 2 * r + 1)]
    G.add_edges_from([("s", v[0])] + list(zip(v, v[1:])) + [("s", "t"), (v[-1], x[0])] + list(zip(x, x[1:])) + [(v[-1], "t")])
    G.add_edges_from((x[2 * r - 2 * j - 1], v[r - j - 1]) for j in range(r))
    return G

def dead_clique(c):
    """s->x1, x1..xc pairwise joined, no exit, s->t"""
    G = nx.DiGraph()
    G.add_edge("s", "x1")
    G.add_edges_from((f"x{i}", f"x{j}") for i in range(1, c + 1) for j in range(1, c + 1) if i != j)
    G.add_edge("s", "t")
    return G

def cases():
    Z = nx.parse_adjlist(['s a d', 'a c t', 'b a', 'c b z', 'd t z', 'z b c', 't'], create_using=nx.DiGraph)
    yield 'Z', Z, 's', 't'
    Y = nx.parse_adjlist(["A D", "B D E F", "C", "D A B C", "E A B D", "F B"], create_using=nx.DiGraph)
    yield 'Y', Y, 'E', 'C'
    Y2 = nx.DiGraph()
    Y2.add_edges_from([(0, 1), (0, 2), (1, 0), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (2, 5), (3, 1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (5, 1)])
    yield 'Y2', Y2, 4, 5
    for c in range(3, 7):
        yield f'K{c}', nx.complete_graph(c, create_using=nx.DiGraph), 0, c - 1
    for r in range(1, 5):
        yield f'L{r}', ladder(r), 's', 't'
    for c in range(2, 6):
        yield f'D{c}', dead_clique(c), 's', 't'
    for run in range(1000):
        random.seed(42 + run)                      # the path-mode instances of the BS-DFS smoke test
        n = random.randint(2, 9)
        p = random.uniform(0, 1)
        random.getrandbits(n)                      # BS-DFS draws its length bound here
        G = nx.gnp_random_graph(n, p, directed=True, seed=run)
        s, t = random.sample(range(n), 2)
        yield f'R{run}', G, s, t

def main():
    ncases = nevents = nout = 0
    with open('cases.txt', 'w') as fc, open('expected.txt', 'w') as fe:
        for name, G, s, t in cases():
            idx = {v: i for i, v in enumerate(G.nodes)}
            n = len(idx)
            print(f"case {name} {n} {idx[s]} {idx[t]}", file=fc)
            for v in G.nodes:
                print(" ".join(str(idx[w]) for w in G.successors(v)), file=fc)
            trace = []
            johnson_traced(G, s, t, trace.append)
            print(f"case {name}", file=fe)
            for ev in trace:
                if ev[0] == 'output':
                    ev = (ev[0], ev[1], tuple(idx[x] for x in ev[2]))
                    nout += 1
                elif ev[0] == 'unblock':
                    ev = (ev[0], ev[1], idx[ev[2]], tuple(idx[x] for x in ev[3]))
                elif ev[0] not in ('start', 'term'):
                    ev = (ev[0], ev[1], idx[ev[2]]) + ev[3:]
                print(repr(ev), file=fe)
                nevents += 1
            ncases += 1
    print(f"{ncases} cases, {nevents} events, {nout} outputs")

main()
