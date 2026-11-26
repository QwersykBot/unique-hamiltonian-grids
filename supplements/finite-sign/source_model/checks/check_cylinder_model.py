#!/usr/bin/env python3
"""Bounded, stdlib-only cylinder audit; never an all-width proof.

Expected data were read from the primary 2015 paper, printed pp. 231--232;
B4 was read on pp. 226--227.  Ordinary, initial, and final transitions below
are derived by graph gluing and connected components, not reconnection rules.
The independent whole-cylinder oracle enumerates vertex paths, then computes
the B words directly from positive-window connected components.

Run: python3 checks/check_cylinder_model.py
The deterministic JSON report is printed on standard output.
"""

if not __debug__:
    raise SystemExit(
        "Verification requires assertions. Rerun without -O/-OO and unset PYTHONOPTIMIZE."
    )

from collections import deque
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json


PAPER = "https://dmtcs.episciences.org/en/articles/2113/download"
EXPECTED = {
    3: {
        "words": ["220", "202", "022", "002", "020", "200"],
        "matrix": [
            [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 1],
            [0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0],
            [1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 0],
        ],
        "F": [1, 2, 3], "Lc": [1, 2, 3], "Lnc": [4, 5, 6],
        "orbit_reps": ["220", "002"],
        "quotient": [[0, 2], [2, 0]],
    },
    4: {
        "words": ["2220", "2202", "2022", "2030", "0222", "0203",
                  "0002", "0020", "0200", "2000", "2020", "0202"],
        "matrix": [
            [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0],
            [0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1],
            [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0],
            [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1],
            [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
            [0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0],
            [1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
            [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
            [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0],
            [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1],
        ],
        "F": [1, 2, 3, 4, 5, 6],
        "Lc": [1, 2, 3, 5, 11, 12], "Lnc": [4, 6, 7, 8, 9, 10],
        "orbit_reps": ["2220", "2030", "0002", "2020"],
        "quotient": [[0, 0, 3, 1], [2, 1, 0, 0],
                     [3, 1, 0, 0], [0, 0, 2, 1]],
    },
}


def components(vertices, edges):
    """Ordinary undirected multigraph traversal; parallel edges are retained."""
    adjacent = {v: [] for v in vertices}
    for u, v in edges:
        adjacent[u].append(v)
        adjacent[v].append(u)
    unseen, answer = set(adjacent), []
    while unseen:
        seed = min(unseen)
        found, stack = {seed}, [seed]
        unseen.remove(seed)
        while stack:
            for v in adjacent[stack.pop()]:
                if v in unseen:
                    unseen.remove(v)
                    found.add(v)
                    stack.append(v)
        answer.append(found)
    return answer


@lru_cache(None)
def matchings(ports):
    if not ports:
        return ((),)
    return tuple(tuple(sorted(((ports[0], ports[k]),) + p + q))
                 for k in range(1, len(ports), 2)
                 for p in matchings(ports[1:k])
                 for q in matchings(ports[k + 1:]))


def support(m, state):
    pairing, shade = state
    active = {i for pair in pairing for i in pair}
    answer, color = [], shade
    for i in range(m):
        color ^= int(i in active)
        answer.append(color)
    assert color == shade
    return tuple(answer)


def canonical(word):
    labels, result = {}, []
    for x in word:
        if x and x not in labels:
            labels[x] = len(labels) + 2
        result.append(labels[x] if x else 0)
    return tuple(result)


def b_word(m, state):
    """Reconstruct labels only by components of P union run-endpoint S."""
    pairing, _ = state
    a = support(m, state)
    runs = []
    for s in range(m):
        if a[s] and not a[s - 1]:
            positions, t = [], s
            while a[t]:
                positions.append(t)
                t = (t + 1) % m
            runs.append((s, t, positions))
    ports = {i for pair in pairing for i in pair}
    cc = components(ports, list(pairing) + [(s, t) for s, t, _ in runs])
    owner = {v: k + 2 for k, part in enumerate(cc) for v in part}
    word = [0] * m
    for s, _, positions in runs:
        for i in positions:
            word[i] = owner[s]
    return canonical(word)


def glue(m, pairing, vertical, close=False):
    """Glue contracted prefix paths to actual column vertices and stubs.

    The column has vertices i, incoming stub vertices m+i, outgoing leaves
    2m+i.  All current vertices must have degree two.  A nonfinal component
    with no outgoing leaves is a premature cycle and is rejected.
    """
    active = {i for pair in pairing for i in pair}
    outgoing = tuple(2 - int(i in active) - vertical[i - 1] - vertical[i]
                     for i in range(m))
    if any(y not in (0, 1) for y in outgoing):
        return None
    if bool(any(outgoing)) == close:
        return None
    vertices = set(range(m)) | {m + i for i in active}
    edges = [(m + i, m + j) for i, j in pairing]
    edges += [(m + i, i) for i in active]
    edges += [(i, (i + 1) % m) for i in range(m) if vertical[i]]
    leaves = {2 * m + i for i in range(m) if outgoing[i]}
    vertices |= leaves
    edges += [(i, 2 * m + i) for i in range(m) if outgoing[i]]
    cc = components(vertices, edges)
    if close:
        return () if len(cc) == 1 else None
    result = []
    for part in cc:
        ends = sorted(part & leaves)
        if len(ends) != 2:
            return None
        result.append(tuple(v - 2 * m for v in ends))
    return tuple(sorted(result))


def reach(seeds, graph):
    found, queue = set(seeds), deque(sorted(seeds))
    while queue:
        for v in graph[queue.popleft()]:
            if v not in found:
                found.add(v)
                queue.append(v)
    return found


def model(m):
    formal = {(p, c) for k in range(2, m + 1, 2)
              for ports in combinations(range(m), k)
              for p in matchings(ports) for c in (0, 1)}
    words = {state: b_word(m, state) for state in formal}
    assert len(set(words.values())) == len(formal), ("B injectivity", m)
    choices = list(product((0, 1), repeat=m))
    first, graph, terminal = set(), {}, [set(), set()]
    for z in choices:
        p = glue(m, (), z)
        if p is not None:
            first.add((p, z[-1]))
    assert first <= formal
    for state in sorted(formal):
        p, c = state
        a = support(m, state)
        graph[state] = {}
        for z in choices:
            q = glue(m, p, z)
            if q is not None:
                target = (q, c ^ z[-1])
                assert target in formal, ("noncrossing closure", m, state, z)
                assert target not in graph[state], ("parallel B edge", m)
                assert support(m, target) == tuple(a[i] ^ z[i] for i in range(m))
                graph[state][target] = z
        for cap in (0, 1):
            if glue(m, p, tuple(v ^ cap for v in a), close=True) is not None:
                terminal[cap].add(state)
        word = words[state]
        b4c = (set(word) == {0, 2}
               and all(a[i - 1] or a[i] for i in range(m)))
        b4nc = (all(not (a[i - 1] and a[i]) for i in range(m))
                and len({v for v in word if v}) == sum(a))
        assert b4c == (state in terminal[0]), ("B4c", m, word)
        assert b4nc == (state in terminal[1]), ("B4nc", m, word)
    reverse = {s: set() for s in formal}
    for s in formal:
        for t in graph[s]:
            reverse[t].add(s)
    actual = reach(first, graph) & reach(terminal[0] | terminal[1], reverse)
    graph = {s: {t: z for t, z in graph[s].items() if t in actual}
             for s in actual}
    return {"m": m, "formal": formal, "actual": actual,
            "words": {s: words[s] for s in actual}, "graph": graph,
            "F": first & actual, "Lc": terminal[0] & actual,
            "Lnc": terminal[1] & actual}


def symmetries(word):
    for base in (word, tuple(reversed(word))):
        for k in range(len(word)):
            yield canonical(base[k:] + base[:k])


def audit_model(data):
    m, actual, words, graph = (data[k] for k in ("m", "actual", "words", "graph"))
    by_word = {w: s for s, w in words.items()}
    J = {s: (s[0], 1 - s[1]) for s in actual}
    assert set(J.values()) == actual
    assert all(J[J[s]] == s for s in actual)
    assert {J[s] for s in data["Lc"]} == data["Lnc"]
    for s in actual:
        assert {J[t]: z for t, z in graph[s].items()} == graph[J[s]]
        for gword, gjword in zip(symmetries(words[s]), symmetries(words[J[s]])):
            assert gword in by_word
            assert words[J[by_word[gword]]] == gjword, ("dihedral J", m)
    orbit_key = {s: min(symmetries(words[s])) for s in actual}
    keys = sorted(set(orbit_key.values()))
    if m in EXPECTED:
        keys = [orbit_key[by_word[tuple(map(int, w))]]
                for w in EXPECTED[m]["orbit_reps"]]
    assert len(keys) == len(set(orbit_key.values())) == len(set(keys))
    orbits = [[s for s in sorted(actual) if orbit_key[s] == key] for key in keys]
    oid = {s: i for i, orbit in enumerate(orbits) for s in orbit}
    quotient = []
    for orbit in orbits:
        rows = {tuple(sum(oid[t] == j for t in graph[s]) for j in range(len(orbits)))
                for s in orbit}
        assert len(rows) == 1, ("representative-dependent quotient", m)
        quotient.append(list(rows.pop()))
    jq = [oid[J[orbit[0]]] for orbit in orbits]
    for i in range(len(orbits)):
        for j in range(len(orbits)):
            assert quotient[i][j] == quotient[jq[i]][jq[j]]
    result = {
        "m": m, "formal_states": len(data["formal"]), "actual_states": len(actual),
        "directed_edges": sum(map(len, graph.values())),
        "initial_states": len(data["F"]), "contractible_end_states": len(data["Lc"]),
        "noncontractible_end_states": len(data["Lnc"]),
        "quotient_states": len(orbits), "quotient_row_weights": quotient,
        "quotient_representatives": ["".join(map(str, key)) for key in keys],
        "quotient_orbit_sizes": list(map(len, orbits)),
        "quotient_initial_weights": [len(set(orbit) & data["F"]) for orbit in orbits],
        "quotient_J_zero_based": jq,
        "checks": {name: True for name in (
            "B_encoding_injective", "cap_closure_equals_B4", "J_involution",
            "J_endpoint_exchange", "J_geometry_preserving_edge_automorphism",
            "J_dihedral_equivariance", "quotient_rows_independent_of_representative",
            "J_preserves_quotient_weights")},
    }
    if m in EXPECTED:
        expected = EXPECTED[m]
        order = [by_word[tuple(map(int, w))] for w in expected["words"]]
        assert set(order) == actual, ("printed state set", m)
        matrix = [[int(t in graph[s]) for t in order] for s in order]
        assert matrix == expected["matrix"], ("printed full matrix", m, matrix)
        ends = {name: [i + 1 for i, s in enumerate(order) if s in data[name]]
                for name in ("F", "Lc", "Lnc")}
        for name in ends:
            assert ends[name] == expected[name], ("printed endpoint", m, name)
        assert quotient == expected["quotient"], ("printed quotient", m, quotient)
        result.update(printed_data_match=True, printed_word_order=expected["words"],
                      full_adjacency=matrix, printed_endpoint_indices=ends,
                      quotient_representatives=expected["orbit_reps"])
    return result


def cylinder_cycles(m, columns):
    """Independent direct Hamiltonian vertex-path DFS; no transfer states."""
    n = m * columns
    edges, seams = set(), set()
    for j in range(columns):
        for i in range(m):
            e = tuple(sorted((j * m + i, j * m + (i + 1) % m)))
            edges.add(e)
            if i == m - 1:
                seams.add(e)
            if j + 1 < columns:
                edges.add((j * m + i, (j + 1) * m + i))
    adjacent = [[] for _ in range(n)]
    for u, v in sorted(edges):
        adjacent[u].append(v)
        adjacent[v].append(u)
    path = [0]

    def walk(used):
        v = path[-1]
        if len(path) == n:
            if 0 in adjacent[v] and path[1] < v:
                cycle = frozenset(tuple(sorted((path[k - 1], path[k])))
                                  for k in range(n))
                yield cycle, len(cycle & seams) % 2
            return
        for w in adjacent[v]:
            if not (used >> w) & 1:
                path.append(w)
                yield from walk(used | (1 << w))
                path.pop()

    yield from walk(1)


def direct_b_sequence(m, columns, cycle, parity):
    """Color from the zero left cap, then label actual dual prefix components."""
    supports, a = [], [0] * m
    for j in range(columns):
        a = [a[i] ^ int(tuple(sorted((j * m + i, j * m + (i + 1) % m))) in cycle)
             for i in range(m)]
        supports.append(tuple(a))
    assert supports[-1] == (parity,) * m
    sequence, states = [], []
    for j in range(columns - 1):
        positive = {k * m + i for k in range(j + 1)
                    for i in range(m) if supports[k][i]}
        dual_edges = []
        for v in sorted(positive):
            k, i = divmod(v, m)
            for w in (k * m + (i + 1) % m, (k + 1) * m + i):
                if w in positive:
                    dual_edges.append((v, w))
        dual_cc = components(positive, dual_edges)
        labels = {v: k + 2 for k, part in enumerate(dual_cc) for v in part}
        word = canonical(tuple(labels.get(j * m + i, 0) for i in range(m)))
        sequence.append(word)
        cutoff, leafbase = (j + 1) * m, columns * m
        primal_edges = [(u, v) for u, v in cycle if v < cutoff]
        leaves = set()
        for u, v in cycle:
            if u < cutoff <= v:
                leaf = leafbase + v % m
                leaves.add(leaf)
                primal_edges.append((u, leaf))
        primal_cc = components(set(range(cutoff)) | leaves, primal_edges)
        pairing = []
        for part in primal_cc:
            ends = sorted(part & leaves)
            assert len(ends) == 2, ("direct prefix closed component", m, columns)
            pairing.append(tuple(v - leafbase for v in ends))
        state = (tuple(sorted(pairing)), supports[j][-1])
        assert b_word(m, state) == word, ("direct dual B vs P-union-S", m, columns, word)
        states.append(state)
    return tuple(sequence), states


def transfer_sequences(data, columns, terminal):
    words, graph = data["words"], data["graph"]
    found = set()

    def walk(state, sequence):
        if len(sequence) == columns - 1:
            if state in data[terminal]:
                assert sequence not in found
                found.add(sequence)
        else:
            for target in graph[state]:
                walk(target, sequence + (words[target],))

    for state in data["F"]:
        walk(state, (words[state],))
    return found


def audit_full_cylinder(data, columns):
    m = data["m"]
    direct, seen_states, seen_edges = [set(), set()], set(), set()
    for cycle, parity in cylinder_cycles(m, columns):
        sequence, states = direct_b_sequence(m, columns, cycle, parity)
        assert sequence not in direct[parity], ("nonunique actual B matrix", m, columns)
        direct[parity].add(sequence)
        assert states[0] in data["F"]
        assert states[-1] in data["Lnc" if parity else "Lc"]
        seen_states.update(states)
        for s, t in zip(states, states[1:]):
            assert t in data["graph"][s], ("direct cycle edge absent", m, columns)
            seen_edges.add((s, t))
    for parity, terminal in enumerate(("Lc", "Lnc")):
        transfer = transfer_sequences(data, columns, terminal)
        assert transfer == direct[parity], (
            "whole-cylinder B-sequence discrepancy", m, columns, terminal,
            sorted(transfer - direct[parity]), sorted(direct[parity] - transfer))
    return {"m": m, "vertex_columns": columns, "window_columns": columns - 1,
            "vertices": m * columns, "contractible_cycles": len(direct[0]),
            "noncontractible_cycles": len(direct[1]),
            "distinct_states_seen": len(seen_states), "distinct_edges_seen": len(seen_edges),
            "direct_dual_B_equals_pairing_encoding": True,
            "direct_and_transfer_B_sequence_sets_equal": True}


def main():
    root = Path(__file__).resolve().parent.parent
    sources = {
        "cylinder_transfer.md":
            "0973bc0d64481268ddf83ec66df0fbc1f03187a7f4a49cf37a0bd03b8c284991",
    }
    for filename, expected in sources.items():
        actual_hash = sha256((root / filename).read_bytes()).hexdigest()
        assert actual_hash == expected, ("frozen source hash", filename, actual_hash)
    models = [model(m) for m in (3, 4, 5)]
    report = {
        "status": "PASS", "scope": "Bounded finite audit only; no all-width proof claim.",
        "primary_source": PAPER,
        "primary_source_pages": {"B4": "226-227", "printed_matrices_and_sets": "231-232"},
        "frozen_sources_sha256": sources,
        "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "method": {
            "transitions": "Connected components of glued primal prefix-path edges, column vertices and frontier leaves.",
            "actual_state_filter": "Reachable from graph-derived first columns and coaccessible to graph-derived single-cycle right caps.",
            "B_reconstruction": "Connected components of multigraph P union positive-run endpoint matching S.",
            "independent_oracle": "Hamiltonian vertex-path DFS on each complete cylinder, reversal deduplicated; contractibility is wrap-seam edge parity.",
            "oracle_B_labels": "Actual positive-window connected components in each whole-cycle prefix.",
        },
        "models": [audit_model(data) for data in models],
        "whole_cylinders": [audit_full_cylinder(data, columns)
                            for data in models for columns in (2, 3)],
    }
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))



if __name__ == "__main__":
    main()
