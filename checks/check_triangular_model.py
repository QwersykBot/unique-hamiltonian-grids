#!/usr/bin/env python3
"""Independent exact finite oracle for simple triangular cylinder graphs.

Rows are zero-based modulo m.  A column has V_i=(i,i+1), and a
left-to-right cut has H_i=(i,i), D_i=(i,i+1).  Cut bits 2*i and 2*i+1
denote H_i and D_i respectively.  Edges are labeled, undirected, and simple.

The transfer construction never samples complete cycles to define states:
it generates every admissible first-column geometry, then exhausts reachable
states by a queue.  Whole-graph DFS below is a separate counting algorithm.
Only the Python standard library is used.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from functools import lru_cache
import hashlib
import json
from math import gcd
from pathlib import Path
import sys

if not __debug__:
    raise SystemExit("Verification requires assertions. Rerun without -O/-OO and unset PYTHONOPTIMIZE.")

Pairing = tuple[tuple[int, int], ...]
State = tuple[int, Pairing, int]


def bit_indices(mask: int):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def canonical_pairing(pairs) -> Pairing:
    return tuple(sorted(tuple(sorted(pair)) for pair in pairs))


def state_json(s: State):
    return [s[0], [list(p) for p in s[1]], s[2]]


def digest(value) -> str:
    raw = json.dumps(value, separators=(",", ":"), sort_keys=True).encode()
    return hashlib.sha256(raw).hexdigest()


class UnionFind:
    def __init__(self, n: int):
        self.parent = list(range(n))

    def find(self, a: int) -> int:
        while self.parent[a] != a:
            self.parent[a] = self.parent[self.parent[a]]
            a = self.parent[a]
        return a

    def join(self, a: int, b: int):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.parent[b] = a


class ColumnTransfer:
    def __init__(self, m: int):
        assert m >= 3
        self.m = m
        self.full = (1 << (2 * m)) - 1
        self.geometry_count = 0
        self.base_expansion_count = 0
        self.geometry_premature_closures = 0
        self.geometry_multiple_terminal_components = 0
        self.geometry_touched_same_destination_stubs = False
        self.seam_checks = 0
        self.initial = self.first_column()
        self.states: list[State] = []
        self.index: dict[State, int] = {}
        self.depth: list[int] = []
        self.edges: list[Counter[int]] = []
        self.terminals: list[tuple[int, int]] = []
        self.generate_closure()

    def incoming_row(self, stub: int) -> int:
        return (stub // 2 + stub % 2) % self.m

    def incoming_degrees(self, mask: int) -> tuple[int, ...]:
        deg = [0] * self.m
        for b in bit_indices(mask):
            deg[self.incoming_row(b)] += 1
        return tuple(deg)

    @lru_cache(maxsize=None)
    def local_geometries(self, incoming: int):
        """All V/outgoing choices satisfying degree two at current vertices."""
        inc = self.incoming_degrees(incoming)
        result = []
        for vertical in range(1 << self.m):
            deficits = []
            for row in range(self.m):
                vd = ((vertical >> row) & 1) + (
                    (vertical >> ((row - 1) % self.m)) & 1
                )
                deficits.append(2 - inc[row] - vd)
            if any(d < 0 or d > 2 for d in deficits):
                continue
            outgoing_choices = [0]
            for row, deficit in enumerate(deficits):
                if deficit == 2:
                    outgoing_choices = [x | (3 << (2 * row)) for x in outgoing_choices]
                elif deficit == 1:
                    outgoing_choices = [
                        x | (1 << (2 * row + kind))
                        for x in outgoing_choices
                        for kind in (0, 1)
                    ]
            for outgoing in outgoing_choices:
                delta = ((vertical >> (self.m - 1)) & 1) ^ (
                    (outgoing >> (2 * self.m - 1)) & 1
                )
                result.append((vertical, outgoing, delta))
        return tuple(result)

    def connect(self, incoming: int, pairing: Pairing, vertical: int, outgoing: int):
        """Return the outgoing pairing, 'terminal', or a rejection reason.

        Each old path becomes a connection between its two current endpoints.
        Distinct cut stubs remain distinct even if they reach the same vertex.
        Current vertices have degree two, so a component without an outgoing
        stub is a closed cycle.  An outgoing component must have two stubs.
        """
        assert sorted(b for p in pairing for b in p) == list(bit_indices(incoming))
        uf = UnionFind(3 * self.m)
        for a, b in pairing:
            ra, rb = self.incoming_row(a), self.incoming_row(b)
            if ra == rb:
                self.geometry_touched_same_destination_stubs = True
            uf.join(ra, rb)
        for row in bit_indices(vertical):
            uf.join(row, (row + 1) % self.m)
        for b in bit_indices(outgoing):
            uf.join(b // 2, self.m + b)
        groups = {uf.find(row): [] for row in range(self.m)}
        for b in bit_indices(outgoing):
            groups[uf.find(self.m + b)].append(b)
        if outgoing == 0:
            return "terminal" if len(groups) == 1 else "multiple_terminal_components"
        if any(len(ends) == 0 for ends in groups.values()):
            return "premature_closure"
        assert all(len(ends) == 2 for ends in groups.values())
        return canonical_pairing(groups.values())

    def seam_vector(self, outgoing: int, parity: int) -> tuple[int, ...]:
        """All meridian parities derived from the fixed seam and exterior degrees."""
        endpoint_parities = self.incoming_degrees(outgoing)
        seams = [0] * self.m
        previous = parity
        for row in range(self.m):
            seams[row] = previous ^ (endpoint_parities[row] % 2)
            previous = seams[row]
        assert seams[-1] == parity
        return tuple(seams)

    def check_seams(self, source: State | None, vertical: int, target: State):
        old = (0,) * self.m if source is None else self.seam_vector(source[0], source[2])
        expected = tuple(
            old[row] ^ ((vertical >> row) & 1) ^ ((target[0] >> (2 * row + 1)) & 1)
            for row in range(self.m)
        )
        assert expected == self.seam_vector(target[0], target[2])
        self.seam_checks += 1

    def first_column(self) -> Counter[State]:
        initial = Counter()
        for vertical, outgoing, delta in self.local_geometries(0):
            if not outgoing:
                continue  # Width one is outside this audit's a >= 2 domain.
            pairing = self.connect(0, (), vertical, outgoing)
            if isinstance(pairing, str):
                continue
            s = (outgoing, pairing, delta)
            self.check_seams(None, vertical, s)
            initial[s] += 1
        return initial

    @lru_cache(maxsize=None)
    def expand_base(self, incoming: int, pairing: Pairing):
        self.base_expansion_count += 1
        targets = Counter()
        terminal = Counter()
        for vertical, outgoing, delta in self.local_geometries(incoming):
            self.geometry_count += 1
            result = self.connect(incoming, pairing, vertical, outgoing)
            if result == "terminal":
                terminal[delta] += 1
            elif result == "premature_closure":
                self.geometry_premature_closures += 1
            elif result == "multiple_terminal_components":
                self.geometry_multiple_terminal_components += 1
            else:
                assert not isinstance(result, str)
                targets[(outgoing, result, delta)] += 1
        return targets, terminal

    def generate_closure(self):
        pending = deque()

        def add(s, depth):
            if s not in self.index:
                self.index[s] = len(self.states)
                self.states.append(s)
                self.depth.append(depth)
                pending.append(s)
            return self.index[s]

        for s in sorted(self.initial):
            add(s, 1)
        while pending:
            s = pending.popleft()
            sid = self.index[s]
            assert sid == len(self.edges)
            targets, terminal = self.expand_base(s[0], s[1])
            edges = Counter()
            for (outgoing, pairing, delta), weight in sorted(targets.items()):
                t = (outgoing, pairing, s[2] ^ delta)
                tid = add(t, self.depth[sid] + 1)
                edges[tid] += weight
            self.edges.append(edges)
            self.terminals.append(tuple(terminal[p ^ s[2]] for p in (0, 1)))
            # Independently propagate every seam through every admissible geometry.
            for vertical, outgoing, delta in self.local_geometries(s[0]):
                if outgoing:
                    result = self.connect(s[0], s[1], vertical, outgoing)
                    if not isinstance(result, str):
                        self.check_seams(s, vertical, (outgoing, result, s[2] ^ delta))
        assert len(self.states) == len(self.edges) == len(self.terminals)

    def counts(self, max_width: int, allowed=None):
        if allowed is None:
            allowed = set(range(len(self.states)))
        distribution = Counter({self.index[s]: w for s, w in self.initial.items() if self.index[s] in allowed})
        counts = {}
        for width in range(2, max_width + 1):
            counts[width] = tuple(
                sum(weight * self.terminals[i][p] for i, weight in distribution.items())
                for p in (0, 1)
            )
            next_distribution = Counter()
            for i, weight in distribution.items():
                for j, edge_weight in self.edges[i].items():
                    if j in allowed:
                        next_distribution[j] += weight * edge_weight
            distribution = next_distribution
        return counts

    def rotation(self, s: State) -> State:
        # Relabel every old row i to i+1.  The new fixed seam is the old
        # penultimate seam.  Their difference is the old last-row exterior degree.
        def rotate_stub(b):
            return 2 * ((b // 2 + 1) % self.m) + b % 2

        outgoing = sum(1 << rotate_stub(b) for b in bit_indices(s[0]))
        pairing = canonical_pairing((rotate_stub(a), rotate_stub(b)) for a, b in s[1])
        parity_shift = ((s[0] >> (2 * self.m - 2)) & 1) ^ (
            (s[0] >> (2 * self.m - 3)) & 1
        )
        return outgoing, pairing, s[2] ^ parity_shift

    def graph_receipt(self):
        n = len(self.states)
        reverse = [[] for _ in range(n)]
        for i, edges in enumerate(self.edges):
            for j in edges:
                reverse[j].append(i)
        coreachable = set(i for i, g in enumerate(self.terminals) if any(g))
        pending = deque(sorted(coreachable))
        while pending:
            j = pending.popleft()
            for i in reverse[j]:
                if i not in coreachable:
                    coreachable.add(i)
                    pending.append(i)

        z = (self.full, tuple((2 * i, 2 * i + 1) for i in range(self.m)), 1)
        zid = self.index[z]
        all_frontier = [i for i, s in enumerate(self.states) if s[0] == self.full]
        assert all_frontier == [zid]
        assert self.initial[z] == 1
        assert not self.edges[zid]
        assert self.terminals[zid] == (0, 1)
        assert not reverse[zid]

        raw_retained = set(range(n)) - {zid}
        raw_sccs = strongly_connected_components(self.edges, reverse, raw_retained)
        # A reachable path cover need not admit any Hamiltonian completion.
        # Actual cycle-prefix states are both reachable and terminal-coreachable.
        retained = coreachable - {zid}
        self.actual_nonzigzag = retained
        sccs = strongly_connected_components(self.edges, reverse, retained)
        periods = [component_period(self.edges, c) for c in sccs]
        J = {i: self.index.get((s[0], s[1], 1 - s[2])) for i, s in enumerate(self.states)}
        j_missing = [i for i in sorted(retained) if J[i] not in retained]
        j_edge_mismatch = []
        j_terminal_mismatch = []
        if not j_missing:
            for i in sorted(retained):
                expected = Counter({J[j]: weight for j, weight in self.edges[i].items() if j in retained})
                actual = Counter({j: weight for j, weight in self.edges[J[i]].items() if j in retained})
                if expected != actual:
                    j_edge_mismatch.append(i)
                if self.terminals[i][0] != self.terminals[J[i]][1]:
                    j_terminal_mismatch.append(i)

        rotated = {i: self.index.get(self.rotation(s)) for i, s in enumerate(self.states)}
        rotation_missing = [i for i in range(n) if rotated[i] is None]
        rotation_edge_mismatch = []
        rotation_boundary_mismatch = []
        if not rotation_missing:
            for i, s in enumerate(self.states):
                expected = Counter({rotated[j]: weight for j, weight in self.edges[i].items()})
                if expected != self.edges[rotated[i]]:
                    rotation_edge_mismatch.append(i)
                if self.terminals[i] != self.terminals[rotated[i]]:
                    rotation_boundary_mismatch.append(i)
                if self.initial[s] != self.initial[self.rotation(s)]:
                    rotation_boundary_mismatch.append(i)
        parity_changing_rotation = next(
            (s for s in self.states if self.rotation(s)[2] != s[2]), None
        )

        canonical_states = sorted(self.states)
        canonical_index = {s: i for i, s in enumerate(canonical_states)}
        graph_serialization = []
        for s in canonical_states:
            i = self.index[s]
            graph_serialization.append({
                "state": state_json(s),
                "initial_weight": self.initial[s],
                "terminal_weights_even_odd": self.terminals[i],
                "terminal_coreachable": i in coreachable,
                "actual_nonzigzag": i in retained,
                "minimum_prefix_columns": self.depth[i],
                "edges": sorted(
                    (canonical_index[self.states[j]], weight) for j, weight in self.edges[i].items()
                ),
            })
        self.graph_serialization = graph_serialization

        initial_indices = {self.index[s] for s in self.initial}
        retained_reachable = set(initial_indices & retained)
        pending = deque(sorted(retained_reachable))
        while pending:
            i = pending.popleft()
            for j in self.edges[i]:
                if j in retained and j not in retained_reachable:
                    retained_reachable.add(j)
                    pending.append(j)

        receipt = {
            "m": self.m,
            "generation": "queue exhausted; every local vertical/outgoing choice satisfying degree two examined",
            "reachable_states": n,
            "coreachable_states": len(coreachable),
            "initial_support": len(initial_indices),
            "initial_total_weight": sum(self.initial.values()),
            "directed_edges": sum(len(x) for x in self.edges),
            "total_edge_weight": sum(sum(x.values()) for x in self.edges),
            "maximum_parallel_multiplicity": max((max(e.values(), default=0) for e in self.edges), default=0),
            "maximum_minimum_prefix_columns": max(self.depth),
            "frontier_size_histogram": dict(sorted(Counter(s[0].bit_count() for s in self.states).items())),
            "all_frontier_states": len(all_frontier),
            "z": {
                "state": state_json(z),
                "initial_weight": self.initial[z],
                "incoming_arcs": len(reverse[zid]),
                "outgoing_arcs": len(self.edges[zid]),
                "terminal_weights_even_odd": self.terminals[zid],
                "only_contribution": {"width": 2, "even": 0, "odd": 1},
            },
            "raw_reachable_after_removing_z": {
                "states": len(raw_retained),
                "coreachable_states": len(raw_retained & coreachable),
                "scc_count": len(raw_sccs),
                "scc_sizes_descending": sorted((len(c) for c in raw_sccs), reverse=True),
                "dead_states": len(raw_retained - coreachable),
            },
            "after_removing_z": {
                "domain": "reachable AND terminal-coreachable states, excluding z",
                "states": len(retained),
                "directed_edges": sum(sum(j in retained for j in self.edges[i]) for i in retained),
                "total_edge_weight": sum(sum(w for j, w in self.edges[i].items() if j in retained) for i in retained),
                "reachable_from_retained_initial": len(retained_reachable),
                "coreachable_to_a_terminal": len(retained & coreachable),
                "scc_count": len(sccs),
                "scc_sizes_descending": sorted((len(c) for c in sccs), reverse=True),
                "scc_periods": sorted(periods),
                "J_missing_states": len(j_missing),
                "J_transition_weight_mismatches": len(j_edge_mismatch),
                "g_even_vs_J_g_odd_mismatches": len(j_terminal_mismatch),
                "self_loops": sum(i in self.edges[i] for i in retained),
            },
            "rotation": {
                "rule_zero_based": "rotate sources i to i+1, then t'=t XOR H_(m-1) XOR D_(m-2)",
                "missing_states": len(rotation_missing),
                "transition_weight_mismatches": len(rotation_edge_mismatch),
                "boundary_weight_mismatches": len(rotation_boundary_mismatch),
                "example_changing_partial_parity": (
                    {"state": state_json(parity_changing_rotation),
                     "rotated": state_json(self.rotation(parity_changing_rotation))}
                    if parity_changing_rotation else None
                ),
                "all_seam_vector_checks": self.seam_checks,
            },
            "local_geometry_diagnostics": {
                "expanded_distinct_incoming_pairings": self.base_expansion_count,
                "examined_geometries": self.geometry_count,
                "rejected_premature_closed_components": self.geometry_premature_closures,
                "rejected_multiple_terminal_components": self.geometry_multiple_terminal_components,
                "explicitly_encountered_distinct_stubs_sharing_destination": self.geometry_touched_same_destination_stubs,
            },
            "canonical_weighted_graph_sha256": digest(graph_serialization),
        }
        assert len(sccs) == 1 and periods == [1], receipt
        assert retained_reachable == retained, receipt
        assert not j_missing and not j_edge_mismatch and not j_terminal_mismatch, receipt
        assert not rotation_missing and not rotation_edge_mismatch and not rotation_boundary_mismatch, receipt
        return receipt


def strongly_connected_components(edges, reverse, vertices):
    visited = set()
    order = []
    for start in sorted(vertices):
        if start in visited:
            continue
        stack = [(start, iter(edges[start]))]
        visited.add(start)
        while stack:
            node, neighbors = stack[-1]
            try:
                nxt = next(neighbors)
            except StopIteration:
                order.append(node)
                stack.pop()
                continue
            if nxt in vertices and nxt not in visited:
                visited.add(nxt)
                stack.append((nxt, iter(edges[nxt])))
    components = []
    assigned = set()
    for start in reversed(order):
        if start in assigned:
            continue
        component = set()
        pending = [start]
        assigned.add(start)
        while pending:
            node = pending.pop()
            component.add(node)
            for nxt in reverse[node]:
                if nxt in vertices and nxt not in assigned:
                    assigned.add(nxt)
                    pending.append(nxt)
        components.append(component)
    return components


def component_period(edges, component):
    start = min(component)
    distance = {start: 0}
    pending = deque([start])
    while pending:
        node = pending.popleft()
        for nxt in edges[node]:
            if nxt in component and nxt not in distance:
                distance[nxt] = distance[node] + 1
                pending.append(nxt)
    assert set(distance) == component
    period = 0
    for node in component:
        for nxt in edges[node]:
            if nxt in component:
                period = gcd(period, abs(distance[node] + 1 - distance[nxt]))
    return period


def build_whole_graph(m: int, width: int):
    """Construct actual graph edges, independently of cut geometry code."""
    edges = {}

    def add(row_a, col_a, row_b, col_b, label, crosses):
        a, b = col_a * m + row_a, col_b * m + row_b
        key = tuple(sorted((a, b)))
        assert a != b and key not in edges
        edges[key] = (label, crosses)

    for col in range(width):
        for row in range(m):
            add(row, col, (row + 1) % m, col, f"V{row+1}@{col+1}", row == m - 1)
    for col in range(width - 1):
        for row in range(m):
            add(row, col, row, col + 1, f"H{row+1}@{col+1}", False)
            add(row, col, (row + 1) % m, col + 1, f"D{row+1}@{col+1}", row == m - 1)
    adjacency = [[] for _ in range(m * width)]
    for (a, b), (_, parity) in edges.items():
        adjacency[a].append((b, parity))
        adjacency[b].append((a, parity))
    for neighbors in adjacency:
        neighbors.sort()
    return edges, adjacency


def enumerate_whole_graph(m: int, width: int):
    """DFS vertex orders anchored at 0; reverse orders counted once.

    No transfer state, matching, or local-column legality routine is used.
    The DFS traverses actual graph vertices and closes only after all are used.
    """
    edges, adjacency = build_whole_graph(m, width)
    n = m * width
    full = (1 << n) - 1
    counts = [0, 0]
    examples = [None, None]
    square_examples = [None, None]
    splice_examples = {}
    all_outgoing_example_count = 0
    rotation_checked = 0
    path = [0]
    start_neighbors = {v: p for v, p in adjacency[0]}

    def finish(last, parity):
        nonlocal all_outgoing_example_count, rotation_checked
        if last not in start_neighbors or path[1] >= last:
            return
        parity ^= start_neighbors[last]
        counts[parity] += 1
        cycle_edges = {tuple(sorted((path[i], path[(i + 1) % n]))) for i in range(n)}
        labels = sorted(edges[e][0] for e in cycle_edges)
        if examples[parity] is None:
            examples[parity] = labels
        if not any(label.startswith("D") for label in labels):
            if square_examples[parity] is None:
                square_examples[parity] = labels
        # Check full-cycle parity directly under a row rotation.
        rotated_edges = {
            tuple(sorted((
                (a // m) * m + (a % m + 1) % m,
                (b // m) * m + (b % m + 1) % m,
            )))
            for a, b in cycle_edges
        }
        assert all(e in edges for e in rotated_edges)
        assert sum(edges[e][1] for e in rotated_edges) % 2 == parity
        rotation_checked += 1
        if width == 2 and all(not label.startswith("V") for label in labels):
            assert parity == 1
            all_outgoing_example_count += 1
        # Aligned vertical edges in the first and last column allow two copies
        # of a cycle to be joined by exchanging them for horizontal bridges.
        if parity == 0:
            label_set = set(labels)
            aligned_rows = [
                row + 1 for row in range(m)
                if f"V{row+1}@1" in label_set and f"V{row+1}@{width}" in label_set
            ]
            if aligned_rows and "even_aligned_vertical" not in splice_examples:
                splice_examples["even_aligned_vertical"] = {
                    "rows": aligned_rows, "edges": labels,
                    "all_square_edges": not any(label.startswith("D") for label in labels),
                }
            if aligned_rows and not any(label.startswith("D") for label in labels):
                splice_examples.setdefault("even_square_aligned_vertical", {
                    "rows": aligned_rows, "edges": labels,
                    "all_square_edges": True,
                })

    def visit(last, used, parity):
        if used == full:
            finish(last, parity)
            return
        for nxt, edge_parity in adjacency[last]:
            if used & (1 << nxt):
                continue
            path.append(nxt)
            visit(nxt, used | (1 << nxt), parity ^ edge_parity)
            path.pop()

    visit(0, 1, 0)
    return {
        "m": m,
        "width": width,
        "vertices": n,
        "graph_edges": len(edges),
        "even_contractible": counts[0],
        "odd_noncontractible": counts[1],
        "total": sum(counts),
        "full_cycle_rotations_checked": rotation_checked,
        "no_vertical_edge_zigzags": all_outgoing_example_count if width == 2 else None,
        "first_cycle_examples_even_odd": examples,
        "first_square_cycle_examples_even_odd": square_examples,
        "splicing_witnesses": splice_examples,
    }


def validate_selected_cycle(m, width, selected):
    """Read selected actual edges as a graph, checking degree and connectivity."""
    all_edges, _ = build_whole_graph(m, width)
    assert set(selected) <= all_edges.keys()
    adjacency = [[] for _ in range(m * width)]
    for a, b in selected:
        adjacency[a].append(b)
        adjacency[b].append(a)
    assert all(len(neighbors) == 2 for neighbors in adjacency)
    visited = {0}
    pending = [0]
    while pending:
        a = pending.pop()
        for b in adjacency[a]:
            if b not in visited:
                visited.add(b)
                pending.append(b)
    assert len(visited) == m * width
    return sum(all_edges[e][1] for e in selected) % 2


def prefix_state_from_selected_cycle(m, width, selected, cut) -> State:
    """Extract a prefix by explicit graph traversal, without transfer.connect."""
    assert 1 <= cut < width
    all_edges, _ = build_whole_graph(m, width)
    prefix_neighbors = defaultdict(list)
    outgoing = 0
    parity = 0
    stub_offset = m * width
    for a, b in selected:
        col_a, col_b = a // m, b // m
        if col_a >= cut and col_b >= cut:
            continue
        parity ^= all_edges[(a, b)][1]
        if col_a < cut and col_b < cut:
            pa, pb = a, b
        else:
            assert col_a == cut - 1 and col_b == cut
            row_a, row_b = a % m, b % m
            kind = 0 if row_a == row_b else 1
            assert (row_a + kind) % m == row_b
            stub = 2 * row_a + kind
            outgoing |= 1 << stub
            pa, pb = a, stub_offset + stub
        prefix_neighbors[pa].append(pb)
        prefix_neighbors[pb].append(pa)
    assert all(len(prefix_neighbors[v]) == 2 for v in range(m * cut))
    assert all(len(prefix_neighbors[stub_offset + b]) == 1 for b in bit_indices(outgoing))
    visited = set()
    pairs = []
    for start in sorted(prefix_neighbors):
        if start in visited:
            continue
        ends = []
        pending = [start]
        visited.add(start)
        while pending:
            vertex = pending.pop()
            if vertex >= stub_offset:
                ends.append(vertex - stub_offset)
            for nxt in prefix_neighbors[vertex]:
                if nxt not in visited:
                    visited.add(nxt)
                    pending.append(nxt)
        assert len(ends) == 2
        pairs.append(ends)
    return outgoing, canonical_pairing(pairs), int(parity)


def declared_contractible_witness(m, width):
    """The explicit unrolled a=2 and a=3 constructions in the reviewed note.

    This spotcheck was added only after the independent transfer and DFS had
    been implemented and agreed.  It tests the stated construction separately.
    """
    assert width in (2, 3)
    labels = set()
    for row in range(1, m):
        labels.add(f"V{row}@1")
        labels.add(f"V{row}@{width}")
    for col in range(1, width):
        labels.add(f"H1@{col}")
        labels.add(f"H{m}@{col}")
    if width == 3:
        pair_stop = m - 1 if m % 2 == 0 else m - 2
        for row_zero in range(1, pair_stop, 2):
            row = row_zero + 1
            labels.remove(f"V{row}@1")
            labels.update((f"H{row}@1", f"V{row}@2", f"H{row+1}@1"))
        if m % 2:
            row = m - 2
            labels.remove(f"V{row}@1")
            labels.update((f"D{row}@1", f"H{row+1}@1"))
    all_edges, _ = build_whole_graph(m, width)
    by_label = {label: e for e, (label, _) in all_edges.items()}
    selected = {by_label[label] for label in labels}
    assert validate_selected_cycle(m, width, selected) == 0
    assert f"V{m-1}@1" in labels and f"V{m-1}@{width}" in labels
    assert all(not all_edges[e][1] for e in selected)
    return selected, sorted(labels)


def check_declared_self_splice(transfer, width):
    m = transfer.m
    selected, labels = declared_contractible_witness(m, width)
    shift = m * width
    joined = set(selected) | {(a + shift, b + shift) for a, b in selected}
    row_gap = m - 2
    left_a = (width - 1) * m + row_gap
    right_a = width * m + row_gap
    joined.remove((left_a, left_a + 1))
    joined.remove((right_a, right_a + 1))
    joined.add((left_a, right_a))
    joined.add((left_a + 1, right_a + 1))
    assert validate_selected_cycle(m, 2 * width, joined) == 0
    states = [prefix_state_from_selected_cycle(m, 2 * width, joined, cut) for cut in range(1, 2 * width)]
    assert states[0] == states[width]
    state_ids = [transfer.index[s] for s in states]
    assert all(i in transfer.actual_nonzigzag for i in state_ids)
    for i, j in zip(state_ids, state_ids[1:]):
        assert transfer.edges[i][j] > 0
    return {
        "m": m,
        "copy_width": width,
        "cycle_edges": labels,
        "parity": 0,
        "uses_no_wrap_edge": True,
        "common_boundary_gap_one_based": m - 1,
        "joined_width": 2 * width,
        "joined_is_single_hamiltonian_cycle": True,
        "closed_transfer_walk_length": width,
        "closed_walk_states": [state_json(s) for s in states[:width + 1]],
    }


def main():
    max_width = 8
    receipt = {
        "scope": "Exact finite checks; no all-width theorem and no identification with the 2018 paper's labeled B matrix.",
        "model": {
            "rows": "i modulo m, m>=3", "columns": "j=1..a, a>=2",
            "vertical": "(i,j)--(i+1,j)",
            "horizontal": "(i,j)--(i,j+1)",
            "diagonal": "(i,j)--(i+1,j+1)",
            "meridian": "V_m and D_m in one-based row indices",
            "counting": "undirected labeled Hamiltonian cycle edge sets",
            "stub_encoding": "bit 2*i=H_i, bit 2*i+1=D_i in zero-based row indices",
            "parity_accounting": "vertical and outgoing diagonal edges assigned to their processed column; incoming never recounted",
        },
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "transfer": [],
        "independent_whole_graph_dfs": [],
        "declared_contractible_self_splice_spotchecks": [],
        "published_count_crosscheck": {
            "reference": "O. Bodroza-Pantic, H. Kwong, R. Doroslovacki, M. Pantic, A limit conjecture on the number of Hamiltonian cycles on thin triangular grid cylinder graphs, Discussiones Mathematicae Graph Theory 38 (2018), 405-427.",
            "doi": "10.7151/dmgt.2021",
            "primary_url": "https://bibliotekanauki.pl/articles/31342332.pdf",
            "tables": "Tables 2 and 3",
            "index_mapping": "paper n = this audit's a - 1",
            "source_verification": "Primary tables checked by supervising agent; this agent's PDF request returned HTTP 403.",
            "rows": [],
        },
    }
    transfer_counts = {}
    for m in (3, 4):
        transfer = ColumnTransfer(m)
        result = transfer.graph_receipt()
        counts = transfer.counts(max_width)
        reduced_counts = transfer.counts(max_width, transfer.actual_nonzigzag)
        for a, count in counts.items():
            reduced = reduced_counts[a]
            assert count == (reduced[0], reduced[1] + int(a == 2))
        result["reduced_transfer_plus_z_agrees_through_width"] = max_width
        result["counts_by_width"] = {
            str(a): {"even_contractible": c[0], "odd_noncontractible": c[1], "total": sum(c)}
            for a, c in counts.items()
        }
        transfer_counts[m] = counts
        receipt["transfer"].append(result)
        receipt["declared_contractible_self_splice_spotchecks"].extend(
            check_declared_self_splice(transfer, a) for a in (2, 3)
        )
    dfs_cases = [(3, 2), (3, 3), (3, 4), (4, 2), (4, 3)]
    for m, width in dfs_cases:
        if m not in transfer_counts:
            continue
        result = enumerate_whole_graph(m, width)
        actual = (result["even_contractible"], result["odd_noncontractible"])
        expected = transfer_counts[m][width]
        result["transfer_agrees"] = actual == expected
        assert actual == expected, (m, width, actual, expected)
        if width == 2:
            assert result["no_vertical_edge_zigzags"] == 1
        receipt["independent_whole_graph_dfs"].append(result)
    published_rows = [(3, 2, 6, 10), (3, 3, 48, 42), (3, 4, 312, 318), (4, 2, 8, 21), (4, 3, 200, 124)]
    for m, width, even, odd in published_rows:
        if m not in transfer_counts:
            continue
        assert transfer_counts[m][width] == (even, odd)
        receipt["published_count_crosscheck"]["rows"].append({
            "m": m, "paper_n": width - 1, "audit_width_a": width,
            "even_contractible": even, "odd_noncontractible": odd, "agrees": True,
        })
    receipt["all_assertions_passed"] = True
    receipt["status"] = "PASS"
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
