"""Finite oracle for the note's one-column, nonempty reverse-lifting lemma.

Exhaust every degree-two full-column geometry at heights 3..10, retaining
cap-free columns with nonempty even input and output. Enumerate every
noncrossing output matching and recover inputs by glued-graph connectivity.
All closed components are excluded from lifting, including a sole cycle.
No witness-insertion algorithm, transfer matrix, or SCC code is used.
This is a finite one-column check, not an all-height or sequence proof.
Stdlib Python >=3.10; deterministic JSON stdout; no writes or timing calls.
"""

if not __debug__:
    raise SystemExit(
        "Verification requires assertions. Rerun without -O/-OO and unset PYTHONOPTIMIZE."
    )

from functools import lru_cache
import hashlib
from itertools import product
import json
from math import comb
from pathlib import Path


def noncrossing(pairs, ports):
    return (all(a < b for a, b in pairs)
            and sorted(r for pair in pairs for r in pair) == list(ports)
            and not any(a < c < b < d or c < a < d < b
                        for a, b in pairs for c, d in pairs))


@lru_cache(None)
def matchings(ports):
    result = ((),) if not ports else tuple(
        tuple(sorted(((ports[0], ports[j]),) + left + right))
        for j in range(1, len(ports), 2)
        for left in matchings(ports[1:j])
        for right in matchings(ports[j + 1:]))
    t = len(ports) // 2
    assert len(ports) % 2 == 0
    assert len(result) == len(set(result)) == comb(2 * t, t) // (t + 1)
    assert all(noncrossing(pairs, ports) for pairs in result)
    return result


def geometries(height):
    """Solve x_r+y_r+b_(r-1)+b_r=2 over binary variables, exhaustively."""
    for bits in product((0, 1), repeat=height - 1):
        boundary = (0,) + bits + (0,)
        need = tuple(2 - boundary[r] - boundary[r + 1]
                     for r in range(height))
        flexible = tuple(r for r in range(height) if need[r] == 1)
        for choices in product((0, 1), repeat=len(flexible)):
            x = [int(n == 2) for n in need]
            for r, bit in zip(flexible, choices):
                x[r] = bit
            y = [n - bit for n, bit in zip(need, x)]
            yield (tuple(r + 1 for r in range(height) if x[r]),
                   tuple(r + 1 for r in range(height) if y[r]),
                   tuple(r + 1 for r, bit in enumerate(bits) if bit))


def interval_counts(height, x, y, vertical):
    counts = {"through": 0, "cup": 0, "cap": 0}
    for r in range(1, height + 1):
        assert ((r in x) + (r in y) + (r - 1 in vertical)
                + (r in vertical)) == 2
    start = 1
    for end in range(1, height + 1):
        if end in vertical:
            continue
        if start == end:
            assert start in x and start in y
            kind = "through"
        else:
            assert not any(r in x or r in y for r in range(start + 1, end))
            assert all((r in x) != (r in y) for r in (start, end))
            incoming = (start in x) + (end in x)
            kind = ("cup", "through", "cap")[incoming]
        counts[kind] += 1
        start = end + 1
    return counts


def reverse_compose(height, x, y, vertical, pairs):
    """Compute CURRENT components of the entire reversed, glued graph."""
    assert noncrossing(pairs, y)
    graph = {r: set() for r in range(1, height + 1)}

    def edge(a, b):
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)

    for a, b in pairs:
        edge(height + a, height + b)
    for r in y:
        edge(r, height + r)
    for r in x:
        edge(r, 2 * height + r)
    for r in vertical:
        edge(r, r + 1)
    assert all(len(adjacent) == (1 if node > 2 * height else 2)
               for node, adjacent in graph.items())
    remaining, components = set(graph), []
    while remaining:
        stack, component = [min(remaining)], set()
        while stack:
            node = stack.pop()
            if node not in component:
                component.add(node)
                stack.extend(graph[node] - component)
        remaining.difference_update(component)
        ends = tuple(sorted(node - 2 * height for node in component
                            if node > 2 * height))
        assert len(ends) in (0, 2)
        components.append(ends)
    if any(not ends for ends in components):
        return None, "completed_cycle" if len(components) == 1 else "proper_cycle"
    return tuple(sorted(components)), "ordinary"


def main():
    source = Path(__file__).resolve()
    document = source.parent.parent / "polynomial_cutoff.md"
    document_hash = hashlib.sha256(document.read_bytes()).hexdigest()
    heights = []
    for height in range(3, 11):
        counts = {"height": height, "geometries": 0, "by_cup_count": {},
                  "input_matching_obligations": 0, "output_matchings_tested": 0,
                  "valid_lifts": 0, "proper_cycle_rejections": 0}
        for x, y, vertical in geometries(height):
            kinds = interval_counts(height, x, y, vertical)
            if not x or not y or len(x) % 2 or len(y) % 2 or kinds["cap"]:
                continue
            counts["geometries"] += 1
            cups = str(kinds["cup"])
            counts["by_cup_count"][cups] = counts["by_cup_count"].get(cups, 0) + 1
            targets, achieved = set(matchings(x)), set()
            counts["input_matching_obligations"] += len(targets)
            for pairs in matchings(y):
                result, status = reverse_compose(height, x, y, vertical, pairs)
                counts["output_matchings_tested"] += 1
                if status == "ordinary":
                    assert noncrossing(result, x) and result in targets
                    achieved.add(result)
                    counts["valid_lifts"] += 1
                else:
                    assert status == "proper_cycle"  # x is nonempty.
                    counts["proper_cycle_rejections"] += 1
            assert achieved == targets, (height, x, y, vertical, targets - achieved)
        heights.append(counts)

    empty_outcomes = [reverse_compose(4, (), (1, 2, 3, 4), (1, 3), r)
                      for r in matchings((1, 2, 3, 4))]
    assert all(result is None for result, status in empty_outcomes)
    assert {status for result, status in empty_outcomes} == {"proper_cycle", "completed_cycle"}
    r = ((1, 4), (2, 3), (5, 6))
    assert (1, 2) not in r and (3, 4) not in r
    joint = reverse_compose(6, (5, 6), (1, 2, 3, 4, 5, 6), (1, 3), r)
    assert joint == (None, "proper_cycle")
    assert reverse_compose(6, (5, 6), (1, 2, 3, 4, 5, 6), (3, 1), r) == joint
    assert hashlib.sha256(document.read_bytes()).hexdigest() == document_hash
    print(json.dumps({
        "status": "PASS", "checker_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "reviewed_document": document.name, "reviewed_document_sha256": document_hash,
        "method": "Exhaustive local degree equations; Catalan enumeration checked independently for crossings; full glued-graph connected components",
        "scope": "Every cap-free full column with nonempty even input/output ports at heights 3..10; every noncrossing output matching; surjectivity onto every noncrossing input matching",
        "heights": heights,
        "negative_controls": {
            "empty_input_two_cup_birth_height_4": {
                "ordinary_lifts": 0, "reversed_outcomes": sorted(s for _, s in empty_outcomes)},
            "joint_caps_height_6": {"matching": r, "caps": ((1, 2), (3, 4)),
                                    "straight_rows": (5, 6), "outcome": joint[1],
                                    "cap_order_reversal_checked": True}},
        "limits": ["Finite one-column existence check only; no all-height or sequence proof",
                   "No witness insertion, transfer matrices, SCCs, or imported proof/checker code",
                   "All closure is excluded from lifting, even a sole completed cycle",
                   "No polynomial-cutoff or novelty conclusion is inferred"]
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
