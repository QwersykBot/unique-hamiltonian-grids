#!/usr/bin/env python3
"""Check a complete M(12,12) lower-bound certificate, without cycle search.

Input is one or more gzip JSONL files.  Each starts with
  {"format":"m12-hc-certificate-v1","n":12,
   "edge_order":"row-major-right-then-down"}
and then contains records [D, 0] or [D, hex_cycle_1, hex_cycle_2].
Each D is a sorted, D4-canonical, balanced deletion set of size 0, 2, or 4.
The two 66-digit hexadecimal integers select edges of the *full* grid:
at each row-major vertex, list its right edge first, then its down edge.
Bit zero is the first edge.  No producer status or search result is trusted.

Positive records are checked as two distinct spanning connected 2-factors.
Zero records require a degree contradiction or a forced proper cycle.
These are necessary obstructions;
the checker never branches, searches for a Hamiltonian cycle, or times out.

Coverage uses distinct canonical sets and independently derived Burnside
totals.  --partial validates only the supplied records and makes no complete
coverage claim.  No imports from the producer or other counting programs.
"""

import argparse
from collections import Counter, deque
import gzip
import json
from pathlib import Path
import re
import sys
from time import perf_counter


N = 12
V = N * N
FULL_VERTICES = (1 << V) - 1

# Independent closed-form counts, not values read from the producer.
# d=2: identity fixes 72^2; each axial reflection fixes 72 mixed-color pairs.
# A quarter-turn has no size-two orbit; a half-turn or diagonal reflection
# has only monochromatic two-orbits (and diagonal fixed points have one color).
# d=4: identity C(72,2)^2; quarter-turn 36; half-turn 36^2;
# diagonal 36*(30+C(12,2)); axial C(72,2).
FIXED = {
    0: (1, 1, 1, 1, 1, 1, 1, 1),
    2: (5184, 0, 0, 0, 0, 72, 0, 72),
    4: (6533136, 36, 1296, 36, 3456, 2556, 3456, 2556),
}
EXPECTED_ORBITS = {d: sum(values) // 8 for d, values in FIXED.items()}
EXPECTED_RAW = {d: values[0] for d, values in FIXED.items()}

EDGES = []
NEIGHBORS = [[] for _ in range(V)]
INCIDENT = [0] * V
ENDPOINT_XOR = []
for vertex in range(V):
    row, column = divmod(vertex, N)
    targets = []
    if column + 1 < N:
        targets.append(vertex + 1)
    if row + 1 < N:
        targets.append(vertex + N)
    for other in targets:
        bit = 1 << len(EDGES)
        EDGES.append((vertex, other))
        ENDPOINT_XOR.append(vertex ^ other)
        INCIDENT[vertex] |= bit
        INCIDENT[other] |= bit
        NEIGHBORS[vertex].append(other)
        NEIGHBORS[other].append(vertex)
FULL_EDGES = (1 << len(EDGES)) - 1
HEX_DIGITS = (len(EDGES) + 3) // 4
HEX_PATTERN = re.compile(r"[0-9a-fA-F]{%d}" % HEX_DIGITS)


class InvalidCertificate(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def orbit(deleted):
    """Eight explicit square isometries; no rotation-loop implementation."""
    coordinates = [divmod(vertex, N) for vertex in deleted]
    transforms = (
        lambda r, c: (r, c),
        lambda r, c: (r, N - 1 - c),
        lambda r, c: (N - 1 - r, c),
        lambda r, c: (N - 1 - r, N - 1 - c),
        lambda r, c: (c, r),
        lambda r, c: (c, N - 1 - r),
        lambda r, c: (N - 1 - c, r),
        lambda r, c: (N - 1 - c, N - 1 - r),
    )
    result = set()
    for transform in transforms:
        result.add(tuple(sorted(N * a + b
                                for a, b in (transform(r, c) for r, c in coordinates))))
    return result


def validate_deletions(value):
    require(isinstance(value, list), "deletion set must be a list")
    require(len(value) in EXPECTED_ORBITS, "deletion size must be 0, 2, or 4")
    require(all(type(v) is int and 0 <= v < V for v in value),
            "invalid deleted vertex")
    deleted = tuple(value)
    require(tuple(sorted(set(deleted))) == deleted, "deletions are not sorted and distinct")
    require(sum((v // N + v % N) % 2 for v in deleted) == len(deleted) // 2,
            "deletions are not color-balanced")
    images = orbit(deleted)
    require(min(images) == deleted, "deletion set is not D4-canonical")
    return deleted, len(images)


def parse_cycle(value):
    require(isinstance(value, str) and HEX_PATTERN.fullmatch(value) is not None,
            "cycle must be exactly 66 hexadecimal digits")
    mask = int(value, 16)
    require(mask & ~FULL_EDGES == 0, "cycle contains bits beyond the full-grid edge list")
    return mask


def validate_cycle(mask, deleted):
    """Check degree and walk the single selected component, using full-grid edges."""
    expected_degree = [2] * V
    retained_mask = FULL_VERTICES
    for vertex in deleted:
        expected_degree[vertex] = 0
        retained_mask ^= 1 << vertex
    retained_count = V - len(deleted)
    require(mask.bit_count() == retained_count, "wrong number of selected edges")
    selected = [mask & edges for edges in INCIDENT]
    require(all(edges.bit_count() == expected_degree[v]
                for v, edges in enumerate(selected)),
            "selected edges violate a retained/deleted vertex degree")

    start = (retained_mask & -retained_mask).bit_length() - 1
    vertex, previous_edge, visited = start, 0, 0
    for _ in range(retained_count):
        require(not (visited >> vertex & 1), "selected edges contain a proper cycle")
        visited |= 1 << vertex
        onward = selected[vertex] ^ previous_edge
        edge_bit = onward & -onward
        vertex = ENDPOINT_XOR[edge_bit.bit_length() - 1] ^ vertex
        previous_edge = edge_bit
    require(vertex == start and visited == retained_mask,
            "selected edges are not one spanning cycle")


def certify_zero(deleted):
    """Return a necessary obstruction, or None if no allowed proof was found.

    The available and forced graphs use vertex-neighbor sets, independently
    of the producer's edge-state arrays and disjoint-set implementation.
    """
    gone = set(deleted)
    kept = [v for v in range(V) if v not in gone]
    available = [set() if v in gone else set(NEIGHBORS[v]) - gone for v in range(V)]
    forced = [set() for _ in range(V)]
    pending = deque(kept)
    while pending:
        vertex = pending.popleft()
        if len(forced[vertex]) > 2 or len(available[vertex]) < 2:
            return "degree"
        if len(available[vertex]) == 2:
            for other in available[vertex] - forced[vertex]:
                forced[vertex].add(other)
                forced[other].add(vertex)
                pending.append(other)
        if len(forced[vertex]) == 2:
            for other in available[vertex] - forced[vertex]:
                available[vertex].remove(other)
                available[other].remove(vertex)
                pending.append(other)

    # At the fixed point all forced degrees are at most two.  A forced
    # component that is a cycle cannot later connect to another component.
    unseen = set(kept)
    while unseen:
        first = next(iter(unseen))
        component, stack = {first}, [first]
        while stack:
            vertex = stack.pop()
            for other in forced[vertex]:
                if other not in component:
                    component.add(other)
                    stack.append(other)
        unseen.difference_update(component)
        if len(component) < len(kept) and all(len(forced[v]) == 2 for v in component):
            return "forced_proper_cycle"

    # No general Hamiltonian search or additional rejection rule is used.
    # A producer's zero label is rejected unless one of the proofs above
    # succeeds.  In particular, lack of a found cycle is never a zero proof.
    return None


def check(paths, partial=False):
    started = perf_counter()
    seen = {d: set() for d in EXPECTED_ORBITS}
    counts = {d: Counter() for d in EXPECTED_ORBITS}
    orbit_weights = Counter()
    zero_reasons = Counter()
    records = 0
    for path in paths:
        with gzip.open(path, "rt", encoding="utf-8") as stream:
            header = json.loads(next(stream, "null"))
            require(isinstance(header, dict)
                    and header.get("format") == "m12-hc-certificate-v1"
                    and type(header.get("n")) is int and header["n"] == N
                    and header.get("edge_order") == "row-major-right-then-down",
                    f"{path}: invalid or missing certificate header")
            for line_number, line in enumerate(stream, 2):
                try:
                    record = json.loads(line)
                    require(isinstance(record, list) and len(record) in (2, 3),
                            "record must be [D,0] or [D,hex1,hex2]")
                    deleted, orbit_size = validate_deletions(record[0])
                    d = len(deleted)
                    require(deleted not in seen[d], "duplicate deletion set")
                    if len(record) == 2:
                        require(type(record[1]) is int and record[1] == 0,
                                "two-field record must have integer zero marker")
                        reason = certify_zero(deleted)
                        require(reason is not None,
                                "zero label has no permitted necessary-obstruction proof")
                        zero_reasons[reason] += 1
                        counts[d]["zero"] += 1
                    else:
                        first, second = map(parse_cycle, record[1:])
                        require(first != second, "the two cycle edge sets are identical")
                        validate_cycle(first, deleted)
                        validate_cycle(second, deleted)
                        counts[d]["at_least_two"] += 1
                    seen[d].add(deleted)
                    orbit_weights[d] += orbit_size
                    records += 1
                    if records % 100000 == 0:
                        print(f"Checked {records:,} certificate records", file=sys.stderr, flush=True)
                except (ValueError, TypeError, IndexError, KeyError) as error:
                    raise InvalidCertificate(f"{path}:{line_number}: {error}") from error
    if not partial:
        for d in EXPECTED_ORBITS:
            require(len(seen[d]) == EXPECTED_ORBITS[d], f"incomplete coverage for d={d}")
            require(orbit_weights[d] == EXPECTED_RAW[d], f"wrong expanded orbit total for d={d}")
    return {
        "valid": True,
        "complete": not partial,
        "records": records,
        "datasets": {str(d): {"canonical_sets": len(seen[d]),
                              "expected_canonical_sets": EXPECTED_ORBITS[d],
                              "expanded_orbit_total": orbit_weights[d],
                              "classifications": dict(counts[d])}
                     for d in EXPECTED_ORBITS},
        "zero_obstructions": dict(zero_reasons),
        "conclusion": ("Every balanced deletion set of size 0, 2, or 4 has zero or at least two Hamiltonian cycles; therefore M(12,12) >= 6."
                       if not partial else
                       "Only supplied records were validated; complete coverage and the lower bound are not asserted."),
        "seconds": perf_counter() - started,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="+", type=Path, help="gzip JSONL certificate files")
    parser.add_argument("--partial", action="store_true", help="validate a sample without claiming complete coverage")
    args = parser.parse_args()
    try:
        report = check(args.certificates, partial=args.partial)
    except (OSError, EOFError, ValueError, TypeError) as error:
        print(f"INVALID CERTIFICATE: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
