"""Independent geometric checks of the SCC proof's explicit path gadgets.

These finite checks supplement the written induction; they do not replace it.
No transfer, certificate-generator, or SCC implementation is imported.
"""

if not __debug__:
    raise SystemExit(
        "Verification requires assertions. Rerun without -O/-OO and unset PYTHONOPTIMIZE."
    )


import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
DOCUMENT = (Path(sys.argv[1]).resolve() if len(sys.argv) > 1
            else ROOT / "grid_width_classification.md")


def edges(path):
    return {tuple(sorted((a, b))) for a, b in zip(path, path[1:])}


def check_path(path, endpoint_row):
    assert path[0] == (endpoint_row, 0)
    assert path[-1] == (endpoint_row, 3)
    assert len(set(path)) == len(path)
    assert all(abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1
               for a, b in zip(path, path[1:]))
    assert len(edges(path)) == len(path) - 1


def check_cover(paths, height):
    occupied = set()
    starts = []
    for path in paths:
        row = path[0][0]
        check_path(path, row)
        assert not occupied.intersection(path)
        occupied.update(path)
        starts.append(row)
    assert occupied == {(row, column) for row in range(height)
                        for column in range(4)}
    assert len(set(starts)) == len(starts)
    return set().union(*(edges(path) for path in paths))


def zigzag(height, offset=0):
    return [(offset + row, column)
            for column in range(4)
            for row in (range(height) if column % 2 == 0
                        else range(height - 1, -1, -1))]


def extend_two_rows(path, height):
    left, right = (height - 1, 0), (height - 1, 1)
    inserted = [(height, 0), (height + 1, 0), (height + 1, 1),
                (height + 1, 2), (height + 1, 3), (height, 3),
                (height, 2), (height, 1)]
    locations = [i for i, (a, b) in enumerate(zip(path, path[1:]))
                 if {a, b} == {left, right}]
    assert len(locations) == 1
    i = locations[0]
    if path[i] == right:
        inserted.reverse()
    return path[:i + 1] + inserted + path[i + 1:]


def main():
    document_before = hashlib.sha256(DOCUMENT.read_bytes()).hexdigest()
    alternatives = {
        3: [(1, 1), (2, 1), (3, 1), (3, 2), (3, 3), (3, 4),
            (2, 4), (2, 3), (2, 2), (1, 2), (1, 3), (1, 4)],
        4: [(1, 1), (2, 1), (3, 1), (4, 1), (4, 2), (4, 3),
            (4, 4), (3, 4), (2, 4), (2, 3), (3, 3), (3, 2),
            (2, 2), (1, 2), (1, 3), (1, 4)],
    }
    heights = []
    for base in (3, 4):
        first = zigzag(base)
        second = [(row - 1, column - 1)
                  for row, column in alternatives[base]]
        for height in range(base, 51, 2):
            first_edges = check_cover([first], height)
            second_edges = check_cover([second], height)
            assert first_edges != second_edges
            shared = tuple(sorted(((height - 1, 0), (height - 1, 1))))
            assert shared in first_edges.intersection(second_edges)
            reflected = [[(height - 1 - row, column) for row, column in path]
                         for path in (first, second)]
            assert check_cover([reflected[0]], height) != check_cover([reflected[1]], height)
            heights.append(height)
            if height + 2 <= 50:
                first = extend_two_rows(first, height)
                second = extend_two_rows(second, height)

    baseline = [[(0, column) for column in range(4)], zigzag(2, 1)]
    alternative = [[(0, 0), (0, 1), (1, 1), (1, 2), (0, 2), (0, 3)],
                   [(1, 0), (2, 0), (2, 1), (2, 2), (2, 3), (1, 3)]]
    cases = {"110": (baseline, alternative)}
    cases["011"] = tuple([[(2 - row, column) for row, column in path]
                           for path in cover] for cover in cases["110"])
    cases["101"] = (
        [[(0, column) for column in range(4)],
         [(3 - row, column) for row, column in zigzag(2, 1)]],
        [zigzag(2), [(2, column) for column in range(4)]],
    )
    mixed = []
    for mask, (first, second) in cases.items():
        first_edges = check_cover(first, 3)
        second_edges = check_cover(second, 3)
        assert first_edges != second_edges
        expected = {i for i, bit in enumerate(mask) if bit == "1"}
        assert {path[0][0] for path in first} == expected
        assert {path[0][0] for path in second} == expected
        mixed.append({"input_mask_top_to_bottom": mask,
                      "distinct_four_column_covers": 2,
                      "individual_endpoint_rows_preserved": sorted(expected)})

    assert hashlib.sha256(DOCUMENT.read_bytes()).hexdigest() == document_before
    result = {
        "status": "PASS",
        "reviewed_document": DOCUMENT.name,
        "reviewed_document_sha256": document_before,
        "method": "Direct vertex coverage, disjointness, adjacency, endpoint identity, and edge-set checks; no transfer-code imports",
        "height_family": {"verified_heights": sorted(heights),
                          "paths_per_height": 2,
                          "vertical_reflections_also_checked": True,
                          "common_bottom_edge_preserved": True},
        "mixed_interval_cases": mixed,
        "limits": ["Finite geometry checks supplement the separate all-height induction",
                   "No proof-assistant formalization or human peer review",
                   "No claim about external adoption or literature-wide priority"],
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
