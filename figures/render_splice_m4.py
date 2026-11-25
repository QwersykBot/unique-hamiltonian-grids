#!/usr/bin/env python3
"""Render one pinned, hand-specified cylinder splice; perform no search.

Run with Python and matplotlib installed:
    python render_splice_m4.py

Keep figure-splice-m4-data.json beside this script. Optional --data and
--output-dir arguments change locations, never the accepted input hash.
The source proof and JSON are read-only inputs. The SVG and PNG are outputs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch, Patch, Rectangle


DATA_SHA256 = "c67f51c76c2044906f3ca66de75c05940624ba25197a57e8c574c3e991a5e691"
PROOF_SHA256 = "a36a91a5382a0faec583eea4e7f98689ab5880411f02e5bf4063731022915b95"
PROOF_NAME = "cylinder-direct-splicing-lemma.txt"
OUTPUT_STEM = "figure-splice-m4"

INK = "#202a33"
MUTED = "#5e6d7a"
GRID = "#ccd6dd"
POSITIVE = "#dcecf5"
ZERO = "#ffffff"
RED = "#c43c42"
GOLD = "#b9820b"
COPY_DASH = (0, (3.2, 2.4))
REMOVED_DASH = (0, (4.2, 2.5))


def key(edge):
    return tuple(sorted(tuple(v) for v in edge))


def global_key(edge, offset):
    return key(((r, c + offset) for r, c in edge))


def draw_windows(ax, graph):
    offset = graph["global_column_offset"]
    supports = graph["cap_and_window_support_columns"][1:-1]
    for cut, support in enumerate(supports, start=1):
        for gap, bit in enumerate(support, start=1):
            x, y = offset + cut, 4 - gap
            ax.add_patch(
                Rectangle(
                    (x, y), 1, 1,
                    facecolor=POSITIVE if bit else ZERO,
                    edgecolor=GRID, linewidth=0.75, zorder=0,
                )
            )
            ax.text(
                x + 0.5, y + 0.5, str(bit),
                ha="center", va="center", fontsize=13.5,
                color="#325c74" if bit else "#71818c",
                weight="medium", zorder=2,
            )


def draw_selected_edges(ax, graph, removed=frozenset(), added=frozenset()):
    offset = graph["global_column_offset"]
    for original_edge in graph["selected_edges"]:
        (r1, c1), (r2, c2) = original_edge
        edge = global_key(original_edge, offset)
        is_removed, is_added = edge in removed, edge in added
        color = RED if is_removed else GOLD if is_added else INK
        linewidth = 3.2 if is_removed or is_added else 2.5
        linestyle = REMOVED_DASH if is_removed else "solid"
        if r1 == r2:
            x = [c1 + offset, c2 + offset]
            y = [5 - r1, 5 - r1]
            ax.plot(
                x, y, color=color, linewidth=linewidth,
                linestyle=linestyle, solid_capstyle="round", zorder=4,
            )
            if r1 == 1:
                # The bottom boundary is an identified copy, not new edges.
                ax.plot(
                    x, [0, 0], color=color,
                    linewidth=2.65 if is_added else 1.9,
                    linestyle=COPY_DASH, alpha=0.95,
                    dash_capstyle="butt", zorder=4,
                )
        else:
            assert c1 == c2
            if {r1, r2} == {1, 4}:
                y = [1, 0]  # gap 4: row 4 to the lower copy of row 1
            else:
                assert abs(r1 - r2) == 1
                y = [5 - r1, 5 - r2]
            ax.plot(
                [c1 + offset, c1 + offset], y,
                color=color, linewidth=linewidth, linestyle=linestyle,
                solid_capstyle="round", dash_capstyle="butt", zorder=4,
            )


def draw_vertices(ax, graph):
    offset = graph["global_column_offset"]
    columns = [offset + c for c in range(1, graph["vertex_columns"] + 1)]
    for x in columns:
        ax.scatter([x] * 4, [4, 3, 2, 1], s=22, color=INK, zorder=5)
        ax.scatter(
            [x], [0], s=29, facecolor="white", edgecolor=INK,
            linewidth=1.1, zorder=5,
        )


def decorate_axis(ax, title):
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlim(0.0, 10.8)
    ax.set_ylim(-0.72, 4.92)
    ax.set_axis_off()
    ax.set_title(title, loc="left", pad=14, fontsize=15, weight="semibold", color=INK)
    for row, y in [(1, 4), (2, 3), (3, 2), (4, 1)]:
        ax.text(0.72, y, str(row), ha="right", va="center", fontsize=11, color=MUTED)
    ax.text(0.72, 0, "1*", ha="right", va="center", fontsize=11, color=MUTED)
    ax.add_patch(
        FancyArrowPatch(
            (0.32, 0.08), (0.32, 3.92), arrowstyle="<->",
            mutation_scale=10, color="#7a8d9b", linewidth=1.0,
        )
    )
    ax.text(
        0.11, 2, "identified", rotation=90, ha="center", va="center",
        fontsize=9.5, color=MUTED,
    )
    for column in range(1, 7):
        ax.text(column, -0.32, str(column), ha="center", va="top", fontsize=10, color=MUTED)
    ax.text(3.5, -0.65, "vertex columns", ha="center", va="center", fontsize=9.5, color=MUTED)


def callout(ax, x, y, headline, body):
    ax.text(x, y, headline, ha="left", va="top", fontsize=13, weight="semibold", color=INK)
    ax.text(x, y - 0.42, body, ha="left", va="top", fontsize=11, linespacing=1.55, color=MUTED)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=Path(__file__).with_name("figure-splice-m4-data.json"))
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).parent)
    args = parser.parse_args()
    raw = args.data.read_bytes()
    if hashlib.sha256(raw).hexdigest() != DATA_SHA256:
        raise SystemExit("Refusing to render: input JSON differs from the frozen figure data.")
    data = json.loads(raw)
    assert data["coordinates"]["row_count"] == 4
    assert data["provenance"]["source_sha256"] == PROOF_SHA256
    assert data["verification_summary"]["all_checks_passed"] is True
    proof = args.data.with_name(PROOF_NAME)
    if proof.exists():
        assert hashlib.sha256(proof.read_bytes()).hexdigest() == PROOF_SHA256

    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 11,
        "svg.fonttype": "path",  # portable, consistent glyphs in exported SVG
        "svg.hashsalt": DATA_SHA256,
        "axes.unicode_minus": True,
        "savefig.facecolor": "white",
    })
    fig = plt.figure(figsize=(10.4, 11.6), facecolor="white")
    grid = fig.add_gridspec(2, 1, left=0.035, right=0.975, top=0.88, bottom=0.19, hspace=0.32)
    before, after = fig.add_subplot(grid[0]), fig.add_subplot(grid[1])

    fig.text(
        0.055, 0.964, "Joining two Hamiltonian cycles on a cylinder",
        ha="left", va="top", fontsize=19, weight="semibold", color=INK,
    )
    fig.text(
        0.055, 0.930, r"One explicit $m=4$ construction  ·  window bits are supports, not $B$ labels",
        ha="left", va="top", fontsize=10.8, color=MUTED,
    )

    removed = frozenset(key(e) for e in data["splice"]["deleted_edges_global"])
    added = frozenset(key(e) for e in data["splice"]["added_edges_global"])

    decorate_axis(before, "A   Before: two noncontractible cycles")
    for name in ["H1", "H2_rotated"]:
        graph = data["graphs"][name]
        draw_windows(before, graph)
        draw_selected_edges(before, graph, removed=removed)
        draw_vertices(before, graph)
    before.text(2, 4.55, r"$H_1$ · type 1", ha="center", va="center", fontsize=11.5, color=INK)
    before.text(5, 4.55, r"$H_2$ · rotated $-1$ row · type 1", ha="center", va="center", fontsize=11.0, color=INK)
    callout(before, 6.7, 3.92, "Two cycles", "12 vertices each\nLeft caps: 0 and 0\nRight caps: 1 and 1")
    callout(before, 6.7, 1.45, "Remove two edges", "The red vertical edges\nare both at row gap 1.")

    decorate_axis(after, "B   After: one contractible cycle")
    graph = data["graphs"]["joined"]
    draw_windows(after, graph)
    draw_selected_edges(after, graph, added=added)
    draw_vertices(after, graph)
    after.text(3.5, 4.55, r"Joined cycle · type $1\oplus1=0$", ha="center", va="center", fontsize=11.5, color=INK)
    callout(after, 6.7, 3.92, "One cycle", "24 vertices\nLeft cap: 0\nRight cap: 0")
    callout(after, 6.7, 1.45, "Add two seam edges", "Gold joins rows 1 and 2.\nGold at row 1* below\nis the row-1 copy.")

    handles = [
        Patch(facecolor=POSITIVE, edgecolor=GRID, label="support 1"),
        Patch(facecolor=ZERO, edgecolor=GRID, label="support 0"),
        Line2D([], [], color=INK, linewidth=2.5, label="selected edge"),
        Line2D([], [], color=RED, linewidth=2.8, linestyle=REMOVED_DASH, label="removed edge"),
        Line2D([], [], color=GOLD, linewidth=3.0, label="new seam edge"),
    ]
    fig.legend(
        handles=handles, loc="lower left", bbox_to_anchor=(0.055, 0.128),
        ncol=3, frameon=False, fontsize=10.3, handlelength=2.5,
        columnspacing=2.1, labelspacing=0.9, borderaxespad=0,
    )
    fig.text(
        0.055, 0.090,
        "The top and bottom row 1 are identified: 1* is a repeated drawing, not another row.\n"
        "Dashed horizontals at 1* copy the top edges; the gold copy is not a third added edge.\n"
        "The blank gap before the join is not a window. Only the after panel has seam windows.",
        ha="left", va="top", fontsize=10.2, linespacing=1.5, color=MUTED,
    )

    description = (
        "One hand-specified m=4 splice, not an enumeration. Two 3-column "
        "noncontractible Hamiltonian cycles join to one 6-column contractible "
        "cycle. H2 is rotated -1 row. The two vertical edges at row gap 1 are "
        "removed, and seam horizontals at rows 1 and 2 are added. Window fills "
        "show canonical binary supports with left cap 0; they are not B labels. "
        "Top and bottom displayed row 1 are identified; bottom dashed edges "
        "are copies. Data SHA256: " + DATA_SHA256 + ". Source proof SHA256: " + PROOF_SHA256 + "."
    )
    args.output_dir.mkdir(parents=True, exist_ok=True)
    svg_path = args.output_dir / (OUTPUT_STEM + ".svg")
    png_path = args.output_dir / (OUTPUT_STEM + ".png")
    fig.savefig(
        svg_path, format="svg", bbox_inches="tight", pad_inches=0.14,
        metadata={
            "Title": "Direct cylinder splice: one explicit m=4 example",
            "Description": description,
            "Creator": "/root/grid_proof_review; rendered from pinned explicit data",
            "Date": "2026-11-25",
            "Identifier": "sha256:" + DATA_SHA256,
        },
    )
    fig.savefig(
        png_path, format="png", dpi=220, bbox_inches="tight", pad_inches=0.14,
        metadata={
            "Title": "Direct cylinder splice: one explicit m=4 example",
            "Description": description,
            "SourceDataSHA256": DATA_SHA256,
            "SourceProofSHA256": PROOF_SHA256,
            "Creation Time": "2026-11-25",
        },
    )
    plt.close(fig)
    for path in [svg_path, png_path]:
        contents = path.read_bytes()
        print(json.dumps({"path": str(path.resolve()), "bytes": len(contents), "sha256": hashlib.sha256(contents).hexdigest()}))


if __name__ == "__main__":
    main()
