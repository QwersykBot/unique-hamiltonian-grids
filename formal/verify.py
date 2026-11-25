#!/usr/bin/env python3
"""Build the pinned Lean project and audit the exact named supporting results."""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
MATHLIB_COMMIT = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
MATHLIB_MANIFEST = "5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752"
MODULES = (
    "CylinderSplice",
    "TriangularCylinder",
    "TriangularParity",
    "MatrixContraction.Basic",
    "MatrixContraction.Limits",
    "MatrixContraction.PositiveBlocks",
    "EnumeratedWalk",
    "MeridianClassifier",
    "AuxiliaryCycle",
    "EdgeCoboundary",
    "MatrixContraction.OrderedApplication",
    "RowRotation",
    "SelectedEdgePresentation",
    "SelectedCylinderSplice",
    "ConnectedTwoRegular",
    "FrontierSubstitution",
    "FrontierAttachment",
    "FrontierCongruence",
    "ColumnCut",
    "TwoColumnWitness",
    "ThreeColumnWitness",
    "TwoColumnWitnessCut",
    "ThreeColumnWitnessCut",
    "FiniteTransfer",
    "AcceptedRatio",
    "PhysicalEdges",
    "GenericEdgeWeights",
    "CountedHamiltonian",
    "SelectedCharacterization",
    "SelectedIff",
    "BoundaryState",
    "ColumnFragments",
    "ColumnCutOutgoing",
    "CommonWitnessState",
    "ExceptionalState",
    "ColumnGeometry",
    "ColumnHamiltonian",
    "ColumnWeights",
    "ZigzagException",
    "ColumnEmbedding",
    "CycleSaturation",
    "FullCrossing",
    "FrontierDegrees",
    "FrontierDegreesGeneral",
    "EdgeReplacementReachability",
    "ColumnBoundaryDegree",
    "BoundaryVertical",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_AUDITS = set("""
CylinderSplice.splice_cycles_isHamiltonianCycle
CylinderSplice.splice_edgeSet
CylinderSplice.splice_edgeWeight
TriangularCylinder.spliceAt_isHamiltonianCycle
TriangularCylinder.spliceAt_typeParity
EnumeratedWalk.ofFnWalk_support
EnumeratedWalk.ofFnWalk_edges
EnumeratedWalk.ofFnWalk_isHamiltonian
EnumeratedWalk.ofFnCycle_isHamiltonianCycle
EnumeratedWalk.mem_ofCyclicEnumeration_edges
EnumeratedWalk.ofCyclicEnumeration_isHamiltonianCycle
TriangularCylinder.nextRow_cases
TriangularCylinder.nextRow_last_first
TriangularCylinder.nextRow_target_first_of_source_last
TriangularCylinder.nextRow_source_last_iff_target_first
TriangularCylinder.nextRow_pair_eq_meridian_iff
TriangularCylinder.meridianWeight_nextRow
TriangularCylinder.meridianWeight_last_first
TriangularCylinder.auxiliaryCycle_isHamiltonianCycle
TriangularCylinder.auxiliaryCycle_typeParity
TriangularCylinder.auxiliaryCycle_left_edges_iff
TriangularCylinder.auxiliaryCycle_right_edges_iff
TriangularCylinder.exists_three_column_auxiliary
EdgeCoboundary.edgeWeight_change
EdgeCoboundary.edgeWeight_eq_of_closed
TriangularCylinder.typeParity_shift
TriangularCylinder.exists_row_avoiding_two
TriangularCylinder.exists_aligned_three_column_auxiliary
CylinderMatrixContraction.subtract_constant_mulVec
CylinderMatrixContraction.single_block_contraction
CylinderMatrixContraction.ordered_product_contraction
CylinderMatrixContraction.endpoint_contraction
CylinderMatrixContraction.probability_deviation_bound
CylinderMatrixContraction.ratio_deviation_bound
CylinderMatrixContraction.ratio_tendsto_one_of_imbalance
CylinderMatrixContraction.matrix_family_ratio_tendsto_one
CylinderMatrixContraction.bulk_block_count_tendsto
CylinderMatrixContraction.matrix_pow_add_entry_pos
CylinderMatrixContraction.returns_of_lengths_two_three
CylinderMatrixContraction.eventual_positive_powers
CylinderMatrixContraction.matrix_pow_le_list_prod
CylinderMatrixContraction.matrix_list_prod_le_pow
CylinderMatrixContraction.scaled_matrix_pow_apply
CylinderMatrixContraction.uniform_positive_blocks_of_support
CylinderMatrixContraction.fullChunks_length
CylinderMatrixContraction.fullChunks_flatten_append_drop
CylinderMatrixContraction.fullChunks_spec
CylinderMatrixContraction.chunkProducts_length
CylinderMatrixContraction.factorResidual_length_lt
CylinderMatrixContraction.chunkProducts_mul_residual
CylinderMatrixContraction.symmetricUnder_mul
CylinderMatrixContraction.symmetricUnder_list_prod
CylinderMatrixContraction.uniform_finite_imbalance_of_support
CylinderMatrixContraction.ordered_factor_family_ratio_tendsto_one
SelectedEdgePresentation.isHamiltonianCycle_append_swap
SelectedEdgePresentation.isHamiltonianCycle_reverse
SelectedEdgePresentation.exists_edge_first
SelectedEdgePresentation.exists_edge_first_with_weight
TriangularCylinder.exists_splice_of_selected_edges
ConnectedTwoRegular.exists_isHamiltonianCycle_at_of_neighbor_ncard_two
ConnectedTwoRegular.exists_isHamiltonianCycle_of_neighbor_ncard_two
ConnectedTwoRegular.exists_isHamiltonianCycle_of_degree_two
CylinderFrontier.glue_preconnected_iff
CylinderFrontier.glue_connected_iff
CylinderFrontier.boundary_reachable_of_glue_reachable
CylinderFrontier.touchesBoundary_of_glue_preconnected
CylinderFrontier.touchesBoundary_of_glue_connected
CylinderFrontier.touchesBoundary_of_glue_connected_of_nonempty_boundary
CylinderFrontier.glue_connected_swap
CylinderFrontier.suffix_touchesBoundary_of_glue_connected
CylinderFrontier.both_touchBoundary_of_glue_connected
CylinderFrontier.glue_suffix_reachable_iff
CylinderFrontier.boundaryGraph_adj
CylinderFrontier.boundaryGraph_reachable
CylinderFrontier.compressedPrefix_reachable
CylinderFrontier.touchesBoundary_compressedPrefix
CylinderFrontier.glue_suffix_reachable_iff_compressedPrefix
TriangularCylinder.ColumnCut.ofVertex_toVertex
TriangularCylinder.ColumnCut.toVertex_ofVertex
TriangularCylinder.ColumnCut.vertexEquiv_row
TriangularCylinder.ColumnCut.suffixPart_no_boundary_edges
TriangularCylinder.ColumnCut.prefixPart_boundary_adj
TriangularCylinder.ColumnCut.adj_column_distance_le_one
TriangularCylinder.ColumnCut.no_interior_suffix_edge
TriangularCylinder.ColumnCut.glue_parts_eq_comap
TriangularCylinder.ColumnCut.glue_parts_connected
TriangularCylinder.ColumnCut.prefixPart_touchesBoundary
TriangularCylinder.ColumnCut.both_parts_touchBoundary
CountedHamiltonian.selection_has_presentation
CountedHamiltonian.presentationSelection_surjective
CountedHamiltonian.ofCycle_eq_iff
CountedHamiltonian.selection_edge_mem
CountedHamiltonian.selection_card
CountedHamiltonian.selection_three_le_card
CountedHamiltonian.selectionWeight_ofCycle
TriangularCylinder.selectionParity_ofCycle
TriangularCylinder.parityCount_partition
TriangularCylinder.perimeterCycle_isHamiltonianCycle
TriangularCylinder.perimeterCycle_typeParity
TriangularCylinder.perimeterCycle_left_join_edge
TriangularCylinder.perimeterCycle_right_join_edge
TriangularCylinder.perimeterCycle_lastCut_edges_iff
TriangularCylinder.perimeterPrefixWalk_isPath
TriangularCylinder.perimeterPrefixWalk_support_iff
TriangularCylinder.perimeterPrefixWalk_edges
TriangularCylinder.perimeterPrefixWalk_edges_in_cycle
TriangularCylinder.perimeterPrefixWalk_pair_edges_iff
TriangularCylinder.perimeterPrefixWalk_typeParity
TriangularCylinder.exists_two_column_zero_witness
TriangularCylinder.threeWitnessCycle_isHamiltonianCycle
TriangularCylinder.threeWitnessCycle_typeParity
TriangularCylinder.threeWitnessCycle_left_join_edge
TriangularCylinder.threeWitnessCycle_right_join_edge
TriangularCylinder.threeWitnessCycle_lastCut_edges_iff
TriangularCylinder.threePrefixWalk_isPath
TriangularCylinder.threePrefixWalk_support_iff
TriangularCylinder.threePrefixWalk_edges
TriangularCylinder.threePrefixWalk_edges_in_cycle
TriangularCylinder.threePrefixWalk_pair_edges_iff
TriangularCylinder.threePrefixWalk_typeParity
TriangularCylinder.exists_three_column_zero_witness
TriangularCylinder.threePrefixVertex_first
TriangularCylinder.threePrefixVertex_last
CylinderTransfer.transitionMatrix_apply
CylinderTransfer.card_labelledPath_zero
CylinderTransfer.card_labelledPath_succ
CylinderTransfer.card_labelledPath
CylinderTransfer.realTransitionMatrix_pow
CylinderTransfer.card_labelledPath_real
CylinderTransfer.card_accepted
CylinderTransfer.card_accepted_zero
CylinderTransfer.card_accepted_real
CylinderTransfer.realTransitionMatrix_pow_pos_iff
CylinderTransfer.card_accepted_pos_of_positive_power
CylinderTransfer.eventually_card_accepted_pos
CylinderTransfer.accepted_ratio_limit
CountedHamiltonian.coe_selectedEdges
CountedHamiltonian.selectedEdges_eq_of_edgeSet_eq
CountedHamiltonian.edgeWeight_eq_sum_selectedEdges
CountedHamiltonian.edgeWeight_eq_of_selectedEdges_eq
CountedHamiltonian.edgeWeight_eq_of_edgeSet_eq
CountedHamiltonian.hamiltonianCycle_edgeWeight_eq_of_selectedEdges_eq
CountedHamiltonian.hamiltonianCycle_edgeWeight_eq_of_edgeSet_eq
CountedHamiltonian.selection_eq_iff
TriangularCylinder.parity_eq_zero_or_one
TriangularEdgeEncoding.nextRow_rowSucc
TriangularEdgeEncoding.nextRow_asymm
TriangularEdgeEncoding.forward_col_le
TriangularEdgeEncoding.forward_asymm
TriangularEdgeEncoding.forward_source_target
TriangularEdgeEncoding.toEdge_mem_edgeSet
TriangularEdgeEncoding.toEdge_endpoints
TriangularEdgeEncoding.toEdge_injective
TriangularEdgeEncoding.exists_toEdge_of_forward
TriangularEdgeEncoding.exists_toEdge
TriangularEdgeEncoding.toGraphEdge_bijective
TriangularEdgeEncoding.edgeEquiv
TriangularEdgeEncoding.edgeEquiv_apply_val
CountedHamiltonian.walk_spanningCoe_edgeSet
CountedHamiltonian.fromEdgeSet_selectedEdges
CountedHamiltonian.hamiltonian_selected_connected
CountedHamiltonian.hamiltonian_selected_ncard
CountedHamiltonian.realization_selected_connected_two
CountedHamiltonian.selectedGraph_edgeSet
CountedHamiltonian.selectedGraph_le
CountedHamiltonian.hamiltonian_edgeSet_eq_of_ncard
CountedHamiltonian.selectedEdges_eq_of_hamiltonian_selected
CountedHamiltonian.selectedEdges_mapLe
CountedHamiltonian.realization_of_selected_hamiltonian
CountedHamiltonian.neighborSet_ncard_eq_degree
CountedHamiltonian.realization_iff_connected_two
CountedHamiltonian.realization_iff_connected_degree_two
CountedHamiltonian.realization_iff_subset_connected_two
TriangularCylinder.RawBoundaryState.finite
TriangularCylinder.RawBoundaryState.ext
TriangularCylinder.RawBoundaryState.flip_involutive
TriangularCylinder.RawBoundaryState.flip_ne
TriangularCylinder.BoundaryState.stateAt_horizontal_physical_iff
TriangularCylinder.BoundaryState.stateAt_diagonal_physical_iff
TriangularCylinder.BoundaryState.stateAt_horizontal_iff
TriangularCylinder.BoundaryState.stateAt_diagonal_iff
TriangularCylinder.BoundaryState.stateAt_reach_iff
TriangularCylinder.BoundaryState.stateAt_reach_refl
TriangularCylinder.BoundaryState.stateAt_reach_symm
TriangularCylinder.BoundaryState.stateAt_reach_trans
TriangularCylinder.BoundaryState.stateAt_reach_equivalence
TriangularCylinder.BoundaryState.stateAt_parity
TriangularCylinder.BoundaryState.mem_assignedIds
TriangularCylinder.BoundaryState.horizontalId_assigned_iff
TriangularCylinder.BoundaryState.diagonalId_assigned_iff
TriangularCylinder.BoundaryState.diagonal_target_not_prefix
TriangularCylinder.BoundaryState.cycle_selectedGraph_le
TriangularCylinder.BoundaryState.occurs_stateAt
TriangularCylinder.BoundaryState.actualState_finite
TriangularCylinder.ColumnFragments.forward_iff_of_coordinate_shift
TriangularCylinder.ColumnFragments.forward_prefix_iff
TriangularCylinder.ColumnFragments.forward_suffix_iff
TriangularCylinder.ColumnFragments.prefixVertex_adj_iff
TriangularCylinder.ColumnFragments.suffixVertex_adj_iff
TriangularCylinder.ColumnFragments.suffixAmbient_no_boundary_edges
TriangularCylinder.ColumnFragments.prefixPart_le_prefixAmbient
TriangularCylinder.ColumnFragments.suffixPart_le_suffixAmbient
TriangularCylinder.ColumnFragments.glue_permitted_le_comap
TriangularCylinder.ColumnFragments.transportedGlue_le
TriangularCylinder.ColumnFragments.mixed_cut_parts_le
TriangularCylinder.ColumnCut.suffixPart_boundary_geometry
TriangularCylinder.ColumnCut.suffixPart_boundary_adj_iff
TriangularCylinder.ColumnCut.suffixPart_boundary_adj_iff_masks
TriangularCylinder.ColumnCut.firstSuffix_horizontal_ne_diagonal
TriangularCylinder.ColumnCut.suffixPart_boundary_neighborSet
TriangularCylinder.ColumnCut.suffixPart_boundary_neighbor_ncard
TriangularCylinder.ColumnCut.suffixPart_boundary_neighbor_ncard_eq_of_masks_eq
TriangularCylinder.perimeterCycle_selected_edgeWeight_zero
TriangularCylinder.threeWitnessCycle_selected_edgeWeight_zero
TriangularCylinder.perimeterCycle_state_horizontal
TriangularCylinder.threeWitnessCycle_state_horizontal
TriangularCylinder.perimeterCycle_state_diagonal
TriangularCylinder.threeWitnessCycle_state_diagonal
TriangularCylinder.perimeterCycle_prefix_reachable
TriangularCylinder.threeWitnessCycle_prefix_reachable
TriangularCylinder.perimeterCycle_state_reach
TriangularCylinder.threeWitnessCycle_state_reach
TriangularCylinder.perimeterCycle_state_parity
TriangularCylinder.threeWitnessCycle_state_parity
TriangularCylinder.perimeterCycle_stateAt_common
TriangularCylinder.threeWitnessCycle_stateAt_common
TriangularCylinder.witness_states_eq
TriangularCylinder.commonWitnessState_occurs
TriangularCylinder.exceptional_prefixPart_eq_bot_of_no_vertical
TriangularCylinder.exceptional_assignedParity_of_no_vertical
TriangularCylinder.stateAt_eq_exceptional_of_physical_selection
TriangularCylinder.zigzag_physical_mem_iff
TriangularCylinder.zigzag_prefixPart_eq_bot
TriangularCylinder.zigzag_stateAt_exceptional
TriangularCylinder.zigzag_state_horizontal
TriangularCylinder.zigzag_state_diagonal
TriangularCylinder.zigzag_state_reach
TriangularCylinder.zigzag_state_parity
TriangularCylinder.exceptionalRawState_occurs
CycleSaturation.isHamiltonianCycle_of_neighbor_ncard_two
CycleSaturation.length_eq_card_of_neighbor_ncard_two
TriangularCutSaturation.FullCrossingAt
TriangularCutSaturation.columnShift
TriangularCutSaturation.columnShift_injective
TriangularCutSaturation.columnShift_left
TriangularCutSaturation.columnShift_right
TriangularCutSaturation.fullCrossingAt_of_masks
TriangularCutSaturation.length_two_of_fullCrossingAt
TriangularCutSaturation.length_two_of_full_crossing_masks
TriangularCutSaturation.not_full_crossing_masks
TriangularCutSaturation.selectedId_adj
TriangularCutSaturation.zigzagInto
TriangularCutSaturation.zigzagInto_injective
TriangularEdgeEncoding.HamiltonianGeometry
TriangularEdgeEncoding.IsHamiltonianGeometry
TriangularEdgeEncoding.columnSelectionEquiv
TriangularEdgeEncoding.columnSelectionEquiv_val
TriangularEdgeEncoding.existsUnique_geometry_of_edges
TriangularEdgeEncoding.exists_geometry_of_edges
TriangularEdgeEncoding.geometryEquiv
TriangularEdgeEncoding.geometryFlag_ofIds
TriangularEdgeEncoding.geometryOfIds_idsOfGeometry
TriangularEdgeEncoding.geometryOfIds_injective
TriangularEdgeEncoding.geometryParity
TriangularEdgeEncoding.geometryParityCount
TriangularEdgeEncoding.geometryParityCount_eq_parityCount
TriangularEdgeEncoding.geometryWeight
TriangularEdgeEncoding.geometry_realization_iff
TriangularEdgeEncoding.graphSelectionEquiv
TriangularEdgeEncoding.graphSelectionEquiv_val
TriangularEdgeEncoding.hamiltonianSelectionEquiv
TriangularEdgeEncoding.hamiltonianSelectionEquiv_val
TriangularEdgeEncoding.idsOfGeometry_geometryOfIds
TriangularEdgeEncoding.idsOfGeometry_injective
TriangularEdgeEncoding.instFintypeHamiltonianGeometry
TriangularEdgeEncoding.mem_idsOfGeometry
TriangularEdgeEncoding.meridianWeight_toEdge_diagonal
TriangularEdgeEncoding.meridianWeight_toEdge_horizontal
TriangularEdgeEncoding.meridianWeight_toEdge_vertical
TriangularEdgeEncoding.parityGeometryEquiv
TriangularEdgeEncoding.realizedEdges_injective
TriangularEdgeEncoding.realizedEdges_mem
TriangularEdgeEncoding.selectionParity_hamiltonianSelectionEquiv
TriangularEdgeEncoding.selectionWeight_hamiltonianSelectionEquiv
TriangularEdgeEncoding.sum_idsOfGeometry_eq_column_cut
TriangularEdgeEncoding.sum_idsOfGeometry_eq_flagSum
TriangularEdgeEncoding.sum_idsOfGeometry_eq_vhd
TriangularEdgeEncoding.sum_idsOfGeometry_filter_le_eq_column_cut
TriangularEdgeEncoding.sum_idsOfGeometry_filter_le_eq_vhd
TriangularEdgeEncoding.sum_idsOfGeometry_filter_le_meridian_eq_lastRow
TriangularEdgeEncoding.sum_idsOfGeometry_meridian_eq_lastRow
TriangularEdgeEncoding.sum_masked_singleton_row
TriangularEdgeEncoding.sum_realizedEdges_eq_column_cut
TriangularEdgeEncoding.sum_realizedEdges_eq_selectedIds
TriangularEdgeEncoding.sum_realizedEdges_meridian_eq_lastRow
TriangularZigzag.adj_left
TriangularZigzag.adj_right
TriangularZigzag.connected
TriangularZigzag.diagonal_toEdge
TriangularZigzag.exists_selectedGraph_isHamiltonianCycle
TriangularZigzag.geometryParity_eq_one
TriangularZigzag.hasHamiltonianRealization
TriangularZigzag.horizontal_toEdge
TriangularZigzag.isHamiltonianGeometry
TriangularZigzag.mem_realizedEdges
TriangularZigzag.neighborSet_left
TriangularZigzag.neighborSet_ncard_two
TriangularZigzag.neighborSet_right
TriangularZigzag.reachable_left
TriangularZigzag.rowSucc_injective
TriangularZigzag.selectedGraph_adj
TriangularZigzag.selection
TriangularZigzag.selectionParity_eq_one
TriangularZigzag.selection_val
CylinderFrontier.glue_prefix_neighbor_ncard
CylinderFrontier.glue_suffix_neighbor_ncard
CylinderFrontier.glue_boundary_neighbor_ncard
CylinderFrontier.glue_neighbor_ncard_two
CylinderFrontier.glue_boundary_neighbor_ncard_of_no_shared_boundary
CylinderFrontier.glue_boundary_neighbor_ncard_of_suffix_no_boundary
CylinderFrontier.glue_neighbor_ncard_two_of_no_shared_boundary
CylinderFrontier.glue_neighbor_ncard_two_of_suffix_no_boundary
CylinderFrontier.EdgeReplacement.old_reachable_iff
CylinderFrontier.EdgeReplacement.gadget_reaches_left
TriangularCylinder.ColumnCut.glue_parts_neighbor_ncard
TriangularCylinder.ColumnCut.prefixPart_interior_neighbor_ncard
TriangularCylinder.ColumnCut.suffixPart_interior_neighbor_ncard
TriangularCylinder.ColumnCut.parts_boundary_neighbor_ncard_sum
TriangularCylinder.ColumnCut.prefixPart_boundary_neighbor_ncard_eq_of_masks_eq
TriangularCylinder.ColumnCut.mixed_parts_neighbor_ncard_two
TriangularCylinder.BoundaryVertical.first_neighbors_eq_of_no_vertical
TriangularCylinder.BoundaryVertical.second_neighbors_eq_of_no_vertical
TriangularCylinder.BoundaryVertical.first_crossings_selected_of_no_vertical
TriangularCylinder.BoundaryVertical.last_neighbors_eq_of_no_vertical
TriangularCylinder.BoundaryVertical.penultimate_neighbors_eq_of_no_vertical
TriangularCylinder.BoundaryVertical.last_crossings_selected_of_no_vertical
TriangularCylinder.BoundaryVertical.exists_first_selected_vertical
TriangularCylinder.BoundaryVertical.exists_last_selected_vertical
TriangularCylinder.BoundaryVertical.exists_selected_verticals_at_both_ends
""".split())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def verify_snapshot() -> dict[str, str]:
    """Check every manifested file and the exact local proof-source inventory."""
    manifest = json.loads((ROOT.parent / "manifest.json").read_text())
    for relative, expected in manifest["files"].items():
        path = (ROOT.parent / relative).resolve()
        path.relative_to(ROOT.parent)
        data = path.read_bytes()
        require(len(data) == expected["bytes"] and sha256(data) == expected["sha256"],
                "Snapshot mismatch: " + relative)
    sources = {source_path(module) for module in (*MODULES, "ProofAudit")}
    observed = set(ROOT.glob("*.lean")) | set((ROOT / "MatrixContraction").glob("*.lean"))
    require(observed == sources, "Unexpected or missing local Lean source")
    pins = {}
    for path in sorted(sources):
        relative = str(path.relative_to(ROOT.parent))
        require(relative in manifest["files"], "Unmanifested proof source: " + relative)
        data = path.read_bytes()
        require(not re.search(rb"\b(sorry|admit|axiom|native_decide|unsafe)\b", data),
                "Disallowed proof token in " + relative)
        pins[str(path.relative_to(ROOT))] = sha256(data)
    provenance = json.loads((ROOT / "provenance.json").read_text())
    expected = {str(source_path(module).relative_to(ROOT)) for module in MODULES}
    require(set(provenance["copied_sources"]) == expected, "Incomplete source provenance")
    for name, record in provenance["copied_sources"].items():
        require(pins[name] == record["packaged_sha256"], "Provenance mismatch: " + name)
    return pins


def parse_audits(output: str) -> dict[str, list[str]]:
    pattern = re.compile(
        r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",
        re.MULTILINE,
    )
    matches = list(pattern.finditer(output))
    require(not pattern.sub("", output).strip(), "Unexpected axiom-audit output")
    audits = {match[1]: sorted(x.strip() for x in (match[2] or "").split(",") if x.strip())
              for match in matches}
    require(len(matches) == len(EXPECTED_AUDITS) and set(audits) == EXPECTED_AUDITS,
            "Missing, duplicate, or unexpected axiom-audit declaration")
    for name, axioms in audits.items():
        require(set(axioms) <= ALLOWED_AXIOMS, "Unapproved axiom dependency: " + name)
    return audits


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable for the pinned Lean toolchain")
    parser.add_argument("--fetch-cache", action="store_true",
                        help="Download Mathlib's official compiled cache for the direct imports")
    args = parser.parse_args()
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    receipt = {
        "status": "RUNNING",
        "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Named supporting lemmas; neither cylinder asymptotic theorem is fully formalized.",
        "commands": [],
    }

    def run(command: list[str], cwd: Path = ROOT) -> str:
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                capture_output=True, timeout=1200)
        receipt["commands"].append({
            "command": command, "exit_code": result.returncode,
            "stdout_sha256": sha256(result.stdout.encode()),
            "stderr_sha256": sha256(result.stderr.encode()),
        })
        require(result.returncode == 0,
                "Command failed: " + " ".join(command) + "\n" + result.stdout + result.stderr)
        return result.stdout

    def verify_dependencies() -> dict[str, str]:
        packages = ROOT / ".lake/packages"
        mathlib = packages / "mathlib"
        require(sha256((mathlib / "lake-manifest.json").read_bytes()) == MATHLIB_MANIFEST,
                "Unexpected Mathlib dependency manifest")
        upstream = json.loads((mathlib / "lake-manifest.json").read_text())
        expected = {p["name"]: p["rev"] for p in upstream["packages"]}
        expected["mathlib"] = MATHLIB_COMMIT
        local = json.loads((ROOT / "lake-manifest.json").read_text())
        require({p["name"]: p["rev"] for p in local["packages"]} == expected,
                "Local dependency pins differ from the reviewed pins")
        for name, commit in expected.items():
            checkout = packages / name
            require(run(["git", "rev-parse", "HEAD"], checkout).strip() == commit,
                    "Wrong dependency commit: " + name)
            require(not run(["git", "status", "--porcelain", "--untracked-files=no"], checkout).strip(),
                    "Modified tracked dependency source: " + name)
        return expected

    try:
        require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.19.0",
                "Unexpected Lean toolchain declaration")
        version = run([args.lake, "env", "lean", "--version"]).strip()
        require("version 4.19.0," in version and "commit 6caaee842e94" in version,
                "Unexpected Lean version or compiler commit")
        receipt["lean_version"] = version
        receipt["source_sha256"] = verify_snapshot()
        receipt["dependency_commits"] = verify_dependencies()
        if args.fetch_cache:
            imports = sorted({name for module in MODULES
                              for name in re.findall(r"^import (Mathlib\.[\w.]+)$",
                                                     source_path(module).read_text(), re.MULTILINE)})
            run([args.lake, "exe", "cache", "get", *imports])
        print("Building the pinned project with warnings treated as errors.", flush=True)
        run([args.lake, "build"])
        output = run([args.lake, "env", "lean", "-DwarningAsError=true", "ProofAudit.lean"])
        receipt["axiom_audit"] = parse_audits(output)
        receipt["dependency_commits"] = verify_dependencies()
        receipt["compiled_object_sha256"] = {
            module: sha256((ROOT / ".lake/build/lib/lean" /
                            (module.replace(".", "/") + ".olean")).read_bytes())
            for module in (*MODULES, "ProofAudit")
        }
        receipt["status"] = "PASS"
        print(version)
        print(f"PASS: {len(MODULES)} supporting modules; {len(EXPECTED_AUDITS)} exact named audits; "
              "standard logical axioms only.")
        print("Full cylinder counting correspondence and asymptotic theorems remain unformalized.")
        return 0
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
        receipt["status"] = "FAIL"
        receipt["error"] = str(error)
        print(str(error), file=sys.stderr)
        return 1
    finally:
        (ROOT / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    raise SystemExit(main())
