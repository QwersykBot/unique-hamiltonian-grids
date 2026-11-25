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
    "CylinderSplice", "TriangularCylinder", "TriangularParity", "EnumeratedWalk",
    "MeridianClassifier", "AuxiliaryCycle", "EdgeCoboundary", "RowRotation",
    "MatrixContraction.Basic", "MatrixContraction.Limits",
    "MatrixContraction.PositiveBlocks", "MatrixContraction.OrderedApplication",
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
