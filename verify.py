"""Check snapshot identity, finite evidence, and optimized-mode rejection."""

if not __debug__:
    raise SystemExit(
        "Verification requires assertions. Rerun without -O/-OO and unset PYTHONOPTIMIZE."
    )

import hashlib
import json
from pathlib import Path
import subprocess
import sys

if sys.version_info < (3, 10):
    raise SystemExit("Python 3.10 or later is required for the supplied checks.")


ROOT = Path(__file__).resolve().parent
PROOF = "grid_width_classification.md"
PROOF_SHA256 = "3b325dfe8d0e874bf2202fe8b086e3f4a5f84013d5d4720d75d2f5d8c3402fd1"
REVIEWED_SOURCES = {
    PROOF: PROOF_SHA256,
    "four_n_cutoff.md": "a5608581586c614c9e219666a5caac5fcc5b7c5a15f8ef29ddac4b68bf06944b",
    "eventual_exact_optimum.md": "13445aefa748d7ec3c593833db3854ed73aaa863b1e1fff96127df4cc87afc6b",
    "two_k_construction.md": "52f61a99433bca3f94409d3df493982a22731393dd1e5394d04b46bfbe2f5c07",
    "polynomial_cutoff.md": "46ab4d73958ff6b46aa49c2362e7ee446903388e5c13c79b5f776378bb266453",
}
OPTIMIZED_MESSAGE = "Verification requires assertions."
CHECKS = (
    ("checks/check_geometry.py", "results/geometry.json"),
    ("checks/check_graph_lemma.py", "results/graph_lemma.json"),
    ("checks/check_upper_construction.py", "results/upper_construction.json"),
    ("checks/check_reverse_geometry.py", "results/reverse_geometry.json"),
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_json(relative):
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def verify_manifest():
    manifest = read_json("manifest.json")
    require(manifest["proof_sha256"] == PROOF_SHA256, "Unexpected proof identity in manifest")
    require(manifest["reviewed_sources_sha256"] == REVIEWED_SOURCES,
            "Unexpected reviewed-source identities in manifest")
    for relative, expected in manifest["files"].items():
        path = (ROOT / relative).resolve()
        path.relative_to(ROOT)
        data = path.read_bytes()
        require(len(data) == expected["bytes"], relative + ": size mismatch")
        require(hashlib.sha256(data).hexdigest() == expected["sha256"],
                relative + ": SHA256 mismatch")
    for relative, expected in REVIEWED_SOURCES.items():
        require(relative in manifest["files"], relative + ": missing from manifest")
        require(hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == expected,
                relative + ": reviewed mathematical source has changed")
    return len(manifest["files"])


def verify_check(script, pinned):
    completed = subprocess.run(
        [sys.executable, str(ROOT / script)],
        cwd=ROOT, capture_output=True, text=True,
    )
    require(completed.returncode == 0,
            script + " failed:\n" + completed.stderr + completed.stdout)
    observed = json.loads(completed.stdout)
    require(observed.get("status") == "PASS", script + ": missing PASS result")
    require(observed == read_json(pinned), script + ": output differs from pinned result")
    return "PASS"


def verify_optimized_rejection():
    rejected = []
    for script in ("verify.py", *(script for script, _ in CHECKS),
                   "checks/independent_cycle_counter.py"):
        completed = subprocess.run(
            [sys.executable, "-O", str(ROOT / script)],
            cwd=ROOT, capture_output=True, text=True,
        )
        require(completed.returncode != 0 and OPTIMIZED_MESSAGE in completed.stderr,
                script + ": optimized execution was not explicitly rejected")
        rejected.append(script)
    return rejected


def main():
    count = verify_manifest()
    results = {script: verify_check(script, pinned) for script, pinned in CHECKS}
    optimized = verify_optimized_rejection()
    print(json.dumps({
        "status": "PASS",
        "proof_sha256": PROOF_SHA256,
        "reviewed_sources_sha256": REVIEWED_SOURCES,
        "manifest_files_checked": count,
        "finite_checks_match_pinned_results": results,
        "optimized_mode_rejected": optimized,
        "scope": "Snapshot integrity and finite checks; not formal verification of the universal theorem.",
    }, indent=2))


if __name__ == "__main__":
    main()
