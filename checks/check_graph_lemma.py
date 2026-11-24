"""Independent finite falsification check for the proof's abstract graph lemma.

No grid transfer, certificate, or earlier checker is imported. All arithmetic
counts walks in the saturating semiring {0,1,2}, with 2 meaning at least two.
The finite check supplements the mathematical proof and cannot establish it.
"""

if not __debug__:
    raise SystemExit(
        "Verification requires assertions. Rerun without -O/-OO and unset PYTHONOPTIMIZE."
    )


from itertools import product
from pathlib import Path
import hashlib
import json


def deterministic_cyclic_sccs(matrix):
    n = len(matrix)
    reach = [[i == j or matrix[i][j] > 0 for j in range(n)] for i in range(n)]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                reach[i][j] |= reach[i][k] and reach[k][j]
    remaining = set(range(n))
    answer = []
    while remaining:
        i = min(remaining)
        component = {j for j in remaining if reach[i][j] and reach[j][i]}
        remaining -= component
        cyclic = len(component) > 1 or matrix[i][i] > 0
        if cyclic and all(sum(matrix[v][w] for w in component) == 1
                          for v in component):
            answer.append(sorted(component))
    return answer


def multiply(a, b):
    n = len(a)
    return [[min(2, sum(a[i][k] * b[k][j] for k in range(n)))
             for j in range(n)] for i in range(n)]


def power(a, exponent):
    n = len(a)
    result = [[int(i == j) for j in range(n)] for i in range(n)]
    while exponent:
        if exponent & 1:
            result = multiply(result, a)
        a = multiply(a, a)
        exponent //= 2
    return result


def check_family(n, multiplicities):
    tested = 0
    without_deterministic_scc = 0
    for flat in product(multiplicities, repeat=n*n):
        a = [list(flat[i*n:(i+1)*n]) for i in range(n)]
        deterministic = deterministic_cyclic_sccs(a)
        tested += 1
        if not deterministic:
            without_deterministic_scc += 1
            assert not any(value == 1 for row in power(a, 2*n*n)
                           for value in row), a
        else:
            # A return walk cannot leave its SCC and later return. At multiples
            # of its cycle length the corresponding diagonal count must be one.
            for component in deterministic:
                length = len(component)
                count = power(a, length * (2*n*n + 1))
                assert all(count[v][v] == 1 for v in component), a
    return {"vertices": n, "allowed_edge_multiplicities": list(multiplicities),
            "graphs_checked": tested,
            "graphs_without_deterministic_cyclic_scc": without_deterministic_scc,
            "counterexamples": 0}


if __name__ == "__main__":
    results = [check_family(1, (0, 1, 2)),
               check_family(2, (0, 1, 2)),
               check_family(3, (0, 1, 2))]
    result = {"status": "PASS", "families": results,
              "graphs_checked": sum(r["graphs_checked"] for r in results),
              "scope": "Every directed multigraph on 1, 2, or 3 labeled vertices with each edge multiplicity in {0,1,2}, including self-loops.",
              "limits": "Finite falsification check only; the universal theorem relies on the separately reviewed written argument.",
              "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2))
