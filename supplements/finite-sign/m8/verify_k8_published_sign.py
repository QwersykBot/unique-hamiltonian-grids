#!/usr/bin/env python3
"""Exact all-length sign certificate for the published K_8 rational function.

Python standard library only. Source: Bodroza-Pantic, Kwong, Pantic,
DMTCS 17:1 (2015), printed p. 235, Section 6.7:
https://dmtcs.episciences.org/en/articles/2113/download

The graph-count identification is the original paper's stated formula.
The algebraic proof and its finite integer premises are explained in
K8-published-sign-proof.txt. No numerical roots or extrapolation are used.
"""

import hashlib
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Run without -O, -OO, or PYTHONOPTIMIZE.")

# Direct transcription of r_8(x) and s_8(x), coefficients in ascending order.
# The printed numerator is twice a polynomial; the factor 2 is included here.
ORIGINAL_NUMERATOR = [
    6, -160, 952, -2286, 606, 9834, -17340, -4582, 38954, -26630,
    -33560, 38448, 12206, -19948, -2704, 7852, -3592, 1288, -336, 32,
]
ORIGINAL_DENOMINATOR = [
    1, 5, -104, 529, -1548, 1830, 3915, -13527, 7182, 20914,
    -31027, -9214, 35037, 1205, -19590, 890, 5770, -2048, 588, -184, 16,
]

# Separate transcription of the fifteen coefficients printed for H_8^c and
# H_8^nc on the same page. Entry k counts cycles with k+2 vertex columns.
PRINTED_CONTRACTIBLE = [
    8, 64, 4320, 44288, 1575288, 22337664, 605992784, 10215798448,
    242178636928, 4475508186384, 98989761676840, 1920787160180224,
    40975264449253872, 815884428197037360, 17077909293201385648,
]
PRINTED_NONCONTRACTIBLE = [
    2, 254, 1794, 82138, 1012930, 30717374, 481369234, 12070287370,
    214585144402, 4886085696654, 92880601782338, 2011688161424970,
    39622707294281746, 836009740378418718, 16778455639135020178,
]


def substitute_minus_x(coefficients):
    return [coefficient * (-1) ** k for k, coefficient in enumerate(coefficients)]


def expand(numerator, denominator, terms):
    """Solve D(x) A(x) = P(x) coefficient by coefficient over the integers."""
    assert denominator[0] == 1
    answer = []
    for k in range(terms):
        rhs = numerator[k] if k < len(numerator) else 0
        rhs -= sum(
            denominator[j] * answer[k - j]
            for j in range(1, min(k, len(denominator) - 1) + 1)
        )
        answer.append(rhs)
    return answer


def verify():
    numerator = substitute_minus_x(ORIGINAL_NUMERATOR)
    denominator = substitute_minus_x(ORIGINAL_DENOMINATOR)
    degree = len(denominator) - 1
    assert degree == 20 and len(numerator) == 20
    assert numerator[-1] != 0 and denominator[-1] != 0
    initial = expand(numerator, denominator, degree)
    assert len(PRINTED_CONTRACTIBLE) == len(PRINTED_NONCONTRACTIBLE) == 15
    printed_differences = [
        (-1) ** k * (contractible - noncontractible)
        for k, (contractible, noncontractible) in enumerate(
            zip(PRINTED_CONTRACTIBLE, PRINTED_NONCONTRACTIBLE)
        )
    ]
    assert initial[:15] == printed_differences

    # For d(t)=t^20 D(1/t), synthetic division proves
    # d(t)=(t-r)(t^19-beta_1*t^18-...-beta_19)-gamma.
    growth = 2
    horner = [denominator[0]]
    for coefficient in denominator[1:]:
        horner.append(coefficient + growth * horner[-1])
    beta = [-coefficient for coefficient in horner[1:-1]]
    gamma = -horner[-1]
    assert horner[0] == 1 and len(beta) == 19
    assert all(coefficient >= 0 for coefficient in beta) and gamma > 0

    # The recurrence begins with a_20 because deg P < deg D. The initial
    # a_0 and b_0,...,b_18 below therefore suffice for the joint induction.
    differences = [initial[k + 1] - growth * initial[k] for k in range(19)]
    assert initial[0] == 6 and all(value > 0 for value in differences)
    return {
        "status": "PASS",
        "width": 8,
        "sequence": "a_k = (-1)^k (h_8^c(k+1) - h_8^nc(k+1))",
        "vertex_columns": "L = k + 2",
        "denominator_degree": degree,
        "growth_r": growth,
        "initial_terms_expanded": len(initial),
        "separately_printed_differences_matched": len(printed_differences),
        "a_0": initial[0],
        "minimum_initial_difference": min(differences),
        "beta": beta,
        "gamma": gamma,
        "initial_a": initial,
        "claim": "a_k > 0 and a_(k+1) > 2 a_k for every k >= 0",
        "source": "https://dmtcs.episciences.org/en/articles/2113/download",
        "printed_page": 235,
        "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Exact all-length algebra for the published circumference-eight rational function; no all-width theorem, independent human review, or priority claim.",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
