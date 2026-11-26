#!/usr/bin/env python3
"""Verify the complete certified M(12,12)=6 result using Python only.

--sample is a deliberately partial smoke test. It never establishes equality.
"""
import argparse
from collections import deque
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
UPPER_DELETIONS = [0,48,96,22,70,118]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            value.update(block)
    return value.hexdigest()


def validate_payload():
    """Check frozen payload integrity before importing the counting/checking code."""
    hashes = {}
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = (ROOT / relative).resolve()
        require(path.is_relative_to(ROOT) and path.is_file(), 'Missing or invalid payload path: '+relative)
        require(relative not in hashes, 'Duplicate checksum entry: '+relative)
        require(sha256(path) == expected, 'Payload checksum mismatch: '+relative)
        hashes[relative] = expected
    required = {'verify.py','regenerate.py','src/check_certificate.py','src/root_transfer.py',
                'data/complete-m12-hc-certificate.jsonl.gz','data/sample-m12-hc-certificate.jsonl.gz',
                'data/upper12-witness.json','data/independent-check-report.json'}
    require(required <= hashes.keys(), 'Manifest does not cover every verification input')
    return hashes


def load_source(name):
    spec = importlib.util.spec_from_file_location('m12_packet_'+name, ROOT/'src'/(name+'.py'))
    require(spec is not None and spec.loader is not None, 'Cannot load packaged source: '+name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def forced_upper_cycle(checker):
    """Force the unique upper cycle using necessary edge constraints only.

    Any Hamiltonian cycle must contain forced edges and use available edges.
    No branch, search, counting procedure, or timeout is used.
    """
    gone = set(UPPER_DELETIONS)
    kept = [v for v in range(144) if v not in gone]
    available = [set() if v in gone else set(checker.NEIGHBORS[v])-gone for v in range(144)]
    forced = [set() for _ in range(144)]
    rounds = exclusions = 0
    while True:
        rounds += 1
        pending = deque(kept)
        while pending:
            vertex = pending.popleft()
            require(len(forced[vertex]) <= 2 and len(available[vertex]) >= 2,
                    'Upper propagation derived a degree contradiction')
            if len(available[vertex]) == 2:
                for other in available[vertex]-forced[vertex]:
                    forced[vertex].add(other)
                    forced[other].add(vertex)
                    pending.append(other)
            if len(forced[vertex]) == 2:
                for other in available[vertex]-forced[vertex]:
                    available[vertex].remove(other)
                    available[other].remove(vertex)
                    pending.append(other)
        labels = {}
        components = []
        for first in kept:
            if first in labels:
                continue
            label = len(components)
            component, stack = {first}, [first]
            labels[first] = label
            while stack:
                vertex = stack.pop()
                for other in forced[vertex]:
                    if other not in component:
                        component.add(other)
                        labels[other] = label
                        stack.append(other)
            require(len(component) == len(kept) or any(len(forced[v]) != 2 for v in component),
                    'Upper propagation derived a forced proper cycle')
            components.append(component)
        remove = []
        for vertex in kept:
            for other in available[vertex]-forced[vertex]:
                if vertex < other and labels[vertex] == labels[other] and len(components[labels[vertex]]) < len(kept):
                    # Adding this edge would close a cycle inside a proper
                    # connected component of already-forced edges.
                    remove.append((vertex,other))
        if not remove:
            break
        for vertex,other in remove:
            available[vertex].remove(other)
            available[other].remove(vertex)
        exclusions += len(remove)
    require(all(len(forced[v]) == 2 for v in kept), 'Upper proof stopped before all degrees were forced')
    mask = sum(1 << i for i,(a,b) in enumerate(checker.EDGES) if b in forced[a])
    checker.validate_cycle(mask,tuple(sorted(gone)))
    # All possible Hamiltonian cycles contain this already-spanning cycle;
    # degree two at every retained vertex leaves no alternate edge set.
    return mask, {'propagation_rounds':rounds,'proper_subtour_edge_exclusions':exclusions,
                  'forced_edges':mask.bit_count(),'unique_cycle_hex':format(mask,'066x')}


def verify_upper(checker, frontier=None):
    record = json.loads((ROOT/'data/upper12-witness.json').read_text())
    require(record['m'] == record['n'] == 12, 'Wrong upper-construction grid')
    require(record['deleted'] == UPPER_DELETIONS, 'Wrong six-deletion upper construction')
    require(len(record['cycles']) == 1, 'Expected one saved upper-construction witness')
    cycle = record['cycles'][0]
    retained = set(range(144)) - set(UPPER_DELETIONS)
    require(all(type(vertex) is int for vertex in cycle), 'Noninteger cycle vertex')
    require(len(cycle) == len(retained)+1 and cycle[0] == cycle[-1], 'Wrong upper-cycle length or closure')
    require(set(cycle[:-1]) == retained, 'Upper witness does not span exactly the retained vertices')
    require(all(abs(a//12-b//12)+abs(a%12-b%12)==1 for a,b in zip(cycle,cycle[1:])),
            'Upper witness uses a nongrid edge')
    forced_mask, details = forced_upper_cycle(checker)
    edge_index = {edge:i for i,edge in enumerate(checker.EDGES)}
    witness_mask = sum(1 << edge_index[tuple(sorted((a,b)))] for a,b in zip(cycle,cycle[1:]))
    require(witness_mask == forced_mask, 'Saved upper witness differs from the forced unique cycle')
    report = {'deleted_vertices':UPPER_DELETIONS,'witness_valid':True,'uniqueness_proved':True,
              'exact_hamiltonian_cycle_count':1,'method':'degree and proper-subtour forcing; no search or counting',
              **details}
    if frontier is not None:
        count = frontier.count(12,12,UPPER_DELETIONS)
        require(type(count) is int and count == 1, 'Optional independent frontier count is not one')
        report['optional_frontier_cycle_count'] = count
    return report


def assemble_report(lower, upper, partial):
    require(lower.get('valid') is True, 'Certificate checker did not return valid')
    require(upper.get('witness_valid') is True and upper.get('uniqueness_proved') is True
            and upper.get('exact_hamiltonian_cycle_count') == 1,
            'Upper construction was not established')
    if partial:
        require(lower.get('complete') is False, 'Sample mode unexpectedly returned a complete claim')
        return {'valid':True,'complete':False,'equality_established':False,'mode':'partial-smoke',
                'lower_certificate':lower,'upper_construction':upper,
                'conclusion':'Only the supplied sample and the upper construction were checked; complete coverage, the lower bound, and M(12,12)=6 are not asserted.'}
    require(lower.get('complete') is True, 'Incomplete certificate cannot establish the lower bound')
    return {'valid':True,'complete':True,'equality_established':True,'mode':'complete',
            'lower_certificate':lower,'upper_construction':upper,
            'conclusion':'The complete lower-bound certificate proves M(12,12)>=6; the exact-one six-deletion construction proves M(12,12)<=6. Therefore M(12,12)=6.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sample',action='store_true',help='partial smoke test; never claims complete coverage or equality')
    parser.add_argument('--frontier',action='store_true',help='also run the optional independent upper frontier count')
    args = parser.parse_args()
    started = time.perf_counter()
    hashes = validate_payload()
    checker = load_source('check_certificate')
    frontier = load_source('root_transfer') if args.frontier else None
    name = 'sample-m12-hc-certificate.jsonl.gz' if args.sample else 'complete-m12-hc-certificate.jsonl.gz'
    lower = checker.check([ROOT/'data'/name],partial=args.sample)
    upper = verify_upper(checker,frontier)
    report = assemble_report(lower,upper,args.sample)
    report['payload_files_verified'] = len(hashes)
    report['certificate_sha256'] = hashes['data/'+name]
    report['checker_sha256'] = hashes['src/check_certificate.py']
    if args.frontier:
        report['optional_frontier_source_sha256'] = hashes['src/root_transfer.py']
    report['seconds'] = time.perf_counter()-started
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
