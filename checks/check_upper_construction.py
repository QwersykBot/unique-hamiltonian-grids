"""Finite independent checks of the reconstructed prior 2k upper bound."""

if not __debug__:
    raise SystemExit(
        "Verification requires assertions. Rerun without -O/-OO and unset PYTHONOPTIMIZE."
    )


from itertools import combinations
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from independent_cycle_counter import edge_count, path_count

ROOT = Path(__file__).resolve().parent


def retained_vertices(k, n):
    assert k >= 1 and n >= 3
    m = 4*k
    deleted = {(r,0) for r in range(0,m,4)}
    suffix_residue = 2 if n%2 else 1
    deleted.update((r,n-2) for r in range(suffix_residue,m,4))
    return {(r,c) for r in range(m) for c in range(n)} - deleted


def ladder_completions():
    coordinates = {'A':(0,0),'L':(1,0),'B':(2,0),
                   'C':(0,1),'R':(1,1),'D':(2,1)}
    edges = [(u,v) for u,v in combinations(coordinates,2)
             if sum(abs(a-b) for a,b in zip(coordinates[u],coordinates[v])) == 1]
    completions = []
    for mask in range(1<<len(edges)):
        chosen = [edge for j,edge in enumerate(edges) if mask & (1<<j)]
        degrees = {v:sum(v in edge for edge in chosen) for v in coordinates}
        if all(degrees[v] == (2 if v in 'LR' else 1) for v in coordinates):
            completions.append({tuple(sorted(edge)) for edge in chosen})
    expected = [
        {tuple(sorted(edge)) for edge in [('A','L'),('L','B'),('C','R'),('R','D')]},
        {tuple(sorted(edge)) for edge in [('A','C'),('B','L'),('L','R'),('R','D')]},
        {tuple(sorted(edge)) for edge in [('B','D'),('A','L'),('L','R'),('R','C')]},
    ]
    assert len(completions) == 3 and {frozenset(x) for x in completions} == {frozenset(x) for x in expected}
    return [sorted(completion) for completion in completions]


def main():
    sources = {
        'check_upper_construction.py': ROOT/'check_upper_construction.py',
        'independent_cycle_counter.py': ROOT/'independent_cycle_counter.py',
        'two_k_construction.md': ROOT.parent/'two_k_construction.md',
    }
    source_hashes = {name:hashlib.sha256(path.read_bytes()).hexdigest()
                     for name,path in sources.items()}
    completions = ladder_completions()
    controls = []
    graphs = {
        'two_by_two_cycle':{(r,c) for r in range(2) for c in range(2)},
        'two_by_five_ladder':{(r,c) for r in range(2) for c in range(5)},
        'three_by_three_odd':{(r,c) for r in range(3) for c in range(3)},
        'three_by_four_multiple':{(r,c) for r in range(3) for c in range(4)},
        'four_by_three_perimeter':{(r,c) for r in range(4) for c in range(3) if r in (0,3) or c in (0,2)},
    }
    for name,vertices in graphs.items():
        count,stats = edge_count(vertices)
        stats.pop('cpu_seconds')
        oracle = path_count(vertices)
        assert count == oracle
        controls.append({'name':name,'edge_count_capped_at_two':count,'path_oracle_capped_at_two':oracle,**stats})
    assert {row['edge_count_capped_at_two'] for row in controls} == {0,1,2}
    cases = []
    for k in range(1,5):
        for n in range(3,9):
            m = 4*k
            vertices = retained_vertices(k,n)
            deleted = {(r,c) for r in range(m) for c in range(n)} - vertices
            assert len(deleted) == 2*k
            count,stats = edge_count(vertices)
            stats.pop('cpu_seconds')
            assert count == 1,(m,n,count)
            cases.append({'m':m,'n':n,'k':k,'deleted':len(deleted),
                          'deleted_vertices_zero_based':sorted(deleted),
                          'cycles_capped_at_two':count,**stats})
    for name,digest in source_hashes.items():
        assert hashlib.sha256(sources[name].read_bytes()).hexdigest() == digest
    report = {'status':'PASS','source_hashes':source_hashes,
              'method':'Independent undirected graph-edge search with degree propagation and proper-subtour rejection; no transfer or SCC imports',
              'counter_semantics':'0 and 1 are exact; 2 means at least two distinct undirected Hamiltonian cycles',
              'ladder_completions':completions,'controls':controls,'cases':cases,
              'scope':'Finite checks supplement the general forced-edge and premature-cycle proof. The 2k bound was already stated in the motivating questions; no novelty is claimed.'}
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
