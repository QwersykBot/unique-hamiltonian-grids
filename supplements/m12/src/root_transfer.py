"""Independent cell-frontier Hamiltonian-cycle counter for research checks."""
from collections import defaultdict
from time import perf_counter


def canonical(s):
    labels = {}
    return tuple(0 if v == 0 else labels.setdefault(v, len(labels) + 1) for v in s)


def count(m, n, deleted=(), modulus=None):
    deleted = set(deleted)
    remaining = m * n - len(deleted)
    if remaining < 4:
        return 0
    active = {(0,) * (n + 1): 1}
    for r in range(m):
        for c in range(n):
            pos = r * n + c
            kept = pos not in deleted
            if kept:
                remaining -= 1
            following = defaultdict(int)
            for old, multiplicity in active.items():
                a, b = old[c], old[n]
                s = list(old)
                s[c] = s[n] = 0
                incoming = int(a != 0) + int(b != 0)
                choices = []
                if not kept:
                    if not incoming:
                        choices.append(s)
                elif incoming == 0:
                    if r + 1 < m and c + 1 < n:
                        t = s.copy()
                        t[c] = t[n] = max(s) + 1
                        choices.append(t)
                elif incoming == 1:
                    label = a or b
                    if r + 1 < m:
                        t = s.copy()
                        t[c] = label
                        choices.append(t)
                    if c + 1 < n:
                        t = s.copy()
                        t[n] = label
                        choices.append(t)
                elif a == b:
                    if remaining == 0 and not any(s):
                        choices.append(s)
                else:
                    choices.append([a if v == b else v for v in s])
                for t in choices:
                    following[canonical(t)] += multiplicity
            if modulus:
                active = {s: v % modulus for s, v in following.items() if v % modulus}
            else:
                active = dict(following)
    return active.get((0,) * (n + 1), 0)


if __name__ == '__main__':
    import json
    for m, n in [(2, 2), (2, 5), (3, 3), (3, 4), (4, 4), (4, 6), (6, 6), (8, 8)]:
        t = perf_counter()
        value = count(m, n)
        print(json.dumps({'m': m, 'n': n, 'count': value, 'seconds': perf_counter() - t}), flush=True)
