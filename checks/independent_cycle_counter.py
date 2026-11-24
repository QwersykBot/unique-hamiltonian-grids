"""Independent undirected graph-edge counter, reused without algorithm changes.

Source: bounded-reconstruction/verify_bounded_construction.py
Source SHA256: b24444009cdd9f79608b5888513e0a1dd1ff31449b175a8dff36c11089f2c1cb
No transfer-state or SCC imports.
"""

if not __debug__:
    raise SystemExit(
        "Verification requires assertions. Rerun without -O/-OO and unset PYTHONOPTIMIZE."
    )



import time


def graph(vertices):
    vertices = sorted(vertices)
    lookup = {vertex: index for index, vertex in enumerate(vertices)}
    pairs = []
    adjacent = [[] for _ in vertices]
    incident = [0] * len(vertices)
    for source, (row, column) in enumerate(vertices):
        for neighbour in [(row + 1, column), (row, column + 1)]:
            if neighbour in lookup:
                target = lookup[neighbour]
                edge = len(pairs)
                pairs.append((source, target))
                incident[source] |= 1 << edge
                incident[target] |= 1 << edge
                adjacent[source].append((target, edge))
                adjacent[target].append((source, edge))
    return vertices, pairs, incident, adjacent


def edge_count(vertices, cpu_limit=2.0):
    started = time.process_time()
    vertices, pairs, incident, adjacent = graph(vertices)
    size = len(vertices)
    calls = 0
    if size < 4 or sum((r + c) % 2 == 0 for r, c in vertices) * 2 != size:
        return 0, {"calls": calls, "cpu_seconds": time.process_time() - started}
    all_edges = (1 << len(pairs)) - 1

    def search(chosen, forbidden):
        nonlocal calls
        calls += 1
        if calls % 128 == 0 and time.process_time() - started > cpu_limit:
            raise TimeoutError("independent edge-counter CPU limit")
        while True:
            before = chosen, forbidden
            for mask in incident:
                selected = (chosen & mask).bit_count()
                unknown = mask & all_edges & ~(chosen | forbidden)
                available = unknown.bit_count()
                if selected > 2 or selected + available < 2:
                    return 0
                if selected == 2:
                    forbidden |= unknown
                elif selected + available == 2:
                    chosen |= unknown
            if before == (chosen, forbidden):
                break

        degrees = [(chosen & mask).bit_count() for mask in incident]
        unseen = {v for v, degree in enumerate(degrees) if degree}
        while unseen:
            start = min(unseen)
            component = {start}
            frontier = [start]
            while frontier:
                vertex = frontier.pop()
                for neighbour, edge in adjacent[vertex]:
                    if chosen & (1 << edge) and neighbour not in component:
                        component.add(neighbour)
                        frontier.append(neighbour)
            unseen -= component
            if all(degrees[v] == 2 for v in component):
                return int(len(component) == size)

        # Every Hamiltonian cycle must lie within one connected allowed graph.
        reachable = {0}
        frontier = [0]
        while frontier:
            vertex = frontier.pop()
            for neighbour, edge in adjacent[vertex]:
                if not forbidden & (1 << edge) and neighbour not in reachable:
                    reachable.add(neighbour)
                    frontier.append(neighbour)
        if len(reachable) != size:
            return 0

        unknown_all = all_edges & ~(chosen | forbidden)
        choices = [(int((mask & unknown_all).bit_count()), -degrees[v], mask & unknown_all)
                   for v, mask in enumerate(incident) if mask & unknown_all]
        assert choices
        unknown = min(choices)[2]
        edge = unknown & -unknown
        with_edge = search(chosen | edge, forbidden)
        if with_edge >= 2:
            return 2
        return min(2, with_edge + search(chosen, forbidden | edge))

    count = search(0, 0)
    return count, {"calls": calls, "cpu_seconds": time.process_time() - started}


def path_count(vertices):
    """Separate small-graph oracle enumerating vertex paths, not edge subsets."""
    vertices, _, _, adjacent = graph(vertices)
    size = len(vertices)
    if size < 4:
        return 0
    links = [{neighbour for neighbour, _ in row} for row in adjacent]
    full = (1 << size) - 1
    result = 0

    def visit(path, used):
        nonlocal result
        if result >= 2:
            return
        if used == full:
            if 0 in links[path[-1]] and path[1] < path[-1]:
                result += 1
            return
        for neighbour in links[path[-1]]:
            if not used & (1 << neighbour):
                visit(path + [neighbour], used | (1 << neighbour))

    visit([0], 1)
    return result
