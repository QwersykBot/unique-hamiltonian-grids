# Independent review: selected end verticals

**Verdict: PASS for the stated exact graph and hypotheses.** The frozen source was read in full, its two endpoint arguments were checked against the ambient adjacency definition, and one isolated Lean replay succeeded. The independently produced object file matches the author's object hash.

## Frozen source and dependency scope

- Source: `../BoundaryVertical.lean`, 16,376 bytes.
- Source SHA256: `88878e56e5afe32ea18c5fa74dc86f71ab17ddefcc3f1a6b2fd7efa8fdc82b55`.
- Namespace: `TriangularCylinder.BoundaryVertical`.
- Direct imports: `RowRotation` and `Mathlib.Data.Set.Card`.
- Dependency-pin file SHA256: `65794be45e8ec6e1e1fcb00124cc5a6351606c8891e4e369112c55188d4280fd`.

The review checked the source and object hashes of all eight pinned local modules, the upstream rotation receipt, the Mathlib commit, and the Mathlib manifest. The upstream modules and Mathlib were used as pinned dependencies; this replay did not rebuild or independently audit their entire proofs. The exact ambient graph definition and the row-successor equivalence were inspected for this application.

## Statements reviewed

The main theorems are `exists_first_selected_vertical`, `exists_last_selected_vertical`, and their conjunction `exists_selected_verticals_at_both_ends`. Their assumptions are:

- `m >= 3` and `L >= 3`;
- `H : SimpleGraph (Fin m × Fin L)`;
- `H ≤ TriangularCylinder.graph m L hm`;
- `H.Connected`;
- every selected neighbor set has `Set.ncard = 2`.

The conclusions supply a selected vertical edge in each end column, with an actual `NextRow` pair. The two row gaps are allowed to differ. No presentation of `H` as a Hamiltonian walk is assumed.

The neighbor-subset, neighbor-equality, crossing-selection, and closure helpers require only `L >= 2`. Their row-arithmetic section also takes `[NeZero m]`; the main theorems construct that instance from `m >= 3`. Finiteness is provided by the vertex type, so `ncard = 2` is ordinary finite cardinality here.

## Semantic proof audit

The exact ambient graph is the undirected union of vertical, horizontal, and consistently oriented forward diagonal edges. A forward diagonal goes from `(r,c)` to `(r+1,c+1)`, with cyclic row arithmetic. Column advancement is a natural-number equation on column values, not modular addition on `Fin L`; there are no wrapping column edges.

`NoVerticalAt` quantifies positively oriented row steps. Because `H` is a simple undirected graph, the proof correctly excludes reverse-oriented selected verticals by symmetry as well.

At the first end, absence of a selected vertical restricts the neighbors of `(r,0)` to `(r,1)` and `(r+1,1)`. Those vertices are distinct by `nextRow_ne`. Degree two forces both. Symmetry then supplies the distinct neighbors `(r,0)` and `(r-1,0)` of `(r,1)`, saturating the second-column vertex. Thus the first two columns are closed under selected adjacency.

The right end is proved directly, with no column-reflection assumption. Absence of a last-column vertical restricts the neighbors of `(r,L-1)` to `(r,L-2)` and `(r-1,L-2)`. The predecessor is essential: it is the row at the source of a forward diagonal ending at the last-column vertex. Degree two forces these edges. At `(r,L-2)`, the selected neighbors `(r,L-1)` and `(r+1,L-1)` are then forced and exhaust the degree. Thus the last two columns are closed.

Both saturation steps use finite set inclusion together with equal cardinality two. The proof uses the cyclic group operations on `Fin m`, with `nextRow_iff_add_one`; it does not use the size-changing operation `Fin.pred`.

The private reachability helper preserves membership in any adjacency-closed set by induction on `Relation.ReflTransGen`. For the first-end contradiction the source starts in column zero and the target is in column two. For the last-end contradiction the source starts in the last column and the target is in column zero. `L >= 3` makes the respective target lie outside the closed pair of columns.

Only the inequalities `r != r+1` and `r != r-1` are needed. There is no exceptional failure at `m = 3`, nor at `L = 3`. The restriction to at least three columns in the existence theorems is material: for two columns, closing the two-column set yields no connectedness contradiction. The source correctly makes no two-column existence claim.

## Independent replay

`replay.py` verified the frozen pins before compilation and the source pin again afterward. It used a previously absent local output directory, the pinned upstream `verification/build`, and the Mathlib path obtained through the pinned `lake env printenv LEAN_PATH`. The author's `BoundaryVertical.olean` and author output directory were not used as imports.

- Lean: 4.19.0, compiler commit `6caaee842e94`.
- Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Mathlib manifest SHA256: `5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752`.
- Compilation used `-DwarningAsError=true` and exited zero, with empty stderr.
- All nine source-requested theorem axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Output: `build/BoundaryVertical.olean`, 545,832 bytes.
- Independent output SHA256: `5b95409e2a93264b34eefdbc7493fc8cff058500d98e4d2372bed19739d7dbe3`, matching the author pin.
- Receipt: `compiler-receipt.json`, SHA256 `333dfce01fe842a7e89183dc6485f5e1e22d76cc285b80684ff22decb22c25a1`.

The source contains no `sorry`, new `axiom`, `unsafe`, or `native_decide`. The exact command, environment paths, checked dependencies, output hashes, and axiom lists are recorded in the receipt. No graph enumeration or unrelated tests were performed. In this pinned workspace, a subsequent independent replay can use `python3 replay.py --output-dir /absolute/path/to/a/new/replay-directory`.

## Limits of the result

This proves selected vertical existence at the two actual ends, under the connected degree-two assumptions. It does not exclude an arbitrary interior cut, classify the two-column case, align the two selected gaps, establish contractibility or parity, or prove any transfer-state or counting theorem. No such stronger conclusion is needed or used in the reviewed source.

Reviewed by `/root/strip_ports` on 2026-11-25. Source and author receipts were preserved unchanged.
