# Kuratowski's theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

**Theorem (Kuratowski, 1930).** A finite graph is planar if and only if it contains no
subdivision of `K₅` and no subdivision of `K₃,₃`.

The audited statements are in [`Challenge.lean`](Challenge.lean), which imports only Mathlib:
- `KuratowskiTheorem.isPlanar_iff`: Kuratowski's theorem.
- `KuratowskiTheorem.isMinor_of_isTopologicalMinor`: a subdivision of any finite graph `H` in
  `G` gives `H` as a minor of `G`.
- `KuratowskiTheorem.isTopologicalMinor_K33_of_isMinor`: a `K₃,₃` minor gives a `K₃,₃`
  subdivision.
- `KuratowskiTheorem.isTopologicalMinor_of_isMinor_K5`: a `K₅` minor gives a `K₅` or a `K₃,₃`
  subdivision.
- Sanity checks on the definition of planarity: `K₄` is planar, `K₅` and `K₃,₃` are not.

The proofs are in [`Solution.lean`](Solution.lean), `Kuratowski/` and `LeanPool/`. Supporting
files:
- [`comparator.json`](comparator.json) names the compared theorems;
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md) reproduces verbatim the Mathlib definitions
  used;
- [`formalization.yaml`](formalization.yaml) records provenance, sources and process.

## Definitions

* **Planarity.** `G` is planar if it has a *plane map*: a rotation system (a cyclic order of the
  darts at every vertex) whose Euler defect is zero, i.e. every component has genus zero. By the
  Heffter–Edmonds–Ringel rotation principle this is planarity in the usual sense. That
  equivalence with topological embeddings is classical and is **not** formalized here.
* **Minors.** `H` is a minor of `G` if `G` has disjoint, nonempty, connected branch sets, one for
  every vertex of `H`, with an edge of `G` between the branch sets of adjacent vertices.
* **Subdivisions (topological minors).** `G` contains a subdivision of `H` if it has:
  - distinct branch vertices, one for every vertex of `H`;
  - for every pair of adjacent vertices of `H`, a path of `G` between their branch vertices that
    contains no other branch vertex.

  Paths of different edges of `H` meet only at branch vertices.

## How the proof goes

Wagner's theorem says that a finite graph is planar if and only if it has no `K₅` and no `K₃,₃`
minor. It is taken from the author's formalization
[jtraverso/planar-list-colouring](https://github.com/jtraverso/planar-list-colouring). Kuratowski's
theorem then needs three lemmas, all in `Kuratowski/`:

* **Subdivision ⇒ minor** (`TopToMinor.lean`).
  1. Orient the edges of `H`.
  2. The branch set of `w` is its branch vertex together with the paths of the edges leaving
     `w`, without their last vertex.
* **Terminals in a connected set** (`Terminal.lean`).
  - Up to three terminals in a connected vertex set can be joined to a common centre by paths
    inside the set that meet only at the centre.
  - Four terminals can be joined either to one centre, or to two centres joined by a path, each
    centre serving two terminals.
* **Minor ⇒ subdivision** (`Subdivision.lean`).
  - For `K₃,₃`: apply the three-terminal lemma in every branch set, at the endpoints of the
    connecting edges.
  - For `K₅`: apply the four-terminal lemma in every branch set. If every branch set has one
    centre, this gives a `K₅` subdivision. If the branch set of `w` has two centres `c ≠ d`,
    with `c` serving `p, q` and `d` serving `r, s`, then `{c, r, s}` against `{d, p, q}` is a
    `K₃,₃` subdivision.

## Contents

* `LeanPool/K5MinorFreeChoosability/` holds the 33 modules of the planarity library needed for
  Wagner's theorem. They come from the author's Lean Pool contribution (`K5MinorFreeChoosability`)
  and were copied from the author's entry
  [jtraverso/planar-list-colouring](https://github.com/jtraverso/planar-list-colouring) (commit
  `ec1eafbc091713857eb5683a46e460902b2d47b3`).
* `Kuratowski/` contains the subdivision lemmas, which are new.

## Sources

* K. Kuratowski, *Sur le problème des courbes gauches en topologie*, Fund. Math. 15 (1930)
  271–283, doi:10.4064/fm-15-1-271-283.
* K. Wagner, *Über eine Eigenschaft der ebenen Komplexe*, Math. Ann. 114 (1937) 570–590.

## Authorship and use of AI

The result and the proof route were chosen by the author. The statements and proof plans were
written with Claude (Claude Code). The proofs of the subdivision lemmas were produced by
Harmonic's Aristotle and audited and rebuilt locally. Everything is checked mechanically with
Lean. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
