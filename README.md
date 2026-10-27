# exponential-time-hypothesis-verify

Independent reproduction and verification materials for the OpenAI preprint
**"The Exponential Time Hypothesis is False"** (17 Oct 2026, rev. 25 Oct 2026) and its Lean 4 formalization.

Source under study (not vendored here): https://github.com/openai/math at commit
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`
(`preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/`, `lean/ComparatorChallenges/SubexponentialSAT.lean`,
`lean/OAI/Algorithms/SubexponentialSAT/`). OpenAI's materials are Apache-2.0; we only reference them by path, hash and line number.

## What is here

| Path | Contents |
|---|---|
| `docs/REPORT.md` | Full report: definitions, algorithm reconstruction, complexity derivation, Lean audit, dependency graph, assessment, research directions |
| `VERIFICATION.md` | *(added after the build)* Kernel-verification run on Apple M5 Max: build table, verbatim `#print axioms`, Comparator output |
| `scripts/mechanism_test.py` | Independent small-instance reproduction of the core mechanism (swap-matrix construction, replacement rows, separated Taylor data, Hermite recovery) with exact rational arithmetic. `python3 -I scripts/mechanism_test.py <seed>` |
| `docs/weighted-corollary.md` | Remark (not a new result): explicit rational factor tables under the general-count route — height bound and scope |
| `scripts/weighted_test.py` | Same pipeline with arbitrary rational factor tables (weighted partition function `Z`) — shows the mechanism does not depend on factors being clause indicators |
| `scripts/import_closure.py` | Import-closure analysis of the Lean proof (`3,091` modules / `547k` lines for `Main.lean`) |
| `results/` | Logs of the above runs (all `ALL CHECKS PASSED`) |
| `logs/` | Command logs from the sandboxed attempt (where the Mathlib cache was unreachable) |

## Headline findings

* The comparator file `SubexponentialSAT.lean` is a *statement* (its theorem ends in `sorry` by design); the proof is `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` in `SqrtLogSpace/Final.lean`.
* Static audit of the full closure: 0 `sorry`, 0 `axiom`, 0 `native_decide`, 0 `unsafe`/`extern`; challenge definitions match the library textually.
* Lean formalizes the **weaker** bound `(L+1)^{O_k(1)} 2^{O_k(n (log log n)^2/√log n)}` (paper's Prop. `prop:interpolation-bound`), not Theorem 1.1's `n/√log n` tensor-contraction bounds. The weaker bound is still `2^{o(n)}` and suffices to refute ETH; the final step "`ρ(n)=o(n)` ⇒ ETH false" is informal (trivial) and not a Lean theorem in the OpenAI library.
* The algebraic mechanism (Sections 2 and 4.2 of the paper) is correct as a set of exact identities on every small instance tested; see `scripts/`.
* Build/axiom/Comparator results: see `VERIFICATION.md`.

## Reproduce

See `docs/REPORT.md` §11. Short version (macOS/Linux, needs ~40 GB disk, cache access to `cache.mathlib.org`):

```sh
git clone https://github.com/openai/math.git && cd math && git checkout 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
cd lean && lake update && lake exe cache get
lake build ComparatorChallenges.SubexponentialSAT          # statement; expect 1 'sorry' warning
lake build OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final   # proof; #print axioms at Final.lean:197-201
```

## Disclosure

This work was carried out with substantial AI assistance (Claude, Anthropic). Anthropic published an independent claim of the same result on the same day (`anthropics/formal-math/eth`); it was used only as a cross-reference and is discussed in `docs/REPORT.md` §8.7. Nothing here constitutes an endorsement of either claim; the open question is stated in `docs/REPORT.md` §10.

## License

Our own files: MIT. Referenced OpenAI materials remain under their Apache-2.0 license.
