# Appendix D: relaxing `P₀ ≤ Cs` to `P₀ ≤ s(log s)^K`

Source: openai/math @ `7ef5c0cc…`, `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/`.
Line numbers refer to `quantitative-contraction.tex` unless marked `reduction:` (`quantitative-reduction.tex`).

**Status:** the extension is checked by hand against the source; its arithmetic core is proved in Lean
(`lean/PrecisionExtensionCore.lean`, with restrictions listed below). The weighted-table corollary is a
conditional, paper-level argument and is not formalized. Nothing here changes the paper's main result.

## 1. Where `P₀` enters

The tensor-contraction theorem (reduction:26–49) takes entries in `(ℤ/2^{P₀}ℤ)[V]/(V^ℓ)` with `1 ≤ P₀, ℓ ≤ Cs`.
`P₀` occurs at lines 53–54, 66, 354, 561 and 617–618. Only line 354 uses its size: "The first assertion holds at
the root since `P₀ ≤ Cs`". The others choose the ring, the canonical lifts, and the final extraction.

Source parameters: `λ = ⌈log₂ s⌉`, `ε = 1/(128·1024)`, `u_d = ⌊ελ/2^d⌋`, `a_d = 2·Σ_{j≤d} u_j`, `L = 2^{a_d}`
(82–91); children have fewer than `M/8` edges, `M ≤ Cs·8^{−d}`, leaves have `M ≤ H = ⌈s/⌊√λ⌋⌉` (85, 95, 525–526);
on active calls `u ≥ λ^{4/5}`, `a_d ≤ 4ελ`, `L ≤ s^{1/1000}` (100–104); `D_t = L/2^{v₂(t)}`, `h = ⌈3M/u⌉`,
`p_t = p + 8hD_t + 8M(a+1)` (252–264).

## 2. The argument

The precision proof (348–368) has two steps.

1. **Input bound** `p ≤ s·λ^{O(1)}·2^{a_{d−1}}`. With `P₀ ≤ s·λ^K` this still holds at the root (the exponent of
   `λ` grows by `K`); the per-depth increments do not depend on `P₀`.
2. **Child bound** `p_t = O(M·D_t/u)`. From `q_t > 0 ⇒ D_t ≥ 2^{a_{d−1}+u}` (359–361) and `M > H ≥ s/√λ`, it
   suffices that `√λ·λ^{K+O(1)}·u ≤ C′·2^u`, which holds for large `s` because `u ≥ λ^{4/5}`.

The mode count `exp(O(√(M·p_t/D))) = exp(O(M/√u))` (457–460) uses only step 2, so the running time
`2^{O(s/√log s)}` is unchanged. Constants and the small-`s` threshold now depend on `K`.

## 3. Lean: the arithmetic core

```lean
theorem SubexponentialSAT.PrecisionExtensionCore.precision_extension
    (B N d u : Nat) (hB : B ≤ 2 ^ 20) (hN : 2 ^ 640 ≤ N)
    (hd : 2 ^ (6 * d) ≤ 2 ^ 18 * N) (hu : u = N / 2 ^ (17 + d)) :
    2 ^ u ≥ N ^ (B + 2) * u * 2 ^ 18
```

Here `N = λ` and `u = u_d` with `ε = 2^{−17}`. Core Lean only (no Mathlib). Independent check:
`logs/lean-lemma/precision-extension-check.log` (Lean 4.34.1, exit 0, no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]`).

**General `C` (added 30 Oct 2026):** `lean/PrecisionExtensionGeneral.lean` proves

```lean
theorem SubexponentialSAT.PrecisionExtensionCore.precision_extension_general
    (c B N d u : Nat) (hB : B ≤ 2 ^ 20) (hN : 2 ^ (640 + 8 * c) ≤ N)
    (hd : 2 ^ (6 * d) ≤ 2 ^ (18 + c) * N) (hu : u = N / 2 ^ (17 + d)) :
    2 ^ u ≥ N ^ (B + 2) * u * 2 ^ 18
```

so every depth constant `C` is covered by choosing `c` with `C² ≤ 2^(18+c)`; the threshold grows to
`2^(640+8c)`. The original theorem is derived in the same file as the case `c = 0`. Drafted by Claude Fable,
checked independently on the Mac: `logs/lean-lemma/precision-extension-general-check.log` (exit 0, no `sorry`,
both theorems `[propext, Classical.choice, Quot.sound]`). Details: `docs/task-a-general-C.md`.

Restrictions:
- `hd` encodes the depth bound `8^d < C√λ ⇒ 2^{6d} < C²λ`. The first file (`PrecisionExtensionCore.lean`) fixes
  `2^18`, i.e. `C ≤ 512`; the general file removes this restriction.
- Only `B ≤ 2^20` is covered, not every fixed `B`.
- The threshold `λ ≥ 2^640` (that is, `s ≥ 2^(2^640)`) is legitimate for an asymptotic statement and has no
  practical meaning.
- The step "this inequality suffices for the proof" (§2) and the mapping of Lean variables to the paper are
  done by hand.

The file was drafted with GLM-5.3 (via OpenCode) and checked independently as above.

## 4. Weighted-table corollary (conditional, paper level)

For rational factor tables `φ_a`, scale each table by its common denominator `q_a` (numerators `p̃_a`) and set
`Ω = ∏ q_a`. The contraction then computes the integer `ΩZ = Σ_x ∏_a p̃_a(x)`. Recovering it with sign requires

```
P₀ ≥ n + Σ_a ⌈log₂ max|p̃_a|⌉ + 2
```

(`⌈log₂ Ω⌉` is not enough). The source's own counting proof uses the same principle: `P₀ = n+1` because
`0 ≤ #F ≤ 2^n` (reduction:86–93).

Conditions: (i) number of tables and total arity `O(n)`, so `s = Θ(n)`; (ii) bounded arity, encoded like the
source's clause encoding; (iii) polylog-bit numerators and denominators per table. Then `P₀ = O(s(log s)^K)` and
§2 gives `Z` exactly in `(s+𝓛)^{O(1)}·2^{O(n/√log n)}` time and polynomial space. For dense instances the
source itself uses `O(n log log n)` wires and the bound is not sharp.

## 5. Errors found in an earlier AI draft of this argument

Listed so they are not repeated: four mechanisms that are not in the source (`u_d = max(1,·)`, "two-stage node
splitting", an `s^{−Θ(1)}` error term, a constraint `s ≥ exp(c√log N)`; the arithmetic is exact and 2-adic);
`D_t` defined with the description length `𝓛` instead of `L = 2^{a_d}`; edge schedule `M/2` instead of `< M/8`;
a leaf regime with `u = 1`, `M = O(log s)` that does not occur; `P₀ = ⌈log₂ Ω⌉`.
