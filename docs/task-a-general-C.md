# Task A — `precision_extension` generalized to every depth constant `C`

Date: 2026-10-30. File: `lean/PrecisionExtensionGeneral.lean` in this repo (474 lines, core Lean 4.34.1 only, no `import`).
Drafted by Claude Fable. Repeated on the Mac with the same hash: `logs/lean-lemma/precision-extension-general-check.log`
(exit 0, same two warnings, same axioms). The compile section below is Fable's own sandbox run.
SHA-256: `cced7e0fb231c4f04c48fad4663d76c20b0a299d3c73a3860b48fc7fb7c5378c`.
Derived from `lean/PrecisionExtensionCore.lean` @ repo commit `4fbd732` (sha256 `2fef7050…`, 451 lines); all helper lemmas unchanged.

## Statement

```lean
theorem SubexponentialSAT.PrecisionExtensionCore.precision_extension_general
    (c B N d u : Nat) (hB : B ≤ 2 ^ 20)
    (hN : 2 ^ (640 + 8 * c) ≤ N)
    (hd : 2 ^ (6 * d) ≤ 2 ^ (18 + c) * N) (hu : u = N / 2 ^ (17 + d)) :
    2 ^ u ≥ N ^ (B + 2) * u * 2 ^ 18
```

Mapping to the paper: the depth bound `H < M ≤ C·s·8^{-d}` with `H ≥ s/√λ`
(`quantitative-contraction.tex` L94–96, L80) gives `2^{6d} < C²λ`. Take `c` with
`C² ≤ 2^{18+c}`, i.e. `c = max(0, ⌈2·log₂ C⌉ − 18)`; then `hd` holds with `N = λ`.
The threshold is `f(c) = 640 + 8c` (linear in `c`). `hB : B ≤ 2^20` kept (optional removal not done).

## Subsumption of the old theorem (one line, in the file)

```lean
theorem precision_extension (B N d u) (hB) (hN : 2 ^ 640 ≤ N) (hd : 2 ^ (6 * d) ≤ 2 ^ 18 * N) (hu) :
    2 ^ u ≥ N ^ (B + 2) * u * 2 ^ 18 :=
  precision_extension_general 0 B N d u hB hN hd hu
```
`c = 0`: `2^(18+0) = 2^18` covers `C ≤ 512` (`512² = 2^18`), `2^(640+8·0) = 2^640`. Identical statement to the certified one, now a corollary.

## What changed in the proof (only the `18` coming from `hd`)

| Step | old | new |
|---|---|---|
| A | `2^512 ≤ u`; split `d < 110` (use `hN`) / `d ≥ 110` (use `2^(6d−18) ≤ N`) | `2^(512+c) ≤ u`; split `d < 112+7c` / `d ≥ 112+7c` (use `2^(6d−(18+c)) ≤ N`); needs `529+c+d ≤ 640+8c` resp. `≤ 6d−18−c` — both linear, discharged by `omega` |
| C | `2^(5d) ≤ 2^36·u` | `2^(5d) ≤ 2^(36+c)·u` |
| F (`d ≥ 19`) | `2^(d+23) ≤ 2^(5d−36) ≤ u` | split `d+23 ≤ 512+c` (use Step A) / `d ≥ 490+c` (use `2^(d+23) ≤ 2^(5d−36−c) ≤ u`, needs `4d ≥ 59+c`) |
| HK… | uses `2^512 ≤ u` | uses `hA512 : 2^512 ≤ u` derived from Step A; otherwise verbatim |

No new mechanism; the slack in the original argument (`2^(5d−36)` vs `2^(d+23)`, Step-A threshold) absorbs `c` once the precision threshold grows by `8c`.

## Compile (sandbox, Lean 4.34.1 x86_64; please repeat on the Mac — command below)

```
$ lean PrecisionExtensionGeneral.lean ; echo exit $?
PrecisionExtensionGeneral.lean:379:46: warning: exponent 512 exceeds the threshold 256, exponentiation operation was not evaluated, ...
PrecisionExtensionGeneral.lean:469:43: warning: exponent 640 exceeds the threshold 256, exponentiation operation was not evaluated, ...
'SubexponentialSAT.PrecisionExtensionCore.precision_extension_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SubexponentialSAT.PrecisionExtensionCore.precision_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit 0
```
The two warnings are Lean declining to *evaluate* `2^512`/`2^640` as literals (the original file emits the first one too); the proofs treat them as atoms and are unaffected. Escape-hatch grep (`sorry`, `axiom`, `native_decide`, `import`, `exponentiation.threshold`): none. `decide` is used 15 times, all on small literals (`2^20`, `2^27`, `2^6`, `4 = 2*2`, `0 < 2`, …), same as the original.

Mac command (per brief):
```
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean ~/eth-verify/scratch/PrecisionExtensionGeneral.lean; echo exit $?
```
Expected: the four lines above and `exit 0`.

## Caveat
This certifies the arithmetic inequality only. That it is *the* inequality needed at `quantitative-contraction.tex:354` to replace `P₀ ≤ Cs` by `P₀ ≤ s·λ^K`, and that the rest of Appendix D goes through unchanged, remains the hand argument in `docs/appendix-d-precision-extension.md`; it is not formalized.
