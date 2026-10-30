# Does the Lean statement actually say "ETH is false"?

A kernel check proves that the formal statement holds. It does not prove that the statement means what it
is claimed to mean. This note records a reading of every definition in
`lean/ComparatorChallenges/SubexponentialSAT.lean` (openai/math @ `7ef5c0cc…`, SHA-256 `4183b205…`, 220 lines)
looking for a loophole.

**Result: no loophole found.** This is a negative finding, not a new result. The reading was done by two
independent AI reviewers (Claude and a second agent); it is not a substitute for expert review.

## Checks

| Possible loophole | What the file says |
|---|---|
| Is `n` in the exponent the input length? (Then ETH would not be refuted.) | No. `F : SAT.CNF (Fin n)` (l. 199), so `n` is the number of variables. The exponent is `runtimeScale n`; the input length only enters the polynomial factor `(inputBits+1)^degree` (l. 136–139, 210–211). |
| Is the machine model too strong (arithmetic in one step, oracles)? | No. `PrimitiveMachine` (l. 92–124) is a finite-state multi-tape Turing machine over `Option Bool`. Each step reads one tape and either halts or applies one Mathlib `TM0.Stmt`: move one cell or write one symbol (`Mathlib/Computability/TuringMachine/PostTuringMachine.lean` l. 118–120; `Tape.lean` l. 436–439, 542–543). Weaker than the usual model, since only one tape is read per step. |
| Non-uniformity (a different machine per `n`)? | No. Quantifier order `∀ k, ∃ machine, ∃ C A S d e, ∀ n F` (l. 194–199): one fixed machine per `k`. |
| Is time measured honestly? | Yes. `Trace` (l. 87–90) follows the deterministic step function for exactly `time` steps to a halted state (`Sum.inl …`); `step` returns `none` once halted (l. 109). Unit cost per step. |
| Does the encoding hide work? | It is unary (l. 55–77), hence bloated, but harmless: `CNF` is a `Finset`, so there are `O((2n)^k)` distinct clauses of width ≤ k and `formulaBitLength = n^{O(k)}`. For fixed `k` the polynomial factor is `poly(n) = 2^{o(n)}`. |
| Is the output weak? | No. The count tape holds the binary expansion of `SAT.count F` (exact #SAT over all `2^n` assignments); the answer tape and the final state hold `0 < count` (l. 203–208). |
| Is the bound subexponential? | `runtimeScale n = n·(log log(n+16))²/√log(n+16) = o(n)` (natural log). |

## Conclusion

The statement says: for every fixed `k ≥ 2` there is a deterministic multi-tape Turing machine that computes
the exact number of satisfying assignments of any width-≤k CNF on `n` variables in
`poly(|F|)·2^{O(n (log log n)²/√log n)} = 2^{o(n)}` steps, using polynomial space. Taking `k = 3`, this
contradicts ETH. Since SETH implies ETH, SETH is refuted too.

The last step, "this statement implies ¬ETH", is a short informal argument, not a Lean theorem.
The remaining trust base is the Lean kernel, Mathlib's `Turing.Tape`/`TM0` definitions, and the challenge file
itself (hash checked; matched to the proof by Comparator, see `VERIFICATION.md`).
