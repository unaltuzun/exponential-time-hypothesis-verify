# Remark: explicitly encoded rational factor tables (not a new result)

Source: `main_full_version.tex` at `openai/math` commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` — Prop. `prop:general-count` (L2013–2030), Definition `def:layout` (L1714–1748), Lemma `lem:row-coefficients` (L2635), Prop. `prop:count` (L3044–3088), Appendix B `app:arithmetic` (L3886–). Numerical sanity check: `scripts/weighted_test.py` (`results/weighted_test_seed7.log`).

## Setting

Explicit rational tables `φ_a : {0,1}^{S_a} → ℚ`, `a = 1..m`, on `n` Boolean variables; target

`Z = Σ_{x∈{0,1}^n} ∏_a φ_a(x_{S_a})`, `M = Σ_a |S_a|`.

Let `L` be the total binary encoding length of all tables (numerators and denominators), `w = max_a |S_a|`, `b` the maximum number of factors containing one variable.

**Assumptions (all explicit):**
1. `M = Σ_a |S_a| = O(n)` (total incidence; `b ≤ polylog` alone does not imply this).
2. `w ≤ polylog(n)` and `b ≤ polylog(n)`; if `b` is achieved by fixing the variables of incidence above `b₀ = ⌈M/n⌉⌈√λ⌉` (source L3109–3117), the `2^{|S|} ≤ 2^{n/√λ}` branches are a separate multiplicative factor and require assumption 1.
3. The source's layout conditions (Definition `def:layout`, built by Lemma `lem:layout` under Lemma `lem:incidence-parameters`).

Each table is used through its multilinear extension `φ̃_a(y) = Σ_{U⊆S_a} c_{a,U} ∏_{v∈U} y_v`, of degree `≤ w_a`, so the input-degree hypothesis (L1689–1693) holds with `d ≤ M = O(n)`.

## Weighted-factor height bound and scope of the corollary

For each factor `a`, let `w_a = |S_a|`, and let `L_a` denote the encoding length of its rational table. The Möbius coefficients of its multilinear extension satisfy

`|c_{a,U}| ≤ 2^{w_a} · max_{x∈{0,1}^{S_a}} |φ_a(x)|`.

Thus their bit lengths increase by at most `O(w_a)` beyond the table-entry magnitude and common-denominator costs. The argument does not require `w_a` to be constant: `w_a ≤ polylog(n)` suffices for this overhead to remain within the claimed polynomial bit bound.

Using the common denominator

`Ω = ∏_a q_a Δ^{w_a}`,  `Δ = (R−1)! Q!`,  `log₂ Ω = O(L + M Q log(Q+2))`

(`q_a` = product of the denominators of table `a`, `Σ_a log₂ q_a = O(L)`; `Δ` from Lemma `lem:row-coefficients`), and the coefficient 1-norm bound for substituted factors, the integer numerators of products and partial sums have polynomial bit length in the input size and the layout parameters. In particular, the logarithm of the number of accumulated terms contributes only additively to the numerator bit length. The enumeration bound is

`2Qr · C_q (2D+1)^{2τn} 2^{2n/r}`,

where the source's parameter choice gives

`log C_q = O( n (R/Q) log(2Q/R) )`.

Consequently

`log(Qr C_q) = O( log(Qr) + n (R/Q) log(2Q/R) )`.

Thus the logarithm of the total number of accumulated terms is bounded by

`O( log(Qr) + n (R/Q) log(2Q/R) + τ n log(2D+1) + n/r )`.

Under the source's chosen parameter regime, these contributions, together with the common-denominator bound, substituted-factor norm bounds, and Taylor depth `J`, give a polynomial bound `B_data = poly(n, L, λ)`. This height estimate does not require changing the parameters `r, Q, R, τ, D` that determine the source algorithm's exponential running-time factor. The Hermite interpolation and determinant bounds of Appendix B (the Hermite matrix with integer nodes `1..Q` and multiplicity `J`; fraction-free elimination) then apply unchanged.

Note that the Beigel–Tarui lift chain `Δ → Γ = Δ^{2ℓ−1} → Ω = Γ^{m_test}` of `prop:count` (L3072–3077) is **not** needed here: weighted tables are summed directly over `ℚ`, with no parity lift.

## Conditional conclusion

Under assumptions 1–3, the general-count routine adapted to weighted table inputs computes `Z` in `poly(n, L) · 2^{O(ρ(n))}` bit operations and `poly(n, L)` bits of space, with `ρ(n) = n (log log n)²/√log n` the source's exponent on this route (including the dense-variable branching). Weight bit length enters only the polynomial factor, not the exponent.

## Scope and caveats

* This is not a new algorithm: it is an application of the source's general-count routine and Appendix B arithmetic/interpolation framework to explicitly encoded rational factor tables, subject to the stated layout, incidence, and height bounds.
* `prop:general-count` counts ring operations and explicitly requires the bit cost of general factor evaluators to be verified separately (L2040–2044). The height bound above is the part that closes that obligation for weighted tables; it is our derivation from the source's proof template, not a result stated in the source.
* It does not establish the sharper Appendix D tensor-contraction bound `2^{O(s/√log s)}` for arbitrary weighted tables: that route works modulo `2^{P₀}` with `P₀ ≤ Cs`, so weights of super-constant bit length do not fit it without further ideas.
* Real-valued weights are out of scope (no finite encoding).
