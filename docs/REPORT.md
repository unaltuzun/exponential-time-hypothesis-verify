# ETH / Subexponential SAT — Mathematical Reconstruction and Verification Audit

**Subject:** OpenAI preprint *The Exponential Time Hypothesis is False* (dated 17 Oct 2026, revised 25 Oct 2026) and its Lean formalization in `openai/math`.
**Prepared:** 2026-10-27 (UTC). Research directory: `/home/user/eth-research/` (isolated; no existing GODBRAIN project was touched).
**Author of this report:** Claude (Anthropic). Conflict-of-interest note: Anthropic published a parallel, independent claim of the same result on the same day (see §8.7). I have treated both claims with the same skepticism and have not used Anthropic's materials to evaluate OpenAI's proof except as a cross-reference, which is flagged where it appears.

---

## 1. Executive Summary

**What the paper claims.** For every fixed `k ≥ 2` there is a deterministic algorithm that *exactly counts* the satisfying assignments of a `k`-CNF with `n` variables and `m` clauses in time `(n+m)^{O_k(1)} · 2^{O_k(n·log log n / √log n)}` and polynomial space; for `m ≤ Dn` the exponent improves to `O_{k,D}(n/√log n)`. Since the exponent is `o(n)`, the `k = 3` case contradicts the Exponential Time Hypothesis (ETH), SETH, Gap-ETH, NSETH and #ETH. [`main_full_version.tex` L73–85]

**What is actually formalized in Lean.** A *weaker* bound: `(L+1)^{O_k(1)} · 2^{O_k(n (log log n)^2/√log n)}` where `L` is the bit length of a canonical (unary-field) encoding — i.e. the paper's Proposition `prop:interpolation-bound` (exponent `ρ(n)`), **not** Theorem 1.1's sharper bounds, and **not** the fixed-density `n/√log n` bound. The sharper bounds come from a separate tensor-contraction appendix (`quantitative-reduction.tex`, `quantitative-contraction.tex`) that has no Lean counterpart. The weaker bound is still `2^{o(n)}` and is sufficient to contradict ETH. The Lean theorem is `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` (`lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean` L74–102).

**What I verified, and what I could not.**

| Item | Status |
|---|---|
| Repository cloned, commit pinned, cited files exist | ✅ commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` |
| Comparator challenge file `SubexponentialSAT.lean` | ⚠️ It is a *statement*: line 218 is `sorry` by design (Comparator pattern). The proof lives in `OAI/Algorithms/SubexponentialSAT/` (3,977 files, 710,320 lines). |
| Static audit of the full proof closure (3,091 modules, 547,460 lines) | ✅ 0 `sorry`, 0 `axiom`, 0 `native_decide`, 0 `unsafe`/`implemented_by`/`extern`; only 3 genuine `opaque` defs (with bodies) |
| Challenge definitions match library definitions | ✅ textually identical (`SAT.lean`, `Encoding.lean`, `StatementScale.lean`, `Computation.lean`, `VisitedTape.lean`) |
| **Lean compilation / kernel check** | ✅ **Achieved on the user's Mac after this report was first written — see `VERIFICATION.md`** (Final: exit 0, 0 errors; axioms = propext/Classical.choice/Quot.sound; Comparator: accepts). Original sandbox attempt: ❌ Toolchain `v4.34.1` installed locally and works; dependency resolution succeeded; but the Mathlib binary cache host (`cache.mathlib.org`) is blocked by this sandbox's egress proxy (HTTP 403 on all 8,908 archives). Building Mathlib from source on 2 cores/7 GB reached ~750/8,900 modules in 30 min; the OAI closure (547k lines) would come after. The `#print axioms` lines in `Final.lean` L197–201 could therefore not be executed. |
| Comparator tool (`leanprover/comparator` + `landrun` + `lean4export`) | ✅ run in a Linux VM (see `VERIFICATION.md` §6): `Your solution is okay!`. Not runnable in the original sandbox |
| Paper read in full (67 pp.; `.tex` source 214,857 chars + 3 appendix files) | ✅ |
| **Independent reproduction of the core mechanism** | ✅ Implemented from the paper (not from Lean) with exact rational arithmetic; all identities verified on small instances: swap-matrix construction, support and kernel lemmas, replacement rows, design/separation property, separated Taylor-coefficient computation, Hermite recovery of `#F`. 3 random formulas × 3 seeds, all `ALL CHECKS PASSED` (see §8.5). |

**Strongest verified conclusion (by me):** The algebraic mechanism at the heart of the paper — *deform each variable occurrence by a degree-`R` polynomial linear form that (i) restores the variable at `T=0`, and (ii) at `Q` integer points depends on other variable groups only through a small set of shared integer measurements; then recover `H(0)=#F` from `O(nR/Q)` Taylor coefficients at each point by Hermite interpolation* — is **correct as a set of exact identities**. I verified every lemma of Section 4.2 and the full count-recovery pipeline of Section 2 numerically on small instances. What I have **not** verified is the asymptotic bookkeeping (Lemma `lem:incidence-parameters`, the sparsification tree bounds, the expander/greedy parity-test construction, the bit-complexity appendix) and the tensor-contraction sharpening — these rest on the Lean build (which I could not run) and on my reading of the proofs (which found no error but is not a substitute for a kernel check).

**Update (2026-10-28):** the question below was answered affirmatively by the run documented in `VERIFICATION.md` (build exit 0, three standard axioms, Comparator accepts). What remains open is mathematical review of the paper's sharper, unformalized Theorem 1.1 bounds and the Impagliazzo–Paturi–Williams group's report.

**Single most important unresolved technical question (as of the sandbox run):** *Does the Lean library actually compile under the pinned toolchain with only `propext`, `Classical.choice`, `Quot.sound` as axioms, and does Comparator confirm that the proved theorem equals the challenge statement?* Everything else about the ETH refutation reduces to this plus the (elementary, but informal) step from `2^{O(n(log log n)^2/√log n)}` to `2^{δn}` for all `δ > 0`. The OpenAI README itself warns that unformalized results "could have issues"; this one *is* formalized, which is exactly why compiling it is the decisive step.

---

## 2. Source and Version Manifest

### 2.1 Primary repository

| Field | Value |
|---|---|
| URL | https://github.com/openai/math |
| Clone command | `git clone --depth 1 https://github.com/openai/math.git` (exit 0) |
| Retrieval time | 2026-10-27 19:52:30 UTC |
| Branch | `main` |
| Commit | `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` |
| Commit date / message | 2026-10-26 14:18:03 −0700 — "Merge pull request #3 from openai/codex/update-10-26" |
| Tree size | 174,524 files; 753 preprint directories; `lean/OAI/Algorithms/SubexponentialSAT`: 3,977 `.lean` files, 710,320 lines, 42 MB |

### 2.2 Files examined (SHA-256 at the pinned commit)

| Path | SHA-256 |
|---|---|
| `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf` (887,884 B, 67 pages) | `5b1612dc2eebb2cad5b4cbe62d1fed2982f01ab1908c26f70010a651487e8123` |
| `…/build/main_full_version.tex` (214,857 chars) | `b2e6159d4fb7ea6aa4f89ac15605152b0333a5f7cafe93323492bc20a5c066aa` |
| `…/build/quantitative-reduction.tex`, `quantitative-contraction.tex`, `quantitative-circuits.tex` | read; included via `\input` at `main_full_version.tex` L4269, L4326–4327 |
| `lean/ComparatorChallenges/SubexponentialSAT.lean` (220 lines; `sorry` at L218) | `4183b2057cff350d66848215ff7167196dfc20e1891b598fdddea59077a76685` |
| `lean/ComparatorChallenges/SubexponentialSAT.json` | `debbfdc9c01104d2369be80da5180978275106df8b685f693fba7ce7da7c5b19` |
| `lean/docs/378.md` | `a2f7b390d6308997350b903be02c40a1227ebd2b9376982da528574500531f79` |
| `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean` (201 lines) | `040360a8465957622d934e5f1bb4f2cce8dab950e78f52033fbf70da493184f5` |
| `lean/lean-toolchain` → `leanprover/lean4:v4.34.1` | `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b` |

### 2.3 Toolchain and dependencies (what was actually downloaded/installed)

| Component | Source | Result |
|---|---|---|
| `elan` installer | `raw.githubusercontent.com/leanprover/elan/master/elan-init.sh` (sha256 `a620ff16…`), installed to `/home/user/eth-research/toolchain/elan` with `--no-modify-path`, no sudo | installed; **its toolchain downloader was blocked by the proxy** (CONNECT 403) |
| Lean `v4.34.1` Linux release | `https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst` (580,432,872 B) | downloaded via `curl` (GitHub is allowed), decompressed with Python `zstandard`, placed at `/home/user/eth-research/toolchain/lean-4.34.1/`. `lean --version` → `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`; `Lake version 5.0.0-src+5045d00`. |
| Lake dependency resolution (`lake update` in `math/lean/`) | 42 git packages from GitHub, incl. Mathlib pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612` (matches `lakefile.lean`), plus 11 vendor packages patched by the lakefile's `lean4341` compatibility patches | **resolved**; exit 1 only because Mathlib's post-update `cache get` hook failed |
| Mathlib binary cache (`lake exe cache get`) | `cache.mathlib.org` | **FAILED — 0 of 8,908 archives; every request `CONNECT tunnel failed, response 403`** (egress allowlist). Not retried via other routes. |
| `comparator`, `landrun`, `lean4export` | github releases / cargo | not attempted beyond reading the README; cannot run without Mathlib oleans anyway |
| Python `zstandard` | PyPI | installed (user-level, `--break-system-packages`) for tarball decompression only |

Full command log with timestamps and exit codes: `/home/user/eth-research/logs/commands.log`; raw logs in `/home/user/eth-research/logs/`.

### 2.4 Cross-reference material (outside the OpenAI tree)

* `anthropics/formal-math` at `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, sparse-checkout of `eth/` only, in `/home/user/eth-research/external/formal-math/` (used only in §8.7).
* Secondary literature: see §8 and the Sources list at the end.

---

## 3. Mathematical Definitions

**Literals, clauses, CNF.** Over Boolean variables `x_1,…,x_n`, a *literal* is `x_i` or `¬x_i`. A *clause* is a disjunction of literals; a *`k`-clause* has at most `k` literals. A *`k`-CNF* is a conjunction of `k`-clauses. The paper writes clause `e` as `⋁_{j=1}^k (x_{i_{e,j}} ⊕ b_{e,j})` with `b_{e,j} ∈ {0,1}` the negation bit; repeating a literal allows shorter clauses [L54–63]. The Lean library uses set semantics: `CNF V := Finset (Finset (Literal V))`, `WidthAtMost k F := ∀ C ∈ F, C.card ≤ k` (`SAT.lean` L17–38; identical in the challenge file).

**`k`-SAT (decision):** given a `k`-CNF `F`, decide whether `∃x ∈ {0,1}^n` with `F(x)=1`. **3-SAT** is `k=3`; NP-complete (Cook 1971).
**Search:** output such an `x` when one exists. Decision ⇒ search by the standard self-reduction (fix one variable at a time; `n` extra decision calls) [L96–100].
**#`k`-SAT (exact counting):** compute `#F := |{x : F(x)=1}|` [eq. (1.1), L67–69]. #3-SAT is #P-complete (Valiant 1979). Counting ⇒ decision (`#F > 0`), and conditional counts give exact uniform sampling (Jerrum–Valiant–Vazirani 1986). The three problems are nested in difficulty: counting ≥ search ≥ decision. Lean proves the *counting* statement, which is the strongest.

**ETH (Impagliazzo–Paturi 2001):** there is a constant `δ > 0` such that no deterministic algorithm decides 3-SAT on `n` variables in time `2^{δn}` (equivalently, `s_3 := inf{δ : 3-SAT ∈ DTIME(2^{δn})} > 0`). Polynomial factors in the input size are absorbed by a slightly larger `δ`. Variants: **SETH** (`s_k → 1`), **Gap-ETH**, **NSETH** (nondeterministic version for UNSAT), **#ETH** (Dell–Husfeldt–Marx–Taslaman–Wahlén: #3-SAT needs `2^{Ω(n)}`), and randomized versions.

**Which version is contradicted.** The paper's Theorem 1.1 (and the weaker Lean theorem) gives a *deterministic*, *exact counting* algorithm with time `poly(n+m) · 2^{f(n)}` where `f(n) = o(n)`. For every `δ>0` and all sufficiently large `n`, `poly(n+m)·2^{f(n)} ≤ 2^{δn}·poly(m)`; so 3-SAT (decision, via `#F>0`) is in `DTIME(2^{δn}·poly(m))` for every `δ`, i.e. `s_3 = 0`. That contradicts ETH as stated above, and a fortiori SETH, #ETH, Gap-ETH (the promise problem is solved by exact decision), NSETH (deterministic UNSAT in `2^{o(n)}`), and the bounded-error randomized variants [L289–295]. It does **not** contradict the hypothesis that *unbounded-width* CNF-SAT needs `2^{(1−δ)n}` (the width `k` must stay fixed; the constants are `O_k(·)`) [L361–365], nor OVC/3SUM/APSP conjectures directly [L350–358].

**Models and encoding.** Paper: bit operations and bits of space, integers in signed binary, rationals as numerator/denominator [L505–513]. Lean: a multi-tape primitive machine (`Computation.PrimitiveMachine`: `tapeCount` tapes over `Option Bool`, one transition per step reading the scanned tape, writing or moving one head); time = number of steps; space = total visited cells (`visitedSpace`) measured on *every* prefix of the run. Input is `Encoding.encodeCNF F`: unary number of variables, then a framed list of clauses, each a sorted list of unary literal codes `2·var + polarity`. Hence `L := formulaBitLength F = Θ(Σ_clauses Σ_literals (code+1)) ≤ O_k((n+m)^2)` (the library proves `L+1 ≤ (8k+7)(n+m+1)^2` — `encoding_le_declaredSize_sq`, used by `encoding_pow_le_declaredSize`, `SqrtLogSpace/EncodingBounds.lean` L96–102). Because `L` is polynomial in `n+m`, `(L+1)^{O(1)}` and `(n+m)^{O(1)}` are interchangeable.

---

## 4. Algorithm Reconstruction

The paper has three layers. Layer A is the engine and is where the subexponential improvement comes from; layers B and C turn an arbitrary `k`-CNF into inputs the engine handles while keeping the exponent `o(n)`.

### 4.A The engine: counting a sum of products via shared linear summaries (Sections 2–4)

**Setting (bounded occurrence).** A 3-CNF with `n` variables in which every variable occurs in ≤ 3 clauses (plus constant-1 "dummy" factors for unused variables so that every variable has a position). Clause satisfaction polynomial `Φ_e = 1 − ∏_{v∈I_e}(1 − L_{e,v}(X_v))`, `L = X` or `1−X` [L576–589]. Then
`#F = Σ_{x∈{0,1}^n} ∏_e Φ_e(x|_{I_e})` and the product has total degree `M ≤ 3n` [eq. (2.4)].

**Step 1 — Deformation.** For each occurrence `(e,v)` choose a *replacement row* `P⃗_{e,v}(T) ∈ Q[T]^n` with `⟨P⃗_{e,v}(0),X⃗⟩ = X_v` and `deg ≤ R`. Define `H(T) = Σ_x ∏_e Φ_e((⟨P⃗_{e,v}(T),x⟩)_{v∈I_e}) ∈ Q[T]`. Then `H(0) = #F` and `deg H ≤ MR ≤ 3nR` [eq. (2.6)–(2.7)].

**Step 2 — Design at each point `t ∈ [Q]`** (Definition `def:overview-measurement-structure`, L690–729, formal version Definition `def:layout` L1714–1748): a partition `[n] = S_{t,1}⊔…⊔S_{t,r}` with `|S_{t,g}| ≤ 2n/r`; an assigned group `σ_e(t)` per clause; integer measurement matrices `C_{t,g}` with `Σ_g rows ≤ 2τn` and absolute row sums `≤ D`; and the *separation property*: for a clause assigned to `g`, `⟨P⃗_{e,v}(t),x⟩` depends on `x|_{S_h}` (`h≠g`) only through `y_h = C_{t,h} x|_{S_h}`.

**Step 3 — Separated summation** (Lemma `lem:measurement-separation`, L1781–1878). Fix a measurement tuple `y⃗ ∈ ∏_g [−D,D]^{c_g}`; the sum over assignments with those measurements factorizes as `∏_g Σ_{u∈{0,1}^{S_g}: C_g u = y_g} A_g(u; y⃗)`. Summing over `y⃗` gives `H(t)` with `(2D+1)^{2τn} · r·2^{2n/r}` work instead of `2^n`.

**Step 4 — Taylor coefficients at `t`** (Section 2.5 / 3.4). Put `q = ⌊deg H / Q⌋`, `J = q+1`. Write `ΔP⃗(z) = P⃗(t+z) − P⃗(t)` (every entry divisible by `z`), give the shift its own formal input `X⃗`: `𝒢_x(X⃗,z) = ∏_e Φ_e(⟨P⃗(t),x⟩ + ⟨ΔP⃗(z),X⃗⟩)`. Then `deg_X [z^j]𝒢_x ≤ j`, and Lemma `lem:boolean-differences` (L1933–1962; Möbius inversion on the cube) gives
`H(t+z) ≡ Σ_{|E|≤q} Σ_{U⊆E} (−1)^{|E|−|U|} Σ_{x: x_i=1 (i∈E)} 𝒢_x(1_U, z)  (mod z^J)`.
With `X⃗ = 1_U` fixed, the corrections are independent of `x`, so each inner sum is again a separated sum (Step 3) over `Q[z]/(z^J)`. Cost per point: `C_q = Σ_{j≤q} 2^j C(n,j)` pairs `(E,U)`.

**Step 5 — Hermite interpolation.** `QJ > deg H` Taylor coefficients determine `H`; solve the rational Hermite system and read off `H(0) = #F` [L813–830, L1898–1902].

**Step 6 — Constructing the rows (Section 4; the core innovation).** Work on an auxiliary coordinate set `𝓑 = ([r]×[r])^Q`, `D = r^{2Q}`; a label `u = ((a_u(s), d_u(s)))_{s∈[Q]}` records "variable group at point `s`" and "clause group at point `s`". Let `Π_s` swap the two entries of pair `s` (commuting involutions), `V_0 = ∏_s Π_s`, `W_0 = ½Σ_s (I − Π_s)`, and `M_0 = V_0 f_𝓘(W_0)` where `f_𝓘(z) = (−1)^{A_0} Σ_{j<R} (−2)^j C(z−A_0, j)` satisfies `f_𝓘(j) = (−1)^j` on the interval `𝓘 = {A_0,…,A_0+R−1}` [eq. (4.3)]. Two lemmas:
* **`lem:swaps-matrix`** [L2232–2277]: in the product eigenbasis `ψ` (entries in `{0,±1}`), `M_0 ψ = (−1)^j f(j) ψ` where `j` = number of `−1` positions; so `M_0` fixes every `ψ` with `j ∈ 𝓘`. Taking the transposes of the other `ψ` as rows of `C^𝓑` gives `M_0 ξ = ξ` on `ker C^𝓑`, with `#rows = D·Pr[Bin(Q, (r−1)/(2r)) ∉ 𝓘]`.
* **`lem:swaps-support`** [L2288–2306]: `deg f ≤ R−1` ⇒ `M_0` is a combination of `∏_{s∉S}Π_s` with `|S| ≤ R−1`, so `M_0[u,y] ≠ 0` forces `a_y(s) = d_u(s)` for all but `≤ R−1` positions.
Then define `P⃗_u(T) = δ_u(I−M_0) + Σ_{y: M_0[u,y]≠0} M_0[u,y] φ_{u,y}(T) δ_y` with `φ_{u,y}(T) = ∏_{s: a_y(s)≠d_u(s)} (1 − T/s)` [eq. (4.5)]. **`lem:swaps-forms`** [L2333–2372]: `P⃗_u(0)=δ_u`, `deg ≤ R−1`, and at `T=t` the row uses only the coordinates in the assigned group plus `C^𝓑 ζ`. Finally transfer to the formula by choosing schedules `a_v, d_e ∈ [r]^Q` (derandomized by conditional expectations, `lem:incidence-labels` L2442–2530) and `h` copies of the array (`subsec:embedding`).

**Invariants / termination.** All loops are finite enumerations (points `t`, pairs `(E,U)`, measurement tuples, local assignments); there is no recursion in layer A. The correctness invariant is the exact identity `H(0)=#F` together with the separation identity; nothing is approximate.

**Pseudocode (my reconstruction, grounded in Sections 2–4):**

```
COUNT_BOUNDED_OCC(F):                       # 3-CNF, each var in <=3 clauses, n>=n0
  (r,Q,R,tau,D,I) <- PARAMETERS(n)          # Lemma incidence-parameters / eq.(2.15)
  (M0, C_B)       <- SWAP_MATRIX(r,Q,R,I)   # Sec 4.2: M0=V0 f_I(W0); C_B = exceptional eigenvectors
  P_u(T)          <- AUX_ROWS(M0, C_B)      # eq.(4.5)
  (a_v, d_e)      <- SCHEDULES(F, r, Q)     # Lemma incidence-labels (cond. expectations)
  (P_{e,v}(T), S_{t,g}, sigma_e(t), C_{t,g}) <- TRANSFER(P_u, C_B, a_v, d_e)  # eq.(4.7)-(4.8)
  q <- floor(3nR/Q); J <- q+1
  for t in 1..Q:
     Htaylor[t] <- 0 in Q[z]/(z^J)
     for E subset [n], |E|<=q:  for U subset E:
        corr_{e,v} <- <P_{e,v}(t+z)-P_{e,v}(t), 1_U>            # independent of x
        Z <- 0
        for y in prod_g {-D..D}^{c_{t,g}}:                       # measurement tuples
           pick representatives xbar_g with C_{t,g} xbar_g = y_g (skip tuple if none)
           prod <- 1
           for g in 1..r:
              s <- 0
              for u in {0,1}^{S_{t,g}} with C_{t,g}u = y_g and u_i=1 for i in E∩S_{t,g}:
                 s += prod_{e: sigma_e(t)=g} Phi_e( <P_{e,v}(t), u+sum_{h!=g} xbar_h> + corr_{e,v} )  mod z^J
              prod <- prod*s mod z^J
           Z += prod
        Htaylor[t] += (-1)^{|E|-|U|} * Z
  H <- HERMITE_SOLVE({[z^j]Htaylor[t] : t in [Q], j<J})          # QJ > deg H
  return H(0)
```

### 4.B From bounded occurrence to general #k-SAT with exponent `ρ(n)` (Sections 5–6, Appendix A)

1. **Disjoint sparsification** (Lemma `lem:sparsify`, L3543–3568; proof in Appendix A, L3636–3884, following Calabro–Impagliazzo–Paturi's branching and the counting-preserving variant of Dell et al.): with `σ = 1/s`, `s = ⌊√λ/ν²⌋`, produce `poly·2^{σn} = 2^{O(ρ(n))}` leaf formulas on the *same* `n` variables, with disjoint solution sets, each with ≤ `B = O_k((s log s)^{k−1}) = polylog(n)` occurrences per variable.
2. **Parity tests → sparse polynomial system** (Section 6): build `A^{(0)}` from a Tanner/expander code (Lemma `lem:sparse-checks`, L3261–3437: Cayley double cover with ε-biased shifts; local code found by exhaustive search; every nonzero accepted violation vector has weight ≥ `m/P`), then greedily append `3n` short parity rows chosen by exact counts (Lemma `lem:greedy-hashes`, L3446–3503: each round removes ≥ ¼ of the surviving non-solutions; `(3/4)^{3n}2^n < 1`). Result: `≤ 6n` `𝔽_2`-equations of degree ≤ `k` with polylog many monomials whose common zeros are exactly the solutions.
3. **Counting common zeros** (Theorem `thm:overview-sparse-polynomials`, L1640–1649; proof L3096–3206): lift each parity equation to the integer polynomial `p_ℓ(L_i)` (complemented Beigel–Tarui modulus amplifier, Lemma `lem:rational-idempotent`), expand in powers of `h(Y)=Y(Y−1)` and truncate the *total* `h`-order across all equations at `ℓ = n+1` using the algebra `𝒜_ℓ = Q[V]/(V^ℓ)` (Lemma `lem:total-order`) so the product has input degree `k(m_test + 2(ℓ−1)) = O(n)`; branch on the `≤ n/√λ` most frequent variables so every remaining variable has polylog incidence; then run the engine (Prop. `prop:count`).

### 4.C The sharper bounds of Theorem 1.1 (Appendices D–E; **no Lean counterpart**)

`thm:tensor-contraction` (`quantitative-reduction.tex` L26–50): a bipartite Boolean tensor network with `≤ Cs` edges, max degree `≤ ⌈s^{9/10}⌉`, entries in `(Z/2^{P_0})[V]/(V^ℓ)`, can be contracted in `(s+𝓛)^{O(1)} 2^{O(s/√log s)}` time and polynomial space. The proof (`quantitative-contraction.tex`) replaces the single global Taylor expansion by *recursion on the wires*: at each level the wire count drops by a factor 8 while the retained 2-adic precision halves; the per-level exponents `O(M/√u)` sum geometrically to `O(s/√log s)`. For `m ≤ Dn` the clause/equality network has `O_{k,D}(n)` wires (exponent `n/√log n`); for general `m` the sparse-polynomial lift is encoded with `O(n log log n)` wires (exponent `n log log n/√log n`).

### 4.D The precise lemma responsible for the subexponential improvement

Lemmas **`lem:swaps-matrix` + `lem:swaps-support`** together with the parameter balance in **`lem:incidence-parameters`** (L2747–2845). The point is a *tension between two uses of the same degree-`(R−1)` polynomial `f_𝓘`*: low degree in the commuting swaps makes every replacement row *sparse in the right sense* (≤ `R−1` cross-group mismatches, hence deformation degree ≤ `R−1`), while interpolation of `(−1)^j` on an interval of width `R` makes the correction `I − M_0` *low rank* (`D·e^{−R²/8Q}` measurements). The antecedent is the Alman–Williams interpolation that makes Walsh–Hadamard matrices non-rigid; what is new is using the *same* polynomial for a degree bound in a deformation parameter and coupling it with Hermite recovery (see §8).

---

## 5. Complexity Derivation (independently re-derived)

**Parameters** [eq. (2.15), L1365–1375]: `λ = ⌈log₂ n⌉`, `ν = ⌈log₂ λ⌉`,
`r = ⌊√λ/ν²⌋`, `Q = ⌊λ/(128ν)⌋`, `R = 4⌈√λ⌉` (general: `(β+3)⌈√λ⌉`), `τ = 1/(rλ)`, `D = r^{2Q}`, `𝓘` = `R` consecutive integers centred at `Qp`, `p = (r−1)/(2r)`.

**The three exponential costs** [eq. (2.14), (3.11)]:

1. *Taylor data:* `C_q = Σ_{j≤q} 2^j C(n,j)`. With `η = R/Q` in `η^q C_q ≤ (1+2η)^n` (L2008–2011): `log C_q ≤ q log(Q/R) + n log(1+2R/Q) = O(n (R/Q) log(2Q/R))`. Here `q = ⌊d_H/Q⌋`, `d_H = O(nR)`.
2. *Measurements:* `(2D+1)^{2τn}`, log `= 2τn·log(2D+1) ≤ 2τn·(2Q log r + 1)`.
3. *One group:* `r·2^{2n/r}`.

Exponent `= O(n [ (R/Q)log(2Q/R) + τ log(2D+1) + 1/r ])`.

**Plugging in:** `R/Q = Θ(ν/√λ)`, `log(2Q/R) = Θ(ν)` ⇒ term 1 `= Θ(ν²/√λ)`. `log₂D = 2Q log₂ r ≤ λ/128` ⇒ `τ log(2D+1) = O(1/r)`. `1/r = Θ(ν²/√λ)`. Hence the exponent is `O(n ν²/√λ) = O(n (log log n)²/√log n) =: O(ρ(n))`. ✓ (matches eq. (2.16) and `prop:interpolation-bound`).

**Why √log n (my reading).** The binding constraint is `c_𝓑 = D·Pr[Bin(Q,p) ∉ 𝓘] ≤ 2D e^{−R²/(8Q)} ≤ τD/(3r)` [L1223–1227, L2805–2813], i.e. `R ≳ √(8Q·log(6r²λ)) = Θ(√(Qν))`. Binomial concentration forces `R = Ω(√Q)`; the Taylor cost needs `R/Q` small, so the best achievable ratio is `≈ 1/√Q`. `Q` cannot exceed `O(log n/log r)` because the auxiliary array has `D = r^{2Q}` coordinates and must stay polynomial. Thus exponent `≈ n/√Q ≈ n/√log n` up to `log log` factors — **the square root is the central-limit width of a `Q`-fold product of two-eigenvalue swaps, against a polynomial-size budget on `r^{2Q}`.** The tensor-contraction appendix removes the `(log log n)²` by recursing instead of expanding once.

**Constraints checked in the paper for the parameter choice** (`lem:incidence-parameters`): `r ≥ 2`, `R ≥ 32`, `6R ≤ Q`, `𝓘 ⊆ {0,…,Q}`, `2(b+w)D² ≤ M`, `2Qr² ≤ n`, `D ≤ 2^{λ/128}`. All hold for sufficiently large `n`; the algorithm *checks them exactly in integer arithmetic* and falls back to exhaustive search otherwise (L3185–3197), so the finitely many bad `n` are absorbed into `O_k(1)` constants. This is exactly the `cutoff` in the Lean proof (`NativeLargeEntry.run`, `Final.lean` L35, L44–59).

**General #k-SAT with exponent ρ(n):** leaves `2^{n/s}·poly = 2^{O(ρ(n))}` (since `n/s = O(nν²/√λ)`); per leaf `exp((log n)^{O_k(1)})` counter calls (`3n(2m)^P + 1`, `P = polylog`) each costing `2^{O_k(ρ(n))}` (branching over `≤ n/√λ` variables adds only `2^{n/√λ} ≤ 2^{O(ρ(n))}`). Total `(n+m)^{O_k(1)} 2^{O_k(ρ(n))}`. ✓

**Strongest claimed vs. formalized bound.**

| | Exponent | Where |
|---|---|---|
| Paper Theorem 1.1, general `m` | `O_k(n log log n/√log n)` | Appendix D/E (tensor contraction) — not in Lean |
| Paper Theorem 1.1, `m ≤ Dn` | `O_{k,D}(n/√log n)` | Appendix D — not in Lean |
| Paper Prop. `prop:interpolation-bound` | `O_k(n (log log n)²/√log n) = ρ(n)` | Sections 2–6 — **this is what Lean proves** (`exact_count_and_sat` via `runtimeScale`; `exact_count_eth` via `rho`) |
| Lean `exact_count_eth` (`Final.lean` L104–147) | time `≤ C·(n+m+1)^d·2^{A·rho(n)}` with `rho n = n (log₂log₂ n)²/√log₂ n`, for `n ≥ 20` | — |

**Why the weaker bound suffices:** `ρ(n)/n = (log log n)²/√log n → 0`, so for any `δ>0`, `C(n+m+1)^d 2^{Aρ(n)} ≤ 2^{δn}` for all large `n` (with `m ≤ (2n)^k` after clause normalization). This last step is trivial but is **not itself a Lean theorem** in the OpenAI library (no `ETHIsFalse` definition exists there, unlike Anthropic's `MainResults.lean`).

**Assumptions:** clause width `k` fixed (all constants `O_k`); input is the canonical unary-field encoding (Lean) / any reasonable encoding (paper); input size `L = poly_k(n,m)`; `n ≥ 20` for the explicit `rho` form; natural logarithms; the `+16` shift in `runtimeScale` only matters at tiny `n`.

---

## 6. Lean Verification Results

### 6.1 What the files are

* `ComparatorChallenges/SubexponentialSAT.lean` — a **statement-only** file (its single theorem ends in `sorry`, L218). This is the standard [Comparator](https://github.com/leanprover/comparator) pattern: the challenge file fixes definitions and the statement; `SubexponentialSAT.json` names the solution module `OAI.Algorithms.SubexponentialSAT.Main` and theorem `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, permitted axioms `propext, Quot.sound, Classical.choice`, and **`enable_nanoda: false`** (no second-kernel re-check configured for this challenge; 2 of the 415 challenge configs enable it).
* `OAI/Algorithms/SubexponentialSAT/Main.lean` imports `SqrtLog.ExecutionNativeFinal` and `SqrtLogSpace.Final`. Its docstring says `SubexpOrderedRawMainTheorem.mainTheorem_explicit` formalizes an earlier manuscript *A Subexponential Algorithm for Bounded-Width SAT* (**not present in the repository**) and that `SqrtLogSpace.exact_count_and_sat` strengthens "the subsequent square-root-logarithmic result" with exact counting and all-prefix polynomial space.

### 6.2 The exact theorem (Final.lean L74–97; identical text in the challenge file L194–218)

```
theorem exact_count_and_sat (k : ℕ) (hk : 2 ≤ k) :
  ∃ (machine : PrimitiveMachine) (countTape answerTape : Fin machine.tapeCount)
    (C A S : ℝ) (d e : ℕ), 0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
    ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
      ∃ (time : ℕ) (final : LocatedCfg machine),
        Trace (locatedStep machine) time (locatedInit machine (encodeCNF F)) final ∧
        final.config.tapes countTape = Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
        final.config.tapes answerTape = Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
        final.config.state = Sum.inl (decide (0 < SAT.count F)) ∧
        toNat (countWord (SAT.count F)) = SAT.count F ∧ (countWord (SAT.count F)).length ≤ n+1 ∧
        (time : ℝ) ≤ runtimeBound C A d (formulaBitLength F) n ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ time →
          Trace (locatedStep machine) prefixSteps (locatedInit machine (encodeCNF F)) intermediate →
          (visitedSpace intermediate : ℝ) ≤ S * ((formulaBitLength F : ℝ) + 1) ^ e
```
with `runtimeBound C A d L n = C·(L+1)^d·2^{A·runtimeScale n}`, `runtimeScale n = n·(log log(n+16))²/√log(n+16)` (natural logs).

**Quantifier structure is the right one:** one machine and constants `C,A,S,d,e` *before* `∀ n F` (uniform algorithm, no per-instance tuning). The machine is deterministic (`step` is a function), the run halts in state `inl answer`, and the count is written in binary on `countTape`. The space bound holds at every prefix, which rules out "use exponential space, then erase it".

### 6.3 Proof structure (traced statically)

`exact_count_and_sat` ⇐ `compiled_exact_count_and_sat` (L10–69), which exhibits a concrete program `Native.countingProgram cutoff k (NativeLeafProgram.command k) : BitProgram.Program 80 1220 labels` compiled by `GuardedCompiler.primitive` to a 1,220-tape machine, and case-splits on `n ≤ cutoff`:
* `n ≤ cutoff`: `Native.entry_small_primitive` (exhaustive search) + `NativeOuterBudgets.runtime_with_fallback`/`space_with_fallback`;
* `n > cutoff`: `NativeLargeEntry.run` (`SqrtLogSpace/NativeLargeEntry.lean` L11–35): `∃ cutoff C A d S e, …` the actual subexponential run.
Related theorems in the same file: `exact_count_eth` (restates the time bound as `C(n+m+1)^d 2^{A·rho n}` for `n ≥ 20` using `runtimeBound_le_eth`, `Statement.lean` L9–14, and `encoding_pow_le_declaredSize`), `sat_polynomial_space` (`k ≥ 3`, adds `answer = true ↔ Satisfiable F`), `original_sat_main` (the earlier manuscript's `MainTheorem`, `SqrtLog/StatementCanonical.lean` L37–57).

The library is organized as a verified *compiler-and-program* development: `BitProgram*`, `StructuredCalls`, `GuardedCompiler`, `ArrayPrograms`, `BinaryArithmetic`, … implement the algorithm as a concrete stack-machine program; `Sparsify*`, `ExecSparsify*`, `QuantitativeSparsify`, `BranchTree` (Appendix A), `BinomialInterpolation`/`BinomialMatrix`/`RowInterpolation` (Section 4.2 interpolation), `Layout*` (Definition `def:layout`), `Hash*` (Section 6 parity tests), `Subexp*`/`SqrtLog*` (the two bound regimes), `SqrtLogSpace/*` (all-prefix space accounting) carry the mathematics. Subdirectory sizes: root 1,258 files, `Subexp` 388, `SqrtLog` 2,004, `SqrtLogSpace` 299 (+28 in `DisjointReuse`).

### 6.4 Static escape-hatch audit over the 3,091-module closure of `Main.lean`

| Pattern | Hits |
|---|---|
| `sorry` | **0** (the only `sorry` in scope is the challenge file's, by design) |
| `axiom` declarations | **0** |
| `native_decide`, `Lean.ofReduceBool`, `Lean.trustCompiler` | **0** |
| `unsafe`, `partial def`, `implemented_by`, `@[extern]` | **0** |
| `opaque` declarations | 3 genuine (`queryRecovery`, `rawRecovery`, `fixedRecovery`, all with bodies — sound; other grep hits are comments) |
| `set_option maxHeartbeats` / `maxRecDepth` | 0 |
| `decide` (kernel evaluation) | 15,089 occurrences — legitimate but means a build may be heavy |
| non-Mathlib external imports | only `Lean.Elab.Tactic.Omega` |
| direct Mathlib imports | 50 modules, including `import Mathlib` (whole library) |

This rules out the cheap ways a Lean file can lie. It does **not** rule out (a) a mismatch between the formal statement and the intended one (checked manually in §6.5), or (b) elaboration failures that only a build would reveal.

### 6.5 Does the formal statement match the paper?

| Aspect | Paper (Prop. `prop:interpolation-bound`) | Lean `exact_count_and_sat` | Match? |
|---|---|---|---|
| Problem | exact `#F`, deterministic | `SAT.count F` on tape, deterministic machine | ✅ |
| Width | fixed `k ≥ 2` | `∀ k, 2 ≤ k → ∃ machine …` (machine depends on `k`) | ✅ |
| Time | `(n+m)^{O_k(1)} 2^{O_k(ρ(n))}`, `n ≥ 20` | `C(L+1)^d 2^{A·runtimeScale n}`; `exact_count_eth` gives the `(n+m+1)^d 2^{A ρ(n)}` form for `n ≥ 20` | ✅ (`L = poly(n+m)`) |
| Space | `(n+m)^{O_k(1)}` bits | visited cells `≤ S(L+1)^e` at every prefix | ✅ (stronger: prefix-wise) |
| Model | bit operations | multi-tape primitive machine steps | ✅ (standard; polynomial-equivalent) |
| Encoding | unspecified reasonable | explicit unary-field canonical encoding | ✅ with the caveat that `L` can be `Θ_k((n+m)^2)` |
| Theorem 1.1 sharper bounds | `n log log n/√log n`, `n/√log n` | **absent** | ❌ not formalized (stated in `lean/docs/378.md`) |
| "ETH is false" as a statement | Theorem 1.1 ⇒ ETH false | not stated; needs the trivial `ρ(n) = o(n)` step outside Lean | ⚠️ gap is elementary |

### 6.6 What the Lean kernel would and would not verify

Would verify (if the build succeeds with the three standard axioms): that the exhibited machine exists, halts on every width-`k` canonical input with the exact count and the exact time/space bounds, as a theorem of Lean's type theory + Mathlib. Would **not** verify: that `PrimitiveMachine` is a reasonable cost model (it is — one tape operation per step); that `encodeCNF` is the encoding you care about; that `runtimeScale` is `o(n)` (true, but an informal step); that the paper's prose matches the program (the Lean program is the authority; the paper is exposition); or anything about the sharper Appendix-D/E bounds.

### 6.7 Actual compilation results (no inference from file existence)

| Command (cwd `math/lean`) | Result |
|---|---|
| `elan toolchain install leanprover/lean4:v4.34.1` | **exit 1** — downloader blocked (`CONNECT tunnel failed, response 403`) |
| manual download of `lean-4.34.1-linux.tar.zst` from GitHub releases + extraction | **ok**; `lean --version` and `lake --version` work |
| `lake update` | dependency resolution **ok** (42 packages, Mathlib at the pinned commit); post-update Mathlib `cache get` **failed** (`cache.mathlib.org` → 403 on every archive; 0/8,908 downloaded); overall **exit 1** |
| `timeout 240 lake build ComparatorChallenges.SubexponentialSAT` | **exit 124 (timeout)** after building 343 Mathlib modules from source |
| background `lake build ComparatorChallenges.SubexponentialSAT` (2-hour cap) | at 2026-10-27 20:38 UTC: **911 Mathlib modules built from source, 0 errors, after ≈46 min** on 2 cores shared with other work (≈1.6% of the ~8,900 Mathlib modules the challenge file needs; the heaviest modules come later); see `logs/lake-build-bg.log` for the final count when the 2-hour cap ends. **Did not reach any OAI module.** |
| `comparator` run | **not performed** |
| `#print axioms exact_count_and_sat` | **not executed** (requires the build) |

**Conclusion of the audit: the formal proof is structurally clean and the statement is the right one for refuting ETH (at the `ρ(n)` exponent), but its kernel verification was *not* reproduced in this session.** Reproduction instructions that would work on a machine with cache access are in §11; the Anthropic README reports a comparable (smaller) build taking ~8 min on 24 vCPUs with 7 GB peak, so the OpenAI library (≈3× larger) should be feasible on a workstation once Mathlib's cache is available.

---

## 7. Proof Dependency Graph

Nodes are labelled with the LaTeX label in `main_full_version.tex` (line of `\begin{…}`) or the Lean declaration.

```
thm:main (Theorem 1.1, L73)  [general m: exponent n loglog n/√log n;  m<=Dn: n/√log n]
 ├─ App. D/E  thm:tensor-contraction (quantitative-reduction.tex L26)          ── NOT IN LEAN
 │    ├─ lem:tensor-packets (quantitative-contraction.tex L114)
 │    ├─ lem:tensor-integrality (…L206)
 │    ├─ lem:tapered-hermite (…L250)
 │    └─ lem:tensor-sparse-query (quantitative-reduction.tex L108)  ⇐ lem:total-order, Sec.6 tests, lem:sparsify
 └─ (weaker route, exponent ρ(n)) prop:interpolation-bound (L3570)             ── LEAN: exact_count_eth / exact_count_and_sat
      ├─ lem:sparsify (L3543; proof App. A)
      │    ├─ lem:spar-branch (L3695)
      │    ├─ lem:spar-marked-degree (L3740)
      │    └─ lem:spar-insertion-bound (L3771)  → tree size bound (L3808–3853; Lean: BranchTree.lean)
      └─ Sec. 6.3 "counting one sparse formula" (L3505)
           ├─ lem:sparse-checks (L3261)   [Tanner code on ε-biased Cayley double cover; refs Tanner81, SS96, NN93]
           ├─ lem:greedy-hashes (L3446)   [conditional-expectations row selection; ref Raghavan88]
           └─ thm:overview-sparse-polynomials (L1640; proof L3096)
                ├─ lem:rational-idempotent (L2887)  [Beigel–Tarui 1994; Chan–Williams 2021]
                ├─ lem:total-order (L2958)
                ├─ prop:count (L3044)
                │    ├─ prop:general-count (L2013)
                │    │    ├─ lem:measurement-separation (L1781)
                │    │    └─ lem:boolean-differences (L1933)
                │    └─ App. B: lem:rational-lift-height (L3916), bit-length bounds (L3950–)
                ├─ lem:layout (L2696)
                │    ├─ lem:swaps-matrix (L2232)      ◄── core
                │    ├─ lem:swaps-support (L2288)     ◄── core
                │    ├─ lem:swaps-forms (L2333)
                │    ├─ lem:incidence-labels (L2442)
                │    └─ lem:row-coefficients (L2635)
                └─ lem:incidence-parameters (L2747)   ◄── parameter balance → √log n
Corollaries: cor:max-sat-approximation (L111), cor:graph-counting (L151), cor:quantitative-circuits (L183; App. C),
             cor:consequence-circuits (L4242; uses Williams 2013 Thm 6.1), cor:consequence-local-inversion (L4284)
```

Lean top level (`SqrtLogSpace/Final.lean`):
```
exact_count_and_sat ⇐ compiled_exact_count_and_sat
  ⇐ NativeLargeEntry.run (NativeLargeEntry.lean L11)            [n > cutoff: the real algorithm]
  ⇐ Native.entry_small_primitive                                 [n ≤ cutoff: exhaustive]
  ⇐ NativeOuterBudgets.runtime_with_fallback / space_with_fallback
  ⇐ countWord_toNat, countWord_count_length (EncodingBounds.lean)
exact_count_eth ⇐ exact_count_and_sat + runtimeBound_le_eth (Statement.lean L9) + encoding_pow_le_declaredSize (EncodingBounds.lean L96)
sat_polynomial_space ⇐ … + SAT.count_pos_iff
original_sat_main : SqrtLog.Statement.MainTheorem ⇐ sat_polynomial_space (+ locatedTrace_erase)
```
(The mapping of the ~3,000 lower-level Lean modules to paper lemmas above is inferred from module names and docstrings — e.g. `BranchTree.lean` says "proves the finite counting step in Appendix A.3"; `BinomialInterpolation.lean` is the eq. (4.3) interpolation — and was not mechanically checked.)

---

## 8. Independent Assessment

### 8.1 What is genuinely new (as far as I could establish)

1. **Deformation-plus-measurement separation.** Introducing a formal parameter `T` into the *inputs* of each factor via linear forms that are the identity at `T=0` and become "group-local up to few shared integer measurements" at `T = 1..Q`, then recovering `T=0` by Hermite interpolation of low-order Taylor data. I found no prior work combining these three ingredients. Closest antecedents, all acknowledged by the paper: split-and-list (Williams 2005), sum–product with polynomial weights (Koivisto 2006; Scott–Sorkin 2009), interpolation to smaller instances (Björklund 2016), curve/Kakeya-based polynomial evaluation with Hasse derivatives (Björklund–Kaski–Williams 2019; Bhargava–Ghosh–Kumar–Mohapatra 2023), multiplicity-code recovery (Kopparty–Saraf–Yekhanin 2014).
2. **The swap-algebra construction `M_0 = V_0 f(W_0)`.** Using one low-degree polynomial in `Q` commuting involutions to get *simultaneously* a sparse-support bound (`lem:swaps-support`) and a low-rank correction (`lem:swaps-matrix`). The rank part is a direct relative of the Alman–Williams 2017 construction (a low-degree polynomial matching `(−1)^j` on the concentrated range of inner products makes Hadamard matrices non-rigid, [arXiv:1611.05558](https://arxiv.org/abs/1611.05558v2)); the paper says so (L441–457). The support part, and the use of the *same* `f` as a degree budget for `φ_{u,y}(T)`, I believe is new.
3. **Cross-equation truncation of the Beigel–Tarui lift** (`lem:total-order`): expanding `p_ℓ` in powers of `h(Y)=Y(Y−1)` and truncating total `h`-order across all parity tests to keep input degree linear in `n`. The lift itself is Chan–Williams 2021's; the global truncation is what makes `O(n)` parity tests usable.
4. **Deterministic greedy parity tests by exact counting** (`lem:greedy-hashes`): using the counter as a subroutine of its own reduction.

### 8.2 Which barrier was bypassed

There was no proven barrier: ETH is a hypothesis. What was bypassed is the *empirical* barrier that every known `k`-SAT/#`k`-SAT algorithm (Schöning, PPSZ and refinements, Williams' polynomial method, Chan–Williams `2^{n−n/O(k)}`) gains only a constant factor in the exponent base, because they all enumerate (or sample) assignments directly. The new algorithm never sums over `2^n` assignments: it sums over assignments to groups of size `2n/r` and over integer measurement tuples, after an algebraic change of variables. The honest statement of the "barrier": the known randomized/algebraic techniques all produce running times of the form `2^{(1−c_k)n}`; this is the first with exponent `o(n)` for fixed `k`.

### 8.3 Could it generalize?

Yes, and the paper already does: the engine counts `Σ_x ∏_f Φ_f` for *any* rational factors with input degree `O(n)` and polylog scopes/incidences (Prop. `prop:general-count`), and the tensor-contraction appendix handles general bipartite Boolean tensor networks with bounded-ish degree. Immediate consequences in the paper: independent sets, proper `q`-colorings in `2^{o(v)}`; perfect matchings in `2^{o(v+e)}`; Set Splitting; local-function inversion; Max-`k`-SAT PTAS-like approximations in subexponential time; circuit-SAT for **linear-size** circuits in `2^{o(n)}` ⇒ `E^NP ⊄ SIZE(O(n))` (Williams 2013, Theorem 6.1, verified in the [preprint PDF](https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf)) and even `C_L(n) > c·n√log n` i.o. (Cor. `cor:quantitative-circuits`). Where it does **not** transfer: anything whose natural parameter blows up polynomially under reduction (general NP problems), unbounded clause width (`O_k` constants are exponential in `k`), dense graph problems where `e = Θ(v²)`.

### 8.4 Established vs. my interpretation vs. new conjecture

* **Established (cited primary sources):** ETH/SETH definitions (Impagliazzo–Paturi 2001; Impagliazzo–Paturi–Zane 2001); sparsification bounds (Calabro–Impagliazzo–Paturi 2006; Calabro's thesis); #ETH and counting sparsification (Dell–Husfeldt–Marx–Taslaman–Wahlén 2014); Beigel–Tarui modulus amplification (1994); Chan–Williams deterministic #k-SAT (2021); Williams' algorithms-to-lower-bounds Theorem 6.1 (2013); Alman–Williams non-rigidity of Hadamard (2017); Tanner codes / expander codes (Tanner 1981; Sipser–Spielman 1996); ε-biased sets (Naor–Naor 1993).
* **Verified by me in this session:** every exact identity in Sections 2 and 4.2 (numerically, §8.5); the complexity derivation of §5 (by hand); the structural soundness of the Lean closure (§6.4); statement/definition agreement (§6.5).
* **My interpretation:** the "√log n = binomial concentration vs `r^{2Q}` budget" explanation (§5); the mapping from Lean module names to paper sections (§7).
* **Not verified:** correctness of the asymptotic lemmas, the expander/greedy construction, the bit-complexity appendix and the tensor-contraction appendix beyond reading them; the Lean build.

### 8.5 Small-instance reproduction (performed)

Script: `/home/user/eth-research/scripts/mechanism_test.py` (≈380 lines, exact `fractions.Fraction` arithmetic, written from the paper's text; no Lean code was consulted). Logs: `results/mechanism_test_seed{1,2,3}.log`.

*Part A — Section 4.2 lemmas,* for `(r,Q,R) ∈ {(2,2,2),(2,3,2),(2,4,3),(3,2,2)}`, `D = r^{2Q} ∈ {16,64,256,81}`: constructed `V_0, W_0, f_𝓘, M_0` (and cross-checked the spectral formula against the literal `V_0 f(W_0)`); verified `f_𝓘(j)=(−1)^j` on `𝓘`; verified `M_0ψ=ψ` for `j∈𝓘`; verified `rank(I−M_0)` equals the number of measurement rows `D·Pr[Bin(Q,p)∉𝓘]` (1, 10, 13, 9 respectively); verified the support lemma on all `D²` entries; built rows `P⃗_u(T)`, verified `deg ≤ R−1`, `P⃗_u(0)=δ_u`, and the separation property at every `t∈[Q]` for every `u` and every non-assigned group (row-space membership by exact rank).

*Part B — end-to-end,* random 3-CNFs with ≤3 occurrences/variable, random schedules `a_v,d_e`, `h` copies, transferred rows and measurement matrices; for `(r,Q,R,n) ∈ {(2,2,2,5),(2,3,2,6),(2,2,2,7)}` (seed 1: `#F = 19, 32, 65`; seed 2: `19, 29, 55`; seed 3: `16, 27, 50`; copies `h ∈ {2,…,5}`; `deg H ∈ [4,13]`): verified Definition `def:layout`'s kernel condition at every `t`; verified `H(0)=#F` and `deg H ≤ M(R−1)` by brute force over all `2^n` assignments; computed the `J` Taylor coefficients at each `t` **by the separated routine** (measurement-tuple enumeration × inclusion–exclusion over `(E,U)`) and found them **identical** to brute-force Taylor coefficients; solved the Hermite system and recovered `#F` exactly. Runtime ≈4 min per seed (this is a correctness test in the `3^n` regime, not a speed test — the asymptotic parameter regime `R ≪ Q`, `r ≥ 2`, `D ≤ (2n)^{1/128}` needs `n` astronomically large, cf. `2^{λ/128}` ⇒ `n ≳ 2^{128·…}`).

### 8.6 What would falsify my interpretation

* A Lean build of the pinned commit that fails, or whose `#print axioms` output lists anything beyond `propext, Classical.choice, Quot.sound`, or a Comparator mismatch between `ComparatorChallenges.SubexponentialSAT` and `SqrtLogSpace.exact_count_and_sat`.
* A counterexample to any Section 4.2 lemma at a parameter set my script did not cover (e.g. `r ≥ 3` with `Q ≥ 3`), or to `lem:incidence-labels` (balanced schedules) — my test used random, not derandomized, schedules and never needed the balance bounds.
* An error in `lem:incidence-parameters`' inequalities (e.g. the tail bound `Pr[W∉𝓘] ≤ 2e^{−R²/8Q}` requires `𝓘` to contain all integers within `R/4` of the mean, L2802–2813) or in Appendix B's denominator bookkeeping (`Ω = Γ^{m_test}` with `Γ = Δ^{2ℓ−1}`, L3072–3077 — these denominators have bit length `poly(n)`, fine, but the claim that all sums fit in `B_sum` bits should be checked against the Lean `*Height*`/`*Bounds*` modules).
* Discovery that the Lean program implements a different algorithm than the paper (the paper is exposition; the Lean program is what is verified).

### 8.7 External context (as of 2026-10-27)

* OpenAI's `history.md` states an independent working group led by **Russell Impagliazzo, Ramamohan Paturi and Ryan Williams** will examine the proof and asked for immediate release. No outcome from that group is public yet ([kingy.ai tracker](https://kingy.ai/mathematics-science-breakthrough-tracker/records/cs-exponential-time-hypothesis-refutation-openai-2026/), which also reports no completed independent verification).
* **Anthropic** released, the same day, *A `2^{o(n)}` Time Algorithm for 3-SAT* (credited to "Claude (Anthropic)"), claiming `#3-SAT` in `2^{O(n log log n/√log n)}`, with a Lean 4 formalization (`anthropics/formal-math/eth`, Lean `v4.33.1`, build ≈8 min on 24 vCPUs, Comparator + `nanoda` in CI, `MainResults.lean` states `ETHIsFalse` explicitly). Its README summarizes the key idea as tensor-network contraction with a recursive exponent inequality `e(9K^16) ≤ 0.9·e(K) + O(1/K)` and the decomposition `SWAP = I − 2·singlet`, grouping by the number of singlets. That is structurally the same mechanism as OpenAI's `M_0 = V_0 f(W_0)` (eigen-decomposition of commuting swaps, grouped by the count `j` of `−1` eigenvalues) and OpenAI's Appendix-E wire recursion. Two independent teams converging on the same algebraic object is evidence *for* the mechanism, but neither Lean build was reproduced here, and I am made by Anthropic — weigh accordingly. ([cellcog.ai summary](https://cellcog.ai/blog/claude-refutes-eth-3-sat/); [runtimewire](https://runtimewire.com/article/anthropic-posts-its-own-eth-refutation-hours-after-openai-as-lance-fortnow-says-); [John D. Cook](https://www.johndcook.com/blog/2026/10/27/eth-false/).)
* Shiva Kintali posted a 22-page "simplified proof" ([PDF](https://shivakintali.github.io/papers/ETH.pdf), 26 Oct 2026) that re-derives OpenAI's bounded-occurrence argument with a single parameter `s` (`r=s, Q=s⁴, R=s³, τ=s⁻⁶`) getting `2^{εn}` for every `ε`; it is exposition, not independent verification, and relies on IPZ sparsification without proof.
* Named expert reactions so far are cautious: Lance Fortnow — approach "looks promising", cannot vouch yet; Scott Aaronson merely reports the claim ([Shtetl-Optimized](https://scottaaronson.blog/), 26 Oct 2026 post). I found no published objection.

---

## 9. Three (Four) Research Directions

**First, why disproving ETH does not establish P = NP.** ETH false means `3-SAT ∈ DTIME(2^{δn})` for every `δ>0`. The algorithm's actual bound `2^{n/(log n)^{1/2+o(1)}}` is still `2^{n^{1−o(1)}}` — superpolynomial, in fact far above `2^{polylog(n)}`. P = NP would require `3-SAT ∈ DTIME(n^c)`, i.e. exponent `O(log n)`. Moreover, `2^{o(n)}` bounds do not survive polynomial-time reductions (a reduction that maps instances of size `n` to formulas with `n²` variables turns `2^{o(n)}` into `2^{o(n²)}`), which is why the paper itself says the result "does not imply that general NP problems admit subexponential time algorithms" (L149). Nothing in the construction has a polynomial-time flavour: the three enumerations are each `2^{Θ(n/√log n)}`.

### Direction 1 — Is `√log n` the limit of measurement–interpolation? (informed hypothesis)
* **Question.** Within the engine of Section 3 (any factors, Definition `def:layout`), is exponent `Θ(n/√log n)` optimal, or can a different family of commuting operators replace the `Q`-fold product of two-eigenvalue swaps to reach `2^{O(n/(log n)^c)}` for some `c > 1/2`, or `2^{n/polylog(n)}`?
* **Existing results.** The balance of §5: `R ≳ √(Q log(·))` from binomial concentration and `Q ≤ O(log n/log r)` from `D = r^{2Q}`. Appendix E's recursion already gains `(log log n)²` by recursing. Anthropic's recursion `e(9K^16) ≤ 0.9 e(K)+O(1/K)` lands at the same `1/√log`.
* **Proposed lemma.** *Any* design built from a product basis of `Q` commuting involutions on `r^{2Q}` coordinates whose correction `I−M_0` has rank `≤ εD` and whose rows have `≤ R−1` cross mismatches must satisfy `R = Ω(√(Q log(1/ε)))`. (If true, `√log n` is intrinsic to *this* algebra.) Converse conjecture: operators with eigenvalue multiplicities concentrated more sharply than binomial (e.g. from larger symmetric groups acting on pairs, or Hecke-type operators) would give `R = O(Q^{1/2−γ})`.
* **Why it matters.** It decides whether the method's ceiling is `n/√log n` or something like `n/polylog n`; the latter would be a qualitatively different regime (and would collide with several fine-grained reductions that only lose polylog factors).
* **Bounded experiment.** (i) Numerically minimize the three-cost expression under alternative tail-bound shapes `Pr[W∉𝓘] ≤ e^{−R^a/Q^b}` to see which `(a,b)` give `c>1/2`. (ii) Implement the Appendix-E wire recursion on small tensor networks (my Part-B harness is a starting point) and measure the achieved exponent empirically vs. `s`. (iii) Prove the proposed lower-bound lemma for product bases via Fourier analysis on `(Z/2)^Q` (anti-concentration of binomials).
* **Success / failure.** Success: either a sharper exponent or a clean no-go theorem for the swap algebra. Failure to improve teaches that the gain must come from *outside* the design (e.g. new sparsification trade-offs).
* **Status:** informed hypothesis.

### Direction 2 — Unbounded clause width and the fate of SETH-style hypotheses (informed hypothesis)
* **Question.** The constants `O_k` are exponential in `k` (sparsification `B = O_k((σ^{-1}log)^{k−1})`, `2^k` monomials per violation polynomial, `β` in `lem:incidence-parameters`). For which growth rates `k = k(n)` does the method still give `2^{(1−δ)n}` or `2^{o(n)}`? Concretely: does CNF-SAT with `k = O(log log n)` admit `2^{(1−δ)n}` for some `δ>0`?
* **Existing results.** Unrestricted CNF-SAT is known in `2^{n−n/O(log(m/n))}` (Calabro–Impagliazzo–Paturi; Dantsin–Hirsch–Wolpert) and the OV/3SUM/APSP lower bounds use the unbounded-width hypothesis (L350–365). Williams' MA-SETH refutation (2016).
* **Proposed conjecture.** Replace sparsification by direct parity tests on the original clauses (Section 6 needs only polylog incidence, not bounded width) and track `k` through `lem:total-order` (input degree `k(m_test+2ℓ)`) and `prop:count`: the exponent becomes `O(k·n/√log n)`-ish, so `k ≤ (log n)^{1/2−γ}` might still give `2^{o(n)}`.
* **Why it matters.** Would refute the "unrestricted CNF-SAT needs `2^{(1−δ)n}`" hypothesis and hence OVC, with consequences for edit distance, LCS, Fréchet, diameter lower bounds (L338–358).
* **Bounded experiment.** Audit every `O_k` in the proof and tabulate its explicit `k`-dependence (the Lean library has concrete constants, e.g. `425000(B+1)²+56B+11` in `SubexpCRTWeightedMachine.lean` L95 — extracting all of them is a mechanical but finite task). Then prove or refute a `2^{(1−δ)n}` bound for `k = c·log log n`.
* **Success / failure.** Success: SETH-for-growing-`k` falls, OVC falls. Failure: identifies the first step whose `k`-dependence is super-polynomial, locating the real boundary of the technique.
* **Status:** informed hypothesis.

### Direction 3 — Polynomial-size Circuit-SAT and `NEXP ⊄ P/poly` (speculative but precise)
* **Question.** The paper handles linear-size circuits (Tseitin ⇒ `O(n+s)` variables) in `2^{o(n)}`. Can "determined" gate variables be handled without counting them in the exponent, giving `#Circuit-SAT` for circuits of size `s = n^c` on `n` inputs in `2^{O(n/√log n)}·poly(s)`?
* **Existing results.** Williams (2010/2013, JACM/SICOMP): Circuit-SAT for poly-size circuits in `2^n/n^{ω(1)}` ⇒ `NEXP ⊄ P/poly`; ACC lower bounds via `2^{n−n^{ε}}` ACC-SAT (Williams 2011). The present paper's Cor. `cor:consequence-circuits` only reaches `E^NP ⊄ SIZE(O(n))`.
* **Proposed lemma.** In the engine, a factor whose scope contains a variable `z` that is a *deterministic function* of other variables can be eliminated from the Boolean sum (sum over inputs only) while keeping input degree `O(n)` if the gate fan-in is bounded and gates are evaluated inside the group-local products rather than as free Boolean coordinates. Obstacle: a gate reads inputs from *different* groups at point `t`; the design would need measurements of gate values, which are nonlinear.
* **Why it matters.** Even `2^{n−ω(log n)}·poly(s)` for `s = n^2` would give `NEXP ⊄ P/poly` — a breakthrough circuit lower bound; the ETH refutation already gives the first unconditional superlinear bound for `E^NP`.
* **Bounded experiment.** Extend `mechanism_test.py` to CNFs with Tseitin gate variables; try (a) assigning each gate to the group of one of its inputs and measuring only input variables, (b) a "two-layer" deformation (inputs deformed, gates recomputed). Determine empirically whether the separation property can hold for gate factors with *some* measurement budget `o(n)`.
* **Success / failure.** Success: NEXP circuit lower bounds. Failure: a concrete reason the measurement rank must grow with the number of gates — itself informative about why the technique stops at linear size.
* **Status:** speculative.

### Direction 4 — Dense counting: the permanent and #ETH for dense instances (speculative)
* **Question.** `cor:graph-counting` gives permanents/perfect matchings in `2^{o(v+e)}`; for dense bipartite graphs this is worse than Ryser's `2^v`. Is there a `2^{o(n)}` algorithm for the `n×n` 0/1 permanent?
* **Existing results.** Ryser `O(2^n n)`; Björklund 2016 "below all subsets" `2^{n−Ω(√(n/log n))}`; BKW19 fermionants; #ETH ⇒ no `2^{o(n)}` permanent for sparse graphs (Curticapean 2018) — now false by the paper for `O(n)` edges.
* **Proposed conjecture.** The permanent's polynomial `Σ_σ ∏ a_{iσ(i)}` has `n²` Boolean variables but a solution space of size `n!`; a design with `r` groups on *rows* and measurements on column-sums (which are linear!) might separate `∏_i (Σ_j a_{ij} x_{ij})` after fixing column multiplicities — a close cousin of Björklund's approach. The linear structure of the "exactly one per column" constraint is exactly what the measurement framework can exploit, so the conjecture is `#PerfectMatching(K_{n,n} weighted 0/1) ∈ 2^{O(n/√log n)}`.
* **Why it matters.** Would refute #ETH for the permanent (`#P`-complete via dense instances), and permanents sit at the base of many counting reductions.
* **Bounded experiment.** Implement the engine with factors `Φ_i = Σ_j a_{ij}x_{ij}` (row factors) and column-exactness as integer measurements `Σ_i x_{ij} = 1`; check whether input degree stays `O(n)` (it is `n`) and whether the count of measurement tuples is `2^{o(n)}` (it is `(2D+1)^{c}` with `c = n` columns — too many; so the question is whether the column constraints can be *folded into the Taylor recovery* instead).
* **Success / failure.** Success: new permanent algorithm. Failure: a precise statement of why dense constraints defeat linear measurements — a useful boundary.
* **Status:** speculative.

**On P vs NP.** None of these directions is likely to resolve P vs NP, and I have no rigorous argument that any technique here approaches polynomial time. What the result does change is the *landscape of plausible hardness hypotheses* below P ≠ NP: ETH-family hypotheses can no longer be used as axioms, which affects a large body of fine-grained and parameterized lower bounds.

---

## 10. Limitations and Unresolved Questions

1. **No kernel verification achieved here** (Mathlib cache blocked; 2 cores). This is the dominant limitation. Everything in §6 is static analysis.
2. **Comparator not run**, so statement-equality between the challenge file and the proved theorem is checked only by my textual comparison (definitions and theorem text are identical, but Lean elaboration can differ in principle, e.g. via instances).
3. **`enable_nanoda: false`** for this challenge: OpenAI's own CI, if it mirrors the config, re-checks with the Lean kernel only.
4. **Asymptotic lemmas and appendices** (`lem:incidence-parameters`, Appendix A tree bounds, Appendix B bit lengths, the expander construction, and the entire tensor-contraction Appendix D/E) were read but not independently re-proved or tested; the sharper Theorem-1.1 bounds are unformalized.
5. **My reproduction tests correctness, not complexity.** The regime where the parameters satisfy all hypotheses needs `n` far beyond anything executable (`D ≤ 2^{λ/128}` alone needs `λ` in the hundreds). The algorithm is of no practical use; this is consistent with both labs' statements.
6. **`O_k` constants are unquantified** in the paper; the Lean program fixes them but I did not extract them.
7. **Earlier manuscript missing.** `Main.lean` references *A Subexponential Algorithm for Bounded-Width SAT* which is not in the repository; the `SqrtLog` subtree (2,004 files) formalizes that target.
8. **External review pending.** The Impagliazzo–Paturi–Williams group has not reported. No independent party has publicly reported a successful build of the OpenAI library as of 27 Oct 2026 (the community `complexitylib` project has an open issue to port it).
9. **Potential bias**: I am an Anthropic model and Anthropic has a competing claim; I have confined use of Anthropic's materials to §8.7.

**Most important unresolved question:** compile `math/lean` at commit `7ef5c0cc…` with Mathlib cache access, run `#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, and run Comparator on `ComparatorChallenges/SubexponentialSAT.json`. Until then "machine-checked" is a claim, not an observation.

---

## 11. Reproduction Instructions

### 11.1 What was done here (reproducible in any sandbox with GitHub access)
```sh
mkdir -p ~/eth-research && cd ~/eth-research
git clone --depth 1 https://github.com/openai/math.git && cd math && git checkout 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
# toolchain (no elan network access needed):
curl -L -o lean.tar.zst https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst
python3 -c "import zstandard,tarfile;tarfile.open(fileobj=zstandard.ZstdDecompressor().stream_reader(open('lean.tar.zst','rb')),mode='r|').extractall('toolchain',filter='data')"
export PATH=$PWD/toolchain/lean-4.34.1-linux/bin:$PATH
cd lean && lake update            # resolves 42 packages; the Mathlib cache step needs cache.mathlib.org
# static audit:
grep -rn '\bsorry\b\|^\s*axiom\|native_decide\|implemented_by\|@\[extern\|\bunsafe\b' OAI/Algorithms/SubexponentialSAT
python3 -I ../../scripts/import_closure.py . OAI.Algorithms.SubexponentialSAT.Main
# mechanism reproduction (≈4 min, pure Python):
python3 -I ../../scripts/mechanism_test.py 1
```

### 11.2 What remains to do on a machine with network access and ≥16 GB RAM / ≥8 cores
```sh
cd math/lean
lake exe cache get                                        # Mathlib oleans (~5 GB)
lake build ComparatorChallenges.SubexponentialSAT         # challenge statement (imports all of Mathlib)
lake build OAI.Algorithms.SubexponentialSAT.Main          # 3,091 modules / 547k lines; expect hours
lake env lean -c /dev/null --run <(echo '#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat')
# or simply build SqrtLogSpace/Final.lean, which contains the #print axioms commands at L197-201
# Comparator (per lean/ComparatorChallenges/README.md): install comparator, landrun, lean4export; then
lake env comparator ComparatorChallenges/SubexponentialSAT.json
```
Expected (if the authors' claims hold): build succeeds; axioms = `[propext, Classical.choice, Quot.sound]`; Comparator reports the challenge theorem and solution theorem identical. Note the repository's `vm.max_map_count` warning in `lean/README.md` for full-library builds.

### 11.3 Files produced in this session
```
/home/user/eth-research/
├── REPORT.md                      (this file)
├── logs/commands.log              every command, timestamp, exit status
├── logs/elan-install.log, lean-toolchain.log, lake-update.log, lake-build-challenge.log, lake-build-bg.log
├── scripts/import_closure.py      import-closure analysis
├── scripts/mechanism_test.py      independent small-instance reproduction (Sections 2 & 4.2)
├── results/mechanism_test_seed{1,2,3}.log
├── toolchain/                     elan (unused), lean-4.34.1 (used)
├── math/                          pristine clone at 7ef5c0cc… (+ .lake/ dependency checkouts; no source edits)
└── external/formal-math/eth       Anthropic cross-reference (sparse checkout, read-only use)
```

---

## Sources

Primary (this session):
* OpenAI repository and paper: https://github.com/openai/math (commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`); paper `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf`; Lean scope `lean/docs/378.md`; challenge `lean/ComparatorChallenges/SubexponentialSAT.lean`/`.json`; proof `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean`.
* R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*, Theorem 6.1 (ETH false ⇒ `E^NP ⊄ SIZE(O(n))`): https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf (journal version SIAM J. Comput. 42(3), 2013).
* J. Alman, R. Williams, *Probabilistic rank and matrix rigidity*: https://arxiv.org/abs/1611.05558v2 (STOC 2017).
* Comparator: https://github.com/leanprover/comparator. Lean release: https://github.com/leanprover/lean4/releases/tag/v4.34.1.

Cited from the paper's bibliography (standard references, not re-fetched): Impagliazzo–Paturi 2001 (JCSS 62); Impagliazzo–Paturi–Zane 2001 (JCSS 63); Calabro–Impagliazzo–Paturi 2006 (CCC); Dell–Husfeldt–Marx–Taslaman–Wahlén 2014 (ACM TALG 10); Beigel–Tarui 1994 (Comput. Complexity 4); Chan–Williams 2021 (ACM TALG 17); Björklund 2016 (SODA); Björklund–Kaski–Williams 2019 (Algorithmica 81); Tanner 1981; Sipser–Spielman 1996; Naor–Naor 1993; Valiant 1979; Jerrum–Valiant–Vazirani 1986; Schöning 1999; Paturi–Pudlák–Saks–Zane 2005; Hertli 2014; Hansen–Kaplan–Zamir–Zwick 2019; Williams 2016 (MA-SETH).

Secondary / context:
* [John D. Cook, "The Exponential Time Hypothesis is False"](https://www.johndcook.com/blog/2026/10/27/eth-false/)
* [kingy.ai record on the OpenAI claim](https://kingy.ai/mathematics-science-breakthrough-tracker/records/cs-exponential-time-hypothesis-refutation-openai-2026/)
* [S. Kintali, *A simplified proof of ETH is false*](https://shivakintali.github.io/papers/ETH.pdf)
* [Anthropic `formal-math/eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth); [cellcog.ai summary](https://cellcog.ai/blog/claude-refutes-eth-3-sat/); [runtimewire (Fortnow quote)](https://runtimewire.com/article/anthropic-posts-its-own-eth-refutation-hours-after-openai-as-lance-fortnow-says-)
* [Shtetl-Optimized](https://scottaaronson.blog/) (26 Oct 2026 entry)
* [complexitylib issue #1226 (community port)](https://github.com/cslib-community/complexitylib/issues/1226)
* [Wikipedia: Exponential time hypothesis](https://en.wikipedia.org/wiki/Exponential_time_hypothesis)
