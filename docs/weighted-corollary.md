# Weighted rational factor corollary

Source: `main_full_version.tex` at `openai/math` commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` — Prop. `prop:general-count` (L2013–2030), Definition `def:layout` (L1714–1748), Lemma `lem:row-coefficients` (L2635), Lemma `lem:layout` (L2696), Lemma `lem:incidence-parameters` (L2747), branching on dense variables (L3109–3117), fallback (L3185–3197), Appendix B `app:arithmetic` (L3886–). Numerical sanity check: `scripts/weighted_test.py` (`results/weighted_test_seed7.log`).

## Corollary (conditional on the source's lemmas)

Let $S_a \subseteq [n]$ be explicitly specified scopes and let $\phi_a : \{0,1\}^{S_a} \to \mathbb{Q}$ be rational-valued factors given by explicit tables. Let $L$ be the total binary encoding length of the input tables and define

$$Z=\sum_{x\in\{0,1\}^n}\prod_a \phi_a(x|_{S_a}),\qquad M=\sum_a |S_a| .$$

Assume $M = O(n)$ and that every scope has size at most $(\log n)^c$ for a fixed constant $c$. Then the source's `general-count` algorithm, together with its layout construction and exact rational interpolation, computes $Z$ deterministically in

$$\operatorname{poly}(n,L)\; 2^{O\left(n(\log\log n)^2/\sqrt{\log n}\right)}$$

bit operations and polynomial space.

The corollary is conditional on the source's layout, parameter-selection and arithmetic lemmas, with the weighted-factor height bounds established below. It does not establish the sharper Appendix D tensor-contraction bound for arbitrary weighted tables.

## Proof

### 1. Rational-factor height and common denominators

Add a neutral unary factor equal to $1$ on $\{v\}$ for each $v \in [n]$. This changes neither $Z$ nor $M = O(n)$, and ensures $n \le M$. Empty-scope factors are assigned to group one, as in the source's layout construction.

For each table let $L_a$ be its encoding length, $q_a$ the product of its entry denominators, and

$$w_a=|S_a|,\qquad H_a=\max\Bigl(1,\max_{u\in\{0,1\}^{S_a}}|\phi_a(u)|\Bigr).$$

Then $\sum_a \log_2 q_a = O(L)$ and $\sum_a \log_2 H_a = O(L)$.

Let $\widetilde\phi_a$ be the unique multilinear extension of $\phi_a$. Its Möbius coefficients are $c_{a,U}=\sum_{T\subseteq U}(-1)^{|U|-|T|}\phi_a(\mathbf 1_T)$, so $|c_{a,U}| \le 2^{|U|}H_a \le 2^{w_a}H_a$ and $\|\widetilde\phi_a\|_1 \le 3^{w_a}H_a$. These estimates do not assume $w_a$ constant: the scope-dependent overhead is summed using $\sum_a w_a = M = O(n)$. The product of the multilinear extensions has degree at most $d \le \sum_a w_a = M = O(n)$ in the distinct incidence variables used by `general-count`, so the degree hypothesis (source L1689–1693) holds.

Use the source's common row denominator $\Delta=(R-1)!\,Q!$, with $\log_2\Delta = O(Q\log(Q+2))$. Lemma `lem:row-coefficients` bounds the integer coefficient $1$-norm of each $\Delta P_{a,v}(T)$ by $2^{O(Q\log Q)}$. After evaluation at $t+z$ with $0\le t\le Q$, the norm grows by at most $(Q+1)^R$; dot products with Boolean vectors and the correction terms $\langle \Delta P, \mathbf 1_U\rangle$ add at most a polynomial factor in $n$. Thus every substituted input form is $\theta_{a,v}(z)=A_{a,v}(z)/\Delta$ with integer polynomial numerator satisfying

$$\log_2\max(1,\|A_{a,v}\|_1)=O\bigl(Q\log(Q+2)+R\log(Q+1)+\log(n+2)\bigr),$$

which is $O(\log n)$ in the source's parameter regime. Let $K$ be a uniform bound on these norms, $\log_2 K = O(\log n)$.

After substitution, a factor of scope $w_a$ has denominator dividing $q_a\Delta^{w_a}$ and numerator $1$-norm at most $q_aH_a\,3^{w_a}\max(K,\Delta)^{w_a}$. A common denominator for the complete product is

$$\Omega=\prod_a q_a\Delta^{w_a},\qquad \log_2\Omega=O\bigl(L+MQ\log(Q+2)\bigr)=O(L+n\log n),$$

using $Q\log(Q+2)=O(\log n)$. By submultiplicativity, the product's coefficient $1$-norm has logarithm $O\bigl(L+\sum_a w_a\log(K+2)+M\bigr)=O(L+n\log n)$; the scope-dependent part is summed as $\sum_a O(w_a\log n)=M\cdot O(\log n)$, not bounded by the maximum scope times the number of factors.

### 2. Taylor-data height and exact interpolation

`general-count` examines at most $2Qr\,C_q(2D+1)^{2\tau n}2^{2n/r}$ Boolean vectors; for $d=O(n)$ the source's finite-difference estimate gives $\log_2 C_q = O\bigl(n\tfrac{R}{Q}\log\tfrac{2Q}{R}\bigr)$. Hence the logarithm of the number of accumulated terms is

$$O\Bigl(\log(Qr)+n\frac RQ\log\frac{2Q}{R}+\tau n\log(2D+1)+\frac nr\Bigr),$$

each term $O(n)$ under the selected parameters. Accumulation adds the logarithm of the term count to numerator bit length, not the count itself. The Taylor depth is $J=\lfloor dR/Q\rfloor+1=O(1+nR/Q)$; truncation modulo $z^J$ does not increase the $1$-norm. Combining the denominator, product-norm, accumulation and Taylor-depth bounds, the cleared interpolation-data coefficients have bit length

$$B_{\mathrm{data}}=O(L+n\log n)$$

up to polynomial-size bookkeeping. Thus exact factor evaluation and all rational arithmetic have polynomial bit cost.

For interpolation put $M_H=QJ$. The source's Hermite matrix has integer entries $\mathsf V_{(t,j),u}=\binom{u}{j}t^{u-j}$ for $u\ge j$ and $0$ otherwise ($t\in[Q]$, $0\le j<J$, $0\le u<M_H$); its dimension and entry bit lengths are polynomial. If $\mathbf y$ is the Taylor-data vector and $\mathbf h$ the coefficient vector of $H$, then $\mathsf V\mathbf h=\mathbf y$ with $h_0=H(0)=Z$. After clearing denominators, Cramer's rule gives $Z=\det\mathsf V^{(0)}/(\Omega\det\mathsf V)$, where $\mathsf V^{(0)}$ replaces the column $u=0$ by $\Omega\mathbf y$. The source's determinant-height bound and fraction-free Gaussian elimination compute the exact rational answer in polynomial bit complexity and space.

This uses only the factor-independent Hermite/interpolation part of Appendix B. The Beigel–Tarui lift, its $\Gamma$-denominator chain (source L3072–3077) and the integer-residue readout are not required.

### 3. Branching, layout feasibility, and exponential running time

Let $M$ include the neutral unary factors, so $n\le M=O(n)$. Set $\lambda=\lceil\log_2 n\rceil$ and $b_0=\lceil M/n\rceil\lceil\sqrt\lambda\rceil$. Let $S$ be the variables occurring in more than $b_0$ scopes; then $|S|\le M/b_0\le n/\sqrt\lambda$, so there are at most $2^{n/\sqrt\lambda}$ branches.

After fixing $x|_S=b$, each table is restricted to the fixed bits; surviving entries are selected from the original table, so a branch's representation length is $L'\le L+\operatorname{poly}(n)$. Branches are processed sequentially. In each restricted instance the maximum incidence satisfies $b\le b_0=O(\sqrt\lambda)$ (using $M=O(n)$), scopes stay polylogarithmic, and the neutral factors give $n'\le M'\le bn'$ for the free-variable count $n'$ and restricted incidence $M'$.

Choose a fixed $\beta$ with $b,w\le(\lambda')^\beta$, $\lambda'=\lceil\log_2 n'\rceil$, $\nu'=\lceil\log_2\lambda'\rceil$, and use the source's parameters

$$r=\Bigl\lfloor\frac{\sqrt{\lambda'}}{(\nu')^2}\Bigr\rfloor,\quad Q=\Bigl\lfloor\frac{\lambda'}{128\nu'}\Bigr\rfloor,\quad R=(\beta+3)\lceil\sqrt{\lambda'}\rceil,\quad \tau=\frac1{r\lambda'},\quad D=r^{2Q}.$$

Lemma `lem:layout` requires $2(b+w)D^2\le M'$, $2Qr^2\le n'$, $n'\le M'\le bn'$, plus the binomial-tail and interval conditions; Lemma `lem:incidence-parameters` shows they hold for all sufficiently large $n$. For any size at which a check fails, evaluate the weighted sum by exhaustive enumeration (polynomial bit cost per assignment); only finitely many sizes need this fallback, which is absorbed into the constants.

For feasible instances the three exponential-cost terms $\tfrac RQ\log\tfrac{2Q}{R}$, $\tau\log(2D+1)$, $\tfrac1r$ satisfy $R/Q=O(\nu'/\sqrt{\lambda'})$, $\log(2Q/R)=O(\nu')$, $\tau\log(2D+1)=O(1/r)$, $1/r=O((\nu')^2/\sqrt{\lambda'})$. The per-branch time is $\operatorname{poly}(n,L)\,2^{O(n'(\log\log n')^2/\sqrt{\log n'})}$; multiplying by at most $2^{n/\sqrt\lambda}$ branches preserves $\operatorname{poly}(n,L)\,2^{O(n(\log\log n)^2/\sqrt{\log n})}$. Sequential processing keeps the space polynomial. $\blacksquare$

## Scope

* **Not a new algorithm.** This applies the source's `general-count` routine and Appendix B arithmetic/interpolation framework to explicitly encoded rational tables. `prop:general-count` counts ring operations and explicitly requires the bit cost of general factor evaluators to be verified separately (source L2040–2044); §1–2 above close that obligation for weighted tables and are our derivation, not a statement in the source.
* Weight bit length enters only the polynomial factor, not the exponent.
* It does not establish the Appendix D tensor-contraction bound $2^{O(s/\sqrt{\log s})}$ for arbitrary weighted tables: that route works modulo $2^{P_0}$ with $P_0\le Cs$, which weights of super-constant bit length do not satisfy without further ideas.
* Real-valued weights are out of scope (no finite encoding).
