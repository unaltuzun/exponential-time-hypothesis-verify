/-!
Standalone core-Lean certificate for the precision-extension of Appendix D
(paper "The Exponential-Time Hypothesis is False — October 25, 2026",
repo `openai/math`, pinned commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`).

Core-Lean only (no Mathlib), compiles in isolation.  Final goal: the decisive
domination inequality used to relax the hypothesis `P_0 ≤ C·s` of
Theorem `thm:tensor-contraction` (`quantitative-reduction.tex`, line 36) to
`P_0 ≤ s·(log_2 s)^B` for any fixed B (Outcome A of the audit).

This version generalises the depth constant: the paper's `C` enters only
through `2^(6d) < C²·λ`; with `C² ≤ 2^(18+c)` the theorem holds for every `C`.
-/

namespace SubexponentialSAT.PrecisionExtensionCore

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-! ### Small numeric helpers -/

/-- `0 < 2^k`. -/
theorem two_pow_pos : ∀ k : Nat, 0 < 2 ^ k := by
  intro k
  induction k with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      exact Nat.mul_pos ih (by decide)

/-- `1 ≤ 2^k`. -/
theorem one_le_two_pow : ∀ k : Nat, 1 ≤ 2 ^ k := fun k => two_pow_pos k

/-- `t ≤ 2^t`. -/
theorem le_two_pow_self : ∀ t : Nat, t ≤ 2 ^ t := by
  intro t
  induction t with
  | zero => decide
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; decide
      · rw [Nat.pow_succ]
        have h2 : 2 * n ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        have h3 : n + 1 ≤ 2 * n := by omega
        omega

/-- `18 + d ≤ 2^d` for `d ≥ 5`. -/
theorem eighteen_add_d_le_pow : ∀ d : Nat, 5 ≤ d → 18 + d ≤ 2 ^ d := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge n 5 with hlt | hge
      · have hn : n = 4 := by omega
        subst hn
        decide
      · have hpow : 18 + n ≤ 2 ^ n := ih hge
        rw [Nat.pow_succ]
        omega

/-- First-order binomial slack: `(v+1)^t ≤ v^t + 2t·v^(t-1)` for `t ≥ 1`,
`v ≥ 2t`. -/
theorem succ_pow_le : ∀ t v : Nat, 1 ≤ t → 2 * t ≤ v →
    (v + 1) ^ t ≤ v ^ t + 2 * t * v ^ (t - 1) := by
  intro t
  induction t with
  | zero =>
      intro v h1 _
      exact absurd h1 (by omega)
  | succ t ih =>
      intro v h1 h2
      rcases Nat.eq_zero_or_pos t with h0 | htpos
      · subst h0
        have hx : (v + 1) ^ (0 + 1) = v + 1 := by
          rw [show (0: Nat) + 1 = 1 from rfl, Nat.pow_one]
        have hy : v ^ (0 + 1) = v := by
          rw [show (0: Nat) + 1 = 1 from rfl, Nat.pow_one]
        have hz : v ^ ((0 + 1) - 1) = 1 := by
          rw [show 0 + 1 - 1 = 0 from rfl, Nat.pow_zero]
        rw [hx, hy, hz]
        omega
      · have he : (t + 1) - 1 = t := by omega
        rw [he]
        -- goal: (v+1)^(t+1) ≤ v^(t+1) + 2*(t+1)*v^t
        have h2t : 2 * t ≤ v := by omega
        have hih : (v + 1) ^ t ≤ v ^ t + 2 * t * v ^ (t - 1) := ih v htpos h2t
        -- v^(t-1) * v = v^t  (needs t ≥ 1)
        have hkey1 : v ^ (t - 1) * v = v ^ ((t - 1) + 1) :=
          (Nat.pow_succ v (t - 1)).symm
        have hvv : v ^ (t - 1) * v = v ^ t := by
          rw [hkey1, show (t - 1) + 1 = t by omega]
        have hle : 2 * t * v ^ (t - 1) ≤ v ^ t := by
          have hkey : 2 * t * v ^ (t - 1) ≤ v * v ^ (t - 1) :=
            Nat.mul_le_mul_right _ h2t
          rw [Nat.mul_comm v (v ^ (t - 1)), hvv] at hkey
          exact hkey
        have e3 : v ^ (t + 1) = v ^ t * v := Nat.pow_succ v t
        have t1 : v ^ t * v = v ^ (t + 1) := e3.symm
        have t2 : 2 * t * v ^ (t - 1) * v = 2 * t * v ^ t := by
          rw [Nat.mul_assoc, hvv]
        have t3 : v ^ t * 1 = v ^ t := Nat.mul_one (v ^ t)
        have t4 : 2 * t * v ^ (t - 1) * 1 = 2 * t * v ^ (t - 1) := Nat.mul_one _
        have hrhs : v ^ (t + 1) + 2 * (t + 1) * v ^ t
            = v ^ (t + 1) + 2 * t * v ^ t + 2 * v ^ t := by
          rw [Nat.add_assoc]
          congr 1
          have e21 : 2 * (t + 1) = 2 * t + 2 := by omega
          rw [e21, Nat.add_mul]
        calc (v + 1) ^ (t + 1)
            = (v + 1) ^ t * (v + 1) := Nat.pow_succ (v + 1) t
          _ ≤ (v ^ t + 2 * t * v ^ (t - 1)) * (v + 1) :=
              Nat.mul_le_mul_right _ hih
          _ = (v ^ t + 2 * t * v ^ (t - 1)) * v + (v ^ t + 2 * t * v ^ (t - 1)) * 1 :=
              Nat.mul_add _ _ _
          _ = (v ^ t * v + 2 * t * v ^ (t - 1) * v)
                + (v ^ t * 1 + 2 * t * v ^ (t - 1) * 1) := by rw [Nat.add_mul, Nat.add_mul]
          _ = (v ^ (t + 1) + 2 * t * v ^ t) + (v ^ t + 2 * t * v ^ (t - 1)) := by
              rw [t1, t3, t2, t4]
          _ ≤ v ^ (t + 1) + 2 * t * v ^ t + 2 * v ^ t := by omega
          _ = v ^ (t + 1) + 2 * (t + 1) * v ^ t := hrhs.symm

/-- Corollary: `(v+1)^t ≤ 2·v^t` for `t ≥ 1`, `v ≥ 2t`. -/
theorem succ_pow_two : ∀ t v : Nat, 1 ≤ t → 2 * t ≤ v → (v + 1) ^ t ≤ 2 * v ^ t := by
  intro t v h1 h2
  have h := succ_pow_le t v h1 h2
  have hvv : v ^ (t - 1) * v = v ^ t := by
    have hkey1 : v ^ (t - 1) * v = v ^ ((t - 1) + 1) :=
      (Nat.pow_succ v (t - 1)).symm
    rw [hkey1, show (t - 1) + 1 = t by omega]
  have hle : 2 * t * v ^ (t - 1) ≤ v ^ t := by
    have hkey : 2 * t * v ^ (t - 1) ≤ v * v ^ (t - 1) :=
      Nat.mul_le_mul_right _ h2
    rw [Nat.mul_comm v (v ^ (t - 1)), hvv] at hkey
    exact hkey
  have : v ^ t + 2 * t * v ^ (t - 1) ≤ v ^ t + v ^ t := by omega
  omega

/-- Base monotonicity of `Nat.pow`: `1 ≤ a → m ≤ n → a^m ≤ a^n`. -/
theorem pow_mono_base : ∀ a m n : Nat, 1 ≤ a → m ≤ n → a ^ m ≤ a ^ n := by
  intro a m n
  induction n with
  | zero =>
      intro h1 hm
      have h0 : m = 0 := by omega
      subst h0
      exact Nat.le_refl _
  | succ n ih =>
      intro h1 hm
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hm' : m ≤ n := by omega
        have step : a ^ n ≤ a ^ (n + 1) := by
          rw [Nat.pow_succ]
          have hmul := Nat.mul_le_mul_left (a ^ n) h1
          rw [Nat.mul_one] at hmul
          exact hmul
        exact Nat.le_trans (ih h1 hm') step
      · have hme : m = n + 1 := by omega
        subst hme
        exact Nat.le_refl _

/-- Base monotonicity of `Nat.pow` with base bound: `a ≤ b → a^n ≤ b^n`. -/
theorem pow_le_pow_of_le_base : ∀ n a b : Nat, a ≤ b → a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => intro a b _; exact Nat.le_refl _
  | succ k ih =>
      intro a b hab
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul (ih a b hab) hab

/-- `2^v ≥ v^t` whenever `t ≥ 2` and `v ≥ 4t²`. -/
theorem two_pow_ge_pow : ∀ t v : Nat, 2 ≤ t → 4 * t * t ≤ v → 2 ^ v ≥ v ^ t := by
  intro t v ht h4
  have h1t : 1 ≤ t := by omega
  have powSelf : t ≤ 2 ^ t := le_two_pow_self t
  -- atom bridges so that `omega` can relate the different nonlinear shapes
  have hEq44 : 4 * t * t = (4: Nat) * (t * t) := Nat.mul_assoc 4 t t
  have hEqT2 : (t: Nat) * (2 * t) = 2 * (t * t) := by
    rw [Nat.mul_comm t (2 * t), Nat.mul_assoc]
  -- base case: (4t²)^t ≤ 2^(4t²)
  have base : (4 * t * t) ^ t ≤ 2 ^ (4 * t * t) := by
    have h2t : t + t = 2 * t := by omega
    have h2 : (4 * t * t) ^ t = 4 ^ t * ((t * t) ^ t) := by
      calc (4 * t * t) ^ t
          = (4 * (t * t)) ^ t := congrArg (fun x : Nat => x ^ t) (Nat.mul_assoc 4 t t)
        _ = 4 ^ t * ((t * t) ^ t) := Nat.mul_pow 4 (t * t) t
    have h5 : (4: Nat) ^ t = 2 ^ (2 * t) := by
      calc (4: Nat) ^ t
          = (2 * 2) ^ t := by rw [show (4: Nat) = 2 * 2 by decide]
        _ = 2 ^ t * 2 ^ t := Nat.mul_pow 2 2 t
        _ = 2 ^ (t + t) := (Nat.pow_add 2 t t).symm
        _ = 2 ^ (2 * t) := by rw [h2t]
    have hG : (t * t) ^ t ≤ 2 ^ (t * (2 * t)) := by
      calc (t * t) ^ t
          = t ^ t * t ^ t := Nat.mul_pow t t t
        _ = t ^ (t + t) := (Nat.pow_add t t t).symm
        _ = t ^ (2 * t) := by rw [h2t]
        _ ≤ (2 ^ t) ^ (2 * t) := pow_le_pow_of_le_base (2 * t) t (2 ^ t) powSelf
        _ = 2 ^ (t * (2 * t)) := (Nat.pow_mul 2 t (2 * t)).symm
    have hexp : 2 * t + t * (2 * t) ≤ 4 * t * t := by
      have hx0 : t * 1 ≤ t * t := Nat.mul_le_mul_left t h1t
      omega
    calc (4 * t * t) ^ t
        = 4 ^ t * ((t * t) ^ t) := h2
      _ ≤ 2 ^ (2 * t) * 2 ^ (t * (2 * t)) :=
            Nat.mul_le_mul (Nat.le_of_eq h5) hG
      _ = 2 ^ (2 * t + t * (2 * t)) := (Nat.pow_add 2 (2 * t) (t * (2 * t))).symm
      _ ≤ 2 ^ (4 * t * t) :=
            pow_mono_base 2 (2 * t + t * (2 * t)) (4 * t * t) (by decide) hexp
  -- induction over the offset from 4t²
  have main : ∀ n : Nat, (4 * t * t + n) ^ t ≤ 2 ^ (4 * t * t + n) := by
    intro n
    induction n with
    | zero =>
        have ez : 4 * t * t + 0 = 4 * t * t := by omega
        rw [ez]
        exact base
    | succ k ih =>
        have e : 4 * t * t + (k + 1) = (4 * t * t + k) + 1 := by omega
        rw [e]
        have hwt : 2 * t ≤ 4 * t * t + k := by
          have hx : 4 * t * 1 ≤ 4 * t * t := Nat.mul_le_mul_left (4 * t) h1t
          omega
        have hle1 : 1 ≤ t := by omega
        calc (4 * t * t + k + 1) ^ t
            ≤ 2 * (4 * t * t + k) ^ t := succ_pow_two t (4 * t * t + k) hle1 hwt
          _ ≤ 2 * 2 ^ (4 * t * t + k) := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (4 * t * t + k) * 2 := Nat.mul_comm _ _
          _ = 2 ^ ((4 * t * t + k) + 1) := (Nat.pow_succ 2 (4 * t * t + k)).symm
  have hoff : 4 * t * t + (v - 4 * t * t) = v := by omega
  rw [← hoff]
  exact main (v - 4 * t * t)

/-! ### Main precision-extension theorem, general depth constant -/

/-- General form of the Appendix-D domination inequality.  The paper's depth
bound `H < M ≤ C·s·8^(-d)` with `H ≥ s/√λ` gives `2^(6d) < C²·λ`; writing
`C² ≤ 2^(18+c)` for a natural `c` turns this into the hypothesis `hd` below
(`c = 0` is the previously certified case `C ≤ 512`).  The precision threshold
`N ≥ 2^(640+8c)` grows linearly in `c`.  Conclusion unchanged. -/
theorem precision_extension_general (c B N d u : Nat) (hB : B ≤ 2 ^ 20)
    (hN : 2 ^ (640 + 8 * c) ≤ N)
    (hd : 2 ^ (6 * d) ≤ 2 ^ (18 + c) * N) (hu : u = N / 2 ^ (17 + d)) :
    2 ^ u ≥ N ^ (B + 2) * u * 2 ^ 18 := by
  have hDpos : 0 < 2 ^ (17 + d) := two_pow_pos (17 + d)
  have hdm : 2 ^ (17 + d) * (N / 2 ^ (17 + d)) + N % 2 ^ (17 + d) = N :=
    Nat.div_add_mod N (2 ^ (17 + d))
  rw [← hu] at hdm
  have hmod : N % 2 ^ (17 + d) < 2 ^ (17 + d) := Nat.mod_lt _ hDpos
  -- Step A: 2^(512+c) ≤ u
  have hA : 2 ^ (512 + c) ≤ u := by
    have e1 : 2 ^ (17 + d) * 2 ^ (512 + c) = 2 ^ (529 + c + d) := by
      rw [← Nat.pow_add, show (17: Nat) + d + (512 + c) = 529 + c + d by omega]
    have hcancel : 2 ^ (17 + d) * 2 ^ (512 + c) ≤ N → 2 ^ (512 + c) ≤ u := by
      intro hz
      have q1 : 2 ^ (17 + d) * 2 ^ (512 + c) ≤ 2 ^ (17 + d) * u + N % 2 ^ (17 + d) := by
        rw [hdm]; exact hz
      have q2 : 2 ^ (17 + d) * u + N % 2 ^ (17 + d) < 2 ^ (17 + d) * u + 2 ^ (17 + d) := by
        omega
      have q4 : 2 ^ (17 + d) * (u + 1) = 2 ^ (17 + d) * u + 2 ^ (17 + d) := by
        rw [Nat.mul_add, Nat.mul_one]
      have q5 : 2 ^ (17 + d) * 2 ^ (512 + c) < 2 ^ (17 + d) * (u + 1) := by
        rw [q4]
        exact Nat.lt_of_le_of_lt q1 q2
      have s3 : 2 ^ (512 + c) < u + 1 := Nat.lt_of_mul_lt_mul_left q5
      clear hB hN hd hu hDpos hdm hmod q1 q2 q4 q5
      omega
    have hmono : ∀ m : Nat, 529 + c + d ≤ m → 2 ^ (17 + d) * 2 ^ (512 + c) ≤ 2 ^ m := by
      intro m hexp
      rw [e1]
      exact pow_mono_base 2 (529 + c + d) m (by decide) hexp
    rcases Nat.lt_or_ge d (112 + 7 * c) with hlt | hge
    · exact hcancel (Nat.le_trans (hmono (640 + 8 * c) (by omega)) hN)
    · have hN6 : 2 ^ (6 * d - (18 + c)) ≤ N := by
        have w0 : 2 ^ (6 * d - (18 + c)) * 2 ^ (18 + c) ≤ N * 2 ^ (18 + c) := by
          rw [Nat.mul_comm N (2 ^ (18 + c)), ← Nat.pow_add,
            show 6 * d - (18 + c) + (18 + c) = 6 * d by omega]
          exact hd
        exact Nat.le_of_mul_le_mul_right w0 (two_pow_pos (18 + c))
      exact hcancel (Nat.le_trans (hmono (6 * d - (18 + c)) (by omega)) hN6)
  have hA512 : 2 ^ 512 ≤ u :=
    Nat.le_trans (pow_mono_base 2 512 (512 + c) (by decide) (by omega)) hA
  have hule1 : 1 ≤ u := by omega
  -- Step B: N ≤ 2^(18+d) * u
  have hB2 : N ≤ 2 ^ (18 + d) * u := by
    have hB1 : N ≤ 2 ^ (17 + d) * (u + 1) := by
      have h11 : 2 ^ (17 + d) * (u + 1) = 2 ^ (17 + d) * u + 2 ^ (17 + d) := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    have h12 : 2 ^ (18 + d) = 2 ^ (17 + d) * 2 := by
      rw [show (18: Nat) + d = (17 + d) + 1 by omega, Nat.pow_succ]
    have h13 : 2 ^ (17 + d) * 1 ≤ 2 ^ (17 + d) * u :=
      Nat.mul_le_mul_left _ hule1
    have h14 : 2 ^ (18 + d) * u = 2 * (2 ^ (17 + d) * u) := by
      calc 2 ^ (18 + d) * u
          = (2 ^ (17 + d) * 2) * u := by rw [h12]
        _ = 2 ^ (17 + d) * (2 * u) := Nat.mul_assoc _ _ _
        _ = 2 * (2 ^ (17 + d) * u) := Nat.mul_left_comm _ _ _
    omega
  -- Step C: 2^(5d) ≤ 2^(36+c) * u
  have hC : 2 ^ (5 * d) ≤ 2 ^ (36 + c) * u := by
    have e5 : 2 ^ (6 * d) = 2 ^ (5 * d) * 2 ^ d := by
      rw [← Nat.pow_add, show (5: Nat) * d + d = 6 * d by omega]
    have e6 : 2 ^ (18 + c) * (2 ^ (18 + d) * u) = 2 ^ d * (2 ^ (36 + c) * u) := by
      calc 2 ^ (18 + c) * (2 ^ (18 + d) * u)
          = 2 ^ (18 + c) * 2 ^ (18 + d) * u := (Nat.mul_assoc (2 ^ (18 + c)) (2 ^ (18 + d)) u).symm
        _ = 2 ^ ((18 + c) + (18 + d)) * u := by rw [Nat.pow_add 2 (18 + c) (18 + d)]
        _ = 2 ^ (d + (36 + c)) * u := by rw [show (18 + c) + (18 + d) = d + (36 + c) by omega]
        _ = (2 ^ d * 2 ^ (36 + c)) * u := by rw [Nat.pow_add 2 d (36 + c)]
        _ = 2 ^ d * (2 ^ (36 + c) * u) := Nat.mul_assoc _ _ _
    have s1 : 2 ^ (5 * d) * 2 ^ d ≤ 2 ^ d * (2 ^ (36 + c) * u) := by
      rw [← e5, ← e6]
      exact Nat.le_trans hd (Nat.mul_le_mul_left (2 ^ (18 + c)) hB2)
    have s1' : 2 ^ (5 * d) * 2 ^ d ≤ (2 ^ (36 + c) * u) * 2 ^ d := by
      have q1 : (2 ^ (36 + c) * u) * 2 ^ d = 2 ^ d * (2 ^ (36 + c) * u) := Nat.mul_comm _ _
      rw [q1]
      exact s1
    exact Nat.le_of_mul_le_mul_right s1' (two_pow_pos d)
  -- Step F: 2*(18+X) ≤ u, where X = (18+d)*(B+2)
  have hF : 2 * (18 + (18 + d) * (B + 2)) ≤ u := by
    rcases Nat.lt_or_ge d 19 with hlt | hge
    · -- d ≤ 18: small-numeric branch
      have c20 : (2: Nat) ^ 20 = 1048576 := by decide
      have hk1 : 18 + d ≤ 36 := by omega
      have hk2 : B + 2 ≤ 2 ^ 20 + 2 := by omega
      rw [c20] at hk2
      have hk3 : (18 + d) * (B + 2) ≤ 36 * (1048576 + 2) := Nat.mul_le_mul hk1 hk2
      have w1 : 2 * (18 + (18 + d) * (B + 2)) ≤ 36 + 72 * (1048576 + 2) := by
        omega
      have w2 : 36 + 72 * (1048576 + 2) ≤ 2 ^ 512 := by
        have c27 : (2: Nat) ^ 27 = 134217728 := by decide
        have w27 : 36 + 72 * (1048576 + 2) ≤ 2 ^ 27 := by
          rw [c27]; omega
        exact Nat.le_trans w27 (pow_mono_base 2 27 512 (by decide) (by omega))
      exact Nat.le_trans (Nat.le_trans w1 w2) hA512
    · -- d ≥ 19
      have hk3 : (18 + d) * (B + 2) ≤ 2 ^ (d + 21) := by
        have w1 : 18 + d ≤ 2 ^ d := eighteen_add_d_le_pow d (by omega)
        have w2 : B + 2 ≤ 2 ^ 21 := by omega
        have w3 : 2 ^ (d + 21) = 2 ^ d * 2 ^ 21 := Nat.pow_add 2 d 21
        have s1 := Nat.mul_le_mul w1 w2
        rw [← w3] at s1
        exact s1
      have w4 : 2 * (18 + (18 + d) * (B + 2)) ≤ 2 ^ (d + 23) := by
        calc 2 * (18 + (18 + d) * (B + 2))
            ≤ 36 + 2 * 2 ^ (d + 21) := by omega
          _ ≤ 2 ^ (d + 23) := by
              have a22 : 2 ^ (d + 22) = 2 ^ (d + 21) * 2 := by
                rw [show d + 22 = (d + 21) + 1 by omega, Nat.pow_succ]
              have a23 : 2 ^ (d + 23) = 2 ^ (d + 22) * 2 := by
                rw [show d + 23 = (d + 22) + 1 by omega, Nat.pow_succ]
              have w36 : 2 ^ 6 ≤ 2 ^ (d + 22) :=
                pow_mono_base 2 6 (d + 22) (by decide) (by omega)
              have w62 : (2: Nat) ^ 6 = 64 := by decide
              have w36' : 36 ≤ 2 ^ (d + 22) := by
                rw [w62] at w36; omega
              omega
      rcases Nat.lt_or_ge (d + 23) (513 + c) with hsmall | hbig
      · -- d + 23 ≤ 512 + c: use Step A directly
        exact Nat.le_trans w4
          (Nat.le_trans (pow_mono_base 2 (d + 23) (512 + c) (by decide) (by omega)) hA)
      · -- d ≥ 490 + c: use Step C
        have w4' : 2 ^ (d + 23) ≤ 2 ^ (5 * d - (36 + c)) :=
          pow_mono_base 2 (d + 23) (5 * d - (36 + c)) (by decide) (by omega)
        have w5 : 2 ^ (5 * d - (36 + c)) ≤ u := by
          have a1 : 2 ^ (5 * d - (36 + c)) * 2 ^ (36 + c) = 2 ^ (5 * d) := by
            rw [← Nat.pow_add, show 5 * d - (36 + c) + (36 + c) = 5 * d by omega]
          have a2 : 2 ^ (5 * d - (36 + c)) * 2 ^ (36 + c) ≤ u * 2 ^ (36 + c) := by
            rw [a1, Nat.mul_comm u (2 ^ (36 + c))]
            exact hC
          exact Nat.le_of_mul_le_mul_right a2 (two_pow_pos (36 + c))
        exact Nat.le_trans w4 (Nat.le_trans w4' w5)
  -- Step HK: u^(B+3) ≤ 2^(u - E) with E = 18 + (18+d)*(B+2)
  have hE : 18 + (18 + d) * (B + 2) ≤ u - (18 + (18 + d) * (B + 2)) := by
    omega
  have w511 : 2 ^ 511 ≤ u - (18 + (18 + d) * (B + 2)) := by
    have e512 : (2: Nat) ^ 512 = 2 * 2 ^ 511 := by
      rw [show (512: Nat) = 511 + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    clear hA
    omega
  have wHi1 : 1 ≤ u - (18 + (18 + d) * (B + 2)) := by omega
  have wle : u ≤ (u - (18 + (18 + d) * (B + 2)))
      + (u - (18 + (18 + d) * (B + 2))) := by omega
  have wge2 : 2 ≤ u - (18 + (18 + d) * (B + 2)) := by omega
  have w2k : (u - (18 + (18 + d) * (B + 2))) * 2
      ≤ (u - (18 + (18 + d) * (B + 2))) * (u - (18 + (18 + d) * (B + 2))) :=
    Nat.mul_le_mul_left _ wge2
  have e4 : u ≤ (u - (18 + (18 + d) * (B + 2))) ^ 2 := by
    have hpow : (u - (18 + (18 + d) * (B + 2))) ^ 2
        = (u - (18 + (18 + d) * (B + 2))) * (u - (18 + (18 + d) * (B + 2))) := by
      rw [show (2: Nat) = 1 + 1 by omega, Nat.pow_succ, Nat.pow_one]
    omega
  have HI : u ^ (2 ^ 21) ≤ (u - (18 + (18 + d) * (B + 2))) ^ (2 ^ 22) := by
    have e2221 : (2: Nat) ^ 22 = 2 * 2 ^ 21 := by
      rw [show (22: Nat) = 21 + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    calc u ^ (2 ^ 21)
        ≤ ((u - (18 + (18 + d) * (B + 2))) ^ 2) ^ (2 ^ 21) :=
          pow_le_pow_of_le_base (2 ^ 21) u
            ((u - (18 + (18 + d) * (B + 2))) ^ 2) e4
      _ = (u - (18 + (18 + d) * (B + 2))) ^ (2 * 2 ^ 21) :=
          (Nat.pow_mul (u - (18 + (18 + d) * (B + 2))) 2 (2 ^ 21)).symm
      _ = (u - (18 + (18 + d) * (B + 2))) ^ (2 ^ 22) := by rw [e2221]
  have hupos : 1 ≤ u := hule1
  have hJJ : u ^ (B + 3) ≤ u ^ (2 ^ 21) :=
    pow_mono_base u (B + 3) (2 ^ 21) hupos (by omega)
  have hH : (u - (18 + (18 + d) * (B + 2))) ^ (2 ^ 22)
      ≤ 2 ^ (u - (18 + (18 + d) * (B + 2))) :=
    two_pow_ge_pow (2 ^ 22) (u - (18 + (18 + d) * (B + 2))) (by decide) (by
      have tt : (2: Nat) ^ 22 * 2 ^ 22 = 2 ^ 44 := by
        rw [← Nat.pow_add, show 22 + 22 = 44 by omega]
      have e46 : 4 * 2 ^ 22 * 2 ^ 22 = 2 ^ 46 := by
        calc (4: Nat) * 2 ^ 22 * 2 ^ 22
            = 4 * ((2: Nat) ^ 22 * 2 ^ 22) := Nat.mul_assoc _ _ _
          _ = 4 * 2 ^ 44 := by rw [tt]
          _ = 2 ^ 46 := by
              calc (4: Nat) * 2 ^ 44
                  = 2 ^ 2 * 2 ^ 44 := by rw [show (4: Nat) = 2 ^ 2 by decide]
                _ = 2 ^ (2 + 44) := (Nat.pow_add 2 2 44).symm
                _ = 2 ^ 46 := by rw [show (2: Nat) + 44 = 46 by omega]
      have g1 : 2 ^ 46 ≤ 2 ^ 511 := pow_mono_base 2 46 511 (by decide) (by omega)
      rw [e46]
      exact Nat.le_trans g1 w511)
  have HK : u ^ (B + 3) ≤ 2 ^ (u - (18 + (18 + d) * (B + 2))) :=
    Nat.le_trans (Nat.le_trans hJJ HI) hH
  -- Step L: N^(B+2) ≤ 2^((18+d)*(B+2)) * u^(B+2)
  have huprod : u ^ (B + 2) * u = u ^ (B + 3) := by
    rw [← Nat.pow_succ u (B + 2), show (B: Nat) + 2 + 1 = B + 3 by omega]
  have hL : N ^ (B + 2) ≤ 2 ^ ((18 + d) * (B + 2)) * u ^ (B + 2) := by
    have hL0 : N ^ (B + 2) ≤ (2 ^ (18 + d) * u) ^ (B + 2) :=
      pow_le_pow_of_le_base (B + 2) N (2 ^ (18 + d) * u) hB2
    have hLfin : (2 ^ (18 + d) * u) ^ (B + 2)
        = 2 ^ ((18 + d) * (B + 2)) * u ^ (B + 2) := by
      rw [Nat.mul_pow, Nat.pow_mul]
    exact Nat.le_trans hL0 (Nat.le_of_eq hLfin)
  -- Final assembly
  calc N ^ (B + 2) * u * 2 ^ 18
      = 2 ^ 18 * (N ^ (B + 2) * u) := Nat.mul_comm _ _
    _ ≤ 2 ^ 18 * (2 ^ ((18 + d) * (B + 2)) * (u ^ (B + 2) * u)) := by
        have c1 : N ^ (B + 2) * u
            ≤ (2 ^ ((18 + d) * (B + 2)) * u ^ (B + 2)) * u :=
          Nat.mul_le_mul_right u hL
        have c2 : (2 ^ ((18 + d) * (B + 2)) * u ^ (B + 2)) * u
            = 2 ^ ((18 + d) * (B + 2)) * (u ^ (B + 2) * u) := Nat.mul_assoc _ _ _
        exact Nat.mul_le_mul_left _ (Nat.le_trans c1 (Nat.le_of_eq c2))
    _ = 2 ^ 18 * (2 ^ ((18 + d) * (B + 2)) * u ^ (B + 3)) := by
        congr 1
    _ = (2 ^ 18 * 2 ^ ((18 + d) * (B + 2))) * u ^ (B + 3) :=
        (Nat.mul_assoc (2 ^ 18) (2 ^ ((18 + d) * (B + 2))) (u ^ (B + 3))).symm
    _ ≤ 2 ^ (18 + (18 + d) * (B + 2)) * u ^ (B + 3) :=
        Nat.mul_le_mul_right _
          (Nat.le_of_eq ((Nat.pow_add 2 18 ((18 + d) * (B + 2))).symm))
    _ ≤ 2 ^ (18 + (18 + d) * (B + 2))
          * 2 ^ (u - (18 + (18 + d) * (B + 2))) :=
        Nat.mul_le_mul_left _ HK
    _ = 2 ^ ((18 + (18 + d) * (B + 2)) + (u - (18 + (18 + d) * (B + 2)))) :=
        (Nat.pow_add 2 (18 + (18 + d) * (B + 2))
          (u - (18 + (18 + d) * (B + 2)))).symm
    _ = 2 ^ u := by
        rw [show (18: Nat) + (18 + d) * (B + 2) + (u - (18 + (18 + d) * (B + 2)))
          = u by omega]



/-- The previously certified statement (`C ≤ 512`) is the case `c = 0`. -/
theorem precision_extension (B N d u : Nat) (hB : B ≤ 2 ^ 20) (hN : 2 ^ 640 ≤ N)
    (hd : 2 ^ (6 * d) ≤ 2 ^ 18 * N) (hu : u = N / 2 ^ (17 + d)) :
    2 ^ u ≥ N ^ (B + 2) * u * 2 ^ 18 :=
  precision_extension_general 0 B N d u hB hN hd hu

end SubexponentialSAT.PrecisionExtensionCore

#print axioms SubexponentialSAT.PrecisionExtensionCore.precision_extension_general
#print axioms SubexponentialSAT.PrecisionExtensionCore.precision_extension
