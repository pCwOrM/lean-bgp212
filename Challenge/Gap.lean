/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §2, Definition 4.1, Definition 4.5, Lemma 4.9, Theorem 4.10,
Theorem 11.1 and §9.3, Lemma 12.1, the proof of Theorem 1.1 (§12).
-/
import BGP212.Gap

/-! # B3: the final deduction

Statements only; proofs live in `Solution/Gap.lean`. Objects are defined in
`BGP212/Gap.lean`. -/

namespace BGP212.Challenge

open BGP212.Params BGP212.T711 BGP212.Gap Filter

/-- `H₁ = liminf (p_{n+1} − p_n) ≤ D` from `H1Le D`. -/
theorem h1_liminf {D : ℕ} (h : H1Le D) : Filter.liminf primeGap atTop ≤ D :=
  sorry

/-- **DHL[k, 2] ⇒ H₁ ≤ D** for any admissible `k`-tuple of diameter at most `D` (§2: "DHL[k, 2]
implies H₁ ≤ H(k)"). -/
theorem dhl_implies_gap (k D : ℕ) (H : Finset ℤ) (hcard : H.card = k) (hadm : AdmissibleZ H)
    (hdiam : ∀ a ∈ H, ∀ b ∈ H, b - a ≤ D) (hdhl : DHL k 2) : H1Le D :=
  sorry

/-- Lemma 12.1 for the `ℤ`-shift form of `H₄₅`: 45 elements, admissible, diameter 212. -/
theorem h45Z_facts :
    BGP212.WTrick.H45Z.card = 45 ∧ AdmissibleZ BGP212.WTrick.H45Z ∧
      ∀ a ∈ BGP212.WTrick.H45Z, ∀ b ∈ BGP212.WTrick.H45Z, b - a ≤ 212 :=
  sorry

/-- **DHL[45, 2] ⇒ H₁ ≤ 212** (the last sentence of the proof of Theorem 1.1). -/
theorem dhl_45_implies_gap : DHL 45 2 → H1Le 212 :=
  sorry

/-- **Lemma 4.9's W-trick step, prime-factor form**: every prime `p ≤ w` divides `W`;
`gcd(b + h, W) = 1` on `H`; every prime dividing a difference of distinct shifts is at most
`w`; a solution `n ≡ b (mod W)`, `n ≡ −h (mod D_h)` exists. Then the `D_h` are coprime to `W`
and pairwise coprime. -/
theorem wtrick_coprime_of_primes (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ)
    (hW : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ W)
    (hb : ∀ h ∈ H, Int.gcd (b + h) W = 1)
    (hn : (W : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hdiff : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∀ p : ℕ, p.Prime → (p : ℤ) ∣ h - h' → p ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) W) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') :=
  sorry

/-- **Lemma 4.9's W-trick step, as printed**: the shifts differ by at most `w`. -/
theorem wtrick_coprime (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ)
    (hW : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ W)
    (hb : ∀ h ∈ H, Int.gcd (b + h) W = 1)
    (hn : (W : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hsmall : ∀ h ∈ H, ∀ h' ∈ H, (h - h').natAbs ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) W) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') :=
  sorry

/-- The W-trick step at `W = ∏_{p ≤ w} p` (Definition 4.5). -/
theorem wtrick_coprime_primorial (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (w : ℕ)
    (hb : ∀ h ∈ H, Int.gcd (b + h) (primorial w) = 1)
    (hn : (primorial w : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hsmall : ∀ h ∈ H, ∀ h' ∈ H, (h - h').natAbs ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) (primorial w)) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') :=
  sorry

/-- The combined modulus `q = W · ∏ D_h` is squarefree. -/
theorem wtrick_modulus_squarefree (H : Finset ℤ) (D : ℤ → ℕ) (W : ℕ) (hW : Squarefree W)
    (hD : ∀ h ∈ H, Squarefree (D h)) (hcopW : ∀ h ∈ H, Nat.Coprime (D h) W)
    (hcop : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h')) :
    Squarefree (W * ∏ h ∈ H, D h) :=
  sorry

/-- Every prime dividing a nonzero difference of `H₄₅` is at most 103. -/
theorem h45_diff_primes : ∀ a ∈ BGP212.WTrick.H45Z, ∀ c ∈ BGP212.WTrick.H45Z, a ≠ c →
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a - c → p ≤ 103 :=
  sorry

/-- **B2 → Lemma 4.9 for `H₄₅`**: for `w ≥ 103`, B2's residue `b` and the coprimality of every
compatible system of moduli. -/
theorem h45_wtrick_coprime (w : ℕ) (hw : 103 ≤ w) :
    ∃ b : ℕ, (∀ h ∈ BGP212.H45, Nat.gcd (b + h) (primorial w) = 1) ∧
      ∀ (n : ℤ) (D : ℤ → ℕ), (primorial w : ℤ) ∣ n - b →
        (∀ h ∈ BGP212.WTrick.H45Z, (D h : ℤ) ∣ n + h) →
        (∀ h ∈ BGP212.WTrick.H45Z, Nat.Coprime (D h) (primorial w)) ∧
          ∀ h ∈ BGP212.WTrick.H45Z, ∀ h' ∈ BGP212.WTrick.H45Z, h ≠ h' →
            Nat.Coprime (D h) (D h') :=
  sorry

/-- The bound 103 is sharp: at `w = 102` the moduli for the shifts 0 and 206 can share 103. -/
theorem h45_wtrick_sharp (b : ℕ) :
    ∃ (n : ℤ) (D : ℤ → ℕ), (primorial 102 : ℤ) ∣ n - b ∧
      (∀ h ∈ BGP212.WTrick.H45Z, (D h : ℤ) ∣ n + h) ∧
      (0 : ℤ) ∈ BGP212.WTrick.H45Z ∧ (206 : ℤ) ∈ BGP212.WTrick.H45Z ∧
      ¬ Nat.Coprime (D 0) (D 206) :=
  sorry

/-- The prime bound on differences is needed. -/
theorem wtrick_needs_prime_bound :
    ∃ (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ),
      (∀ p : ℕ, p.Prime → p ≤ w → p ∣ W) ∧ (∀ h ∈ H, Int.gcd (b + h) W = 1) ∧
      (W : ℤ) ∣ n - b ∧ (∀ h ∈ H, (D h : ℤ) ∣ n + h) ∧
      ∃ h ∈ H, ∃ h' ∈ H, h ≠ h' ∧ ¬ Nat.Coprime (D h) (D h') :=
  sorry

/-- The condition `gcd(b + h, W) = 1` is needed. -/
theorem wtrick_needs_coprime_residue :
    ∃ (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ),
      (∀ p : ℕ, p.Prime → p ≤ w → p ∣ W) ∧ (W : ℤ) ∣ n - b ∧ (∀ h ∈ H, (D h : ℤ) ∣ n + h) ∧
      ∃ h ∈ H, ¬ Nat.Coprime (D h) W :=
  sorry

/-- Table 3 is a valid Stadlmann support (Definition 4.1, `k = 45`). -/
theorem table3_valid : table3Support.Valid :=
  sorry

/-- The origin lies in Table 3's support set `T₄₅` (Definition 4.1, band `j = 1`). -/
theorem zero_mem_table3Support : (fun _ => (0 : ℝ)) ∈ table3Support.supportSet :=
  sorry

/-- **The final deduction, relative to its named inputs**: Theorem 7.11's named analytic
inputs `A` and the sieve inputs `S` (Theorem 4.10, Theorem 11.1, and the identification of
Theorem 7.11's conclusion with Definition 4.4) give DHL[45, 2] and `H₁ ≤ 212`. -/
theorem final_deduction (A : AnalyticInputs) (S : SieveInputs A) : DHL 45 2 ∧ H1Le 212 :=
  sorry

end BGP212.Challenge
