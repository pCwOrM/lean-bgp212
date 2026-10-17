/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.1 (p. 4), Definition 7.1 (p. 26), Lemmas 5.3–5.7
(pp. 16–17), Definition 7.4 (p. 28), Lemmas 7.5–7.7 (pp. 29–31), Proposition 7.8 and its
proof (pp. 31–36), Lemma 7.10 and Theorem 7.11 (p. 36), Theorem 8.3 (p. 39), Table 3.
-/
import BGP212.Packing

/-! # A4: the objects of Theorem 7.11

Core Lean. Theorem 7.11 reads: "For the rational datum in Table 3, every modulus generated
by the support is covered by Bombieri–Vinogradov, the half-level theorem, or one of
Stadlmann's positive-level Type I, Type II, and Type III estimates." Its proof: "Lemma 7.10
proves conditions A–E of Proposition 7.8 … Theorem 8.3 supplies the sub-half, transition,
and endpoint blocks, and the strict positive-level walls license the remaining blocks
through the estimates of Section 5."

This file transcribes, for a general datum, every combinatorial object that proof uses:

* `SupportDatum`: Definition 4.1's constraints on `(A, B, δ, ε)`.
* `Xi`: Definition 7.4, a single tuple of length `m₁ + m₂` (the source's form).
* `Prop78Scalar`, `Prop78Packing`: the hypotheses (I)–(III) and (A)–(E) of Proposition 7.8,
  quantified exactly as printed: all bands `j, j′ ≤ n`, all `m, m′ ≤ ⌊1/δ⌋`, `m + m′ > 0`.
* `PermI` … `PermIII`: the permissible triples of Lemmas 5.3–5.7, with a margin `η`
  (`η = 0` is the printed strict form; `η > 0` is the "room to spare" of p. 16).
* `dIlow` … `dIII`: the auxiliary widths `δ*(γ)` chosen in the proof of Proposition 7.8.
* `WinI` …: the divisor windows of `D_I … D_III` in logarithmic form (closed windows, the
  form Lemmas 7.5–7.7 deliver).
* `ContainX`: the containments `Q ⊆ D_X` of the proof of Proposition 7.8, in log-size form.
* `AnalyticInputs`: the analytic estimates, each a named hypothesis.

Log-size conventions follow Lemmas 7.5–7.7 as formalized in A2: for Lemmas 7.5 and 7.6 the
profile `y` is the rough logs scaled by `1/(1 − ε₀)` (Definition 4.3 (iii)), so a divisor's
log-size is `(1 − ε₀)·Σ y + Σ z`; for Lemma 7.7 the profile is the rough logs themselves. -/

namespace BGP212.T711

open BGP212.Params BGP212.Packing

/-! ## Definition 4.1 -/

/-- `⌊1/δ⌋` as a natural number. -/
def floorInv (δ' : Rat) : Nat := (1 / δ').floor.toNat

/-- **Definition 4.1** (constraints on the datum): `−ε = A₀ < A₁ < ⋯ < Aₙ < 1/2 − ε`, and
`B` an `n × ⌊1/δ⌋` matrix with `δ < B_{j,m} ≤ B_{j,m+1} ≤ B_{j,m} + δ` whenever both sides are
defined, `B_{j,0} = 0`. -/
def SupportDatum (n : Nat) (A : Nat → Rat) (Bm : Nat → Nat → Rat) (δ' ε : Rat) : Prop :=
  0 < δ' ∧ 0 < ε ∧ A 0 = -ε ∧ (∀ j, j < n → A j < A (j + 1)) ∧ A n < 1 / 2 - ε ∧
    ∀ j, 1 ≤ j → j ≤ n →
      Bm j 0 = 0 ∧ (∀ m, 1 ≤ m → m ≤ floorInv δ' → δ' < Bm j m) ∧
      ∀ m, 1 ≤ m → m + 1 ≤ floorInv δ' → Bm j m ≤ Bm j (m + 1) ∧ Bm j (m + 1) ≤ Bm j m + δ'

/-! ## Table 3 as a datum -/

/-- Table 3's bands: `n = 1`, `(A₀, A₁) = (−1/125, 257/1000)`. -/
def A3 (j : Nat) : Rat := if j = 0 then A0 else A1

/-- Table 3's caps `B_{1,m}` (Definition 4.1's `B_{j,0} = 0`); one band. -/
def B3 (_j m : Nat) : Rat := B m

/-! ## Definition 7.4 -/

/-- **Definition 7.4.** `Ξ(B₁, B₂, m₁, m₂, δ)`: tuples in `[δ, 1]^{m₁+m₂}` whose first `m₁`
coordinates sum to at most `B₁` and whose last `m₂` sum to at most `B₂`. -/
def Xi (B1 B2 : Rat) (m1 m2 : Nat) (δ' : Rat) (ys : List Rat) : Prop :=
  ys.length = m1 + m2 ∧ (∀ y ∈ ys, δ' ≤ y ∧ y ≤ 1) ∧
    (ys.take m1).sum ≤ B1 ∧ (ys.drop m1).sum ≤ B2

/-! ## Proposition 7.8: hypotheses -/

/-- `ω(j, j′) = (A_j + A_j′)/2 − 1/4`. -/
def omegaJJ (A : Nat → Rat) (j j' : Nat) : Rat := (A j + A j') / 2 - 1 / 4

/-- (A), first partition (the range γ ≤ 1/2). -/
def capsA1G (ξ1' ω' ϵ : Rat) : List Rat := [ξ1' - 2 * ϵ, 1 / 6 - 4 * ω' - 2 * ϵ]
/-- (A), second partition (the range γ ∈ (1/2, 1/2 + 2ω + ε]). -/
def capsA2G (ω' ϵ : Rat) : List Rat := [1 / 2 - 2 * ω' - 2 * ϵ, 1 / 14 - 68 / 14 * ω' - 2 * ϵ]
/-- (B), Type IIa. -/
def capsBG (ω' δ' ϵ : Rat) : List Rat :=
  [2 / 5 + 24 * ω' / 5 + 7 * δ' / 5 - 2 * ϵ, 1 / 14 - 24 * ω' / 7 - 2 * ϵ]
/-- (C), Type IIb. -/
def capsCG (ω' δ' ϵ : Rat) : List Rat :=
  [1 / 3 + 24 * ω' / 3 + 7 * δ' / 3 - 4 * ϵ, 1 / 10 - 34 * ω' / 5 - 7 * δ' / 5 - 4 * ϵ,
   2 * ω' + δ' - 4 * ϵ]
/-- (D), Type IIc, at `(γ, ω₀)`. -/
def capsDG (γ ω0 δ' ϵ : Rat) : List Rat :=
  [γ - 2 * δ' - 8 * ω0 - ϵ, 1 / 2 - γ - 2 * ω0 - ϵ, 4 * ω0 + δ' - ϵ, 8 * ω0]
/-- (E), Type III. -/
def capsEG (ξ3' ω' ϵ : Rat) : List Rat :=
  [1 - 6 * ω' - 3 * ξ3' / 2 - 2 * ϵ, 5 * ω' / 2 + 3 * ξ3' / 8 - 2 * ϵ]

/-- Conditions (A)–(E) of Proposition 7.8 for one tuple, at band pair parameter `ω`. -/
def CondsAE (ξ1' ξ2' ξ3' ω' δ' ϵ : Rat) (ys : List Rat) : Prop :=
  (Packs (capsA1G ξ1' ω' ϵ) ys ∧ Packs (capsA2G ω' ϵ) ys) ∧
  Packs (capsBG ω' δ' ϵ) ys ∧
  Packs (capsCG ω' δ' ϵ) ys ∧
  (∀ ω0 γ, 0 ≤ ω0 → ω0 ≤ ω' → ξ2' - ϵ ≤ γ → γ ≤ 1 / 3 + 24 * ω' / 3 + 7 * δ' / 3 + 3 * ϵ →
    Packs (capsDG γ ω0 δ' ϵ) ys) ∧
  Packs (capsEG ξ3' ω' ϵ) ys

/-- **Proposition 7.8, packing hypotheses (A)–(E)**, quantified as printed: for all
`j, j′ ∈ {1, …, n}` and all `m, m′ ∈ {0, 1, …, ⌊1/δ⌋}` with `m + m′ > 0`, every tuple of
`Ξ(B_{j,m}, B_{j′,m′}, m, m′, δ)` has properties (A)–(E). -/
def Prop78Packing (n : Nat) (A : Nat → Rat) (Bm : Nat → Nat → Rat)
    (δ' ξ1' ξ2' ξ3' ϵ : Rat) : Prop :=
  ∀ j j', 1 ≤ j → j ≤ n → 1 ≤ j' → j' ≤ n →
    ∀ m m', m ≤ floorInv δ' → m' ≤ floorInv δ' → 0 < m + m' →
      ∀ ys, Xi (Bm j m) (Bm j' m') m m' δ' ys →
        CondsAE ξ1' ξ2' ξ3' (omegaJJ A j j') δ' ϵ ys

/-- **Proposition 7.8, scalar hypotheses (I)–(III).** -/
def Prop78Scalar (n : Nat) (A : Nat → Rat) (δ' ξ1' ξ2' ξ3' ϵ : Rat) : Prop :=
  -- (I) Type I
  min (ξ1' - 4 * A n + 2 / 3) (9 / 7 - 34 / 7 * A n) - 2 * ϵ > δ' ∧
  -- (II) Type II
  19 / 2 - 36 * A n - 13 * δ' - 9 * ϵ ≥ 0 ∧
  min (ξ2' / 10 - 32 * A n / 10 + 8 / 10) (ξ2' / 4 + 11 / 16 - 3 * A n) - 2 * ϵ ≥ δ' ∧
  -- (III) Type III
  11 / 8 - 7 / 2 * A n - 9 / 8 * ξ3' - 2 * ϵ > δ'

/-! ## Lemmas 5.3–5.7: permissible triples (with margin `η`) -/

/-- Lemma 5.3 (Type I). `ε` is the lemma's local retreat. -/
def PermI (η ω' γ δs ε : Rat) : Prop :=
  (γ ≤ 1 / 2 → 3 * γ - 12 * ω' - 3 * δs - η > 1) ∧
  (1 / 2 < γ → γ ≤ 1 / 2 + 2 * ω' + ε → 68 * ω' + 14 * δs + η < 1)
/-- Lemma 5.4 (Type IIa). -/
def PermIIa (η ω' γ δs : Rat) : Prop :=
  24 * ω' + 7 * δs - 5 * γ + η < -2 ∧ 8 * ω' + 3 * δs - γ + η < 0
/-- Lemma 5.5 (Type IIb). -/
def PermIIb (η ω' γ δs : Rat) : Prop :=
  24 * ω' + 7 * δs - 3 * γ + η < -1 ∧ 8 * ω' + 3 * δs - γ + η < 0
/-- Lemma 5.6 (Type IIc). -/
def PermIIc (η ω' γ δs : Rat) : Prop :=
  8 * ω' + 4 * δs + 2 * γ + η < 1 ∧ 32 * ω' + 10 * δs - γ + η < 0 ∧
    48 * ω' + 16 * δs - 4 * γ + η < -1
/-- Lemma 5.7 (Type III). -/
def PermIII (η ω' γ δs : Rat) : Prop := 28 * ω' + 9 * γ + 8 * δs + η < 4

/-! ## The proof of Proposition 7.8: ranges and widths `δ*(γ)` -/

/-- Type I, `γ ≤ 1/2`: `δ*(γ) = γ − 4ω − 1/3 − ϵ`. -/
def dIlow (ω' γ ϵ : Rat) : Rat := γ - 4 * ω' - 1 / 3 - ϵ
/-- Type I, `γ ∈ (1/2, 1/2 + 2ω + ε]`: the top of the printed interval
`[δ, 1/14 − 68ω/14 − ϵ]`. -/
def dIhigh (ω' ϵ : Rat) : Rat := 1 / 14 - 68 / 14 * ω' - ϵ
/-- Type IIa: `δ*(γ) = 5γ/7 − 2/7 − 24ω/7 − ϵ`. -/
def dIIa (ω' γ ϵ : Rat) : Rat := 5 * γ / 7 - 2 / 7 - 24 * ω' / 7 - ϵ
/-- Type IIb: `δ*(γ) = 3γ/7 − 1/7 − 24ω/7 − ϵ`. -/
def dIIb (ω' γ ϵ : Rat) : Rat := 3 * γ / 7 - 1 / 7 - 24 * ω' / 7 - ϵ
/-- Type III as printed: `δ* = 1/2 − 7ω/2 − 9ξ₃/8 − ϵ`. -/
def dIIIprinted (ω' ξ3' ϵ : Rat) : Rat := 1 / 2 - 7 / 2 * ω' - 9 / 8 * ξ3' - ϵ
/-- Type III, A4's choice: `δ* = 1/2 − 7ω/2 − 9ξ₃/8 − 11ϵ/8` (see `type_III_printed_gap`). -/
def dIII (ω' ξ3' ϵ : Rat) : Rat := 1 / 2 - 7 / 2 * ω' - 9 / 8 * ξ3' - 11 * ϵ / 8

/-- The upper end of the IIc range and lower end of the IIb range. -/
def gIIc (ω' δ' ϵ : Rat) : Rat := 1 / 3 + 24 * ω' / 3 + 7 * δ' / 3 + 3 * ϵ
/-- The upper end of the IIb range and lower end of the IIa range. -/
def gIIa (ω' δ' ϵ : Rat) : Rat := 2 / 5 + 24 * ω' / 5 + 7 * δ' / 5 + 2 * ϵ

/-! ## Divisor windows (log form) and the containments `Q ⊆ D_X` -/

/-- Lemma 7.5's conclusion in log-size form: rough parts `I₁, I₂` of the profile and a smooth
selection `J` with `log_x r = (1 − ε₀)Σ_{I₁} y + Σ_J z ∈ [a, b]`. -/
def HasDiv1 (ε0 a b : Rat) (ys zs : List Rat) : Prop :=
  ∃ y1 y2 J R : List Rat, ys.Perm (y1 ++ y2) ∧ zs.Perm (J ++ R) ∧
    a ≤ (1 - ε0) * y1.sum + J.sum ∧ (1 - ε0) * y1.sum + J.sum ≤ b

/-- Lemma 7.6's conclusion: `r` from `(I₁, J₁)` in `[a₁, b₁]` and `u` from `(I₂, J₂)` in
`[a₂, b₂]`, disjoint. -/
def HasDiv2 (ε0 a1 b1 a2 b2 : Rat) (ys zs : List Rat) : Prop :=
  ∃ y1 y2 y3 J2 J1 R : List Rat, ys.Perm (y1 ++ y2 ++ y3) ∧ zs.Perm (J2 ++ J1 ++ R) ∧
    a2 ≤ (1 - ε0) * y2.sum + J2.sum ∧ (1 - ε0) * y2.sum + J2.sum ≤ b2 ∧
    a1 ≤ (1 - ε0) * y1.sum + J1.sum ∧ (1 - ε0) * y1.sum + J1.sum ≤ b1

/-- Lemma 7.7's conclusion: `u` from `(I₂, J₂)` in `[a₂, b₂]`, `r` from `(I₁, I₄, J₁)` in
`[a₁, b₁]`, and for every `c ∈ [a₁, b₁]` a `d₁ | r` from `(I₁, J′)`, `J′ ⊆ J₁`, in
`[2c + a₃, 2c + b₃]` (with `c = log_x r`: `d₁ ∈ [r² x^{a₃}, r² x^{b₃}]`). -/
def HasDiv3 (a1 b1 a2 b2 a3 b3 : Rat) (ys zs : List Rat) : Prop :=
  ∃ y1 y2 y3 y4 J2 J1 R : List Rat, ys.Perm (y1 ++ y2 ++ y3 ++ y4) ∧ zs.Perm (J2 ++ J1 ++ R) ∧
    a2 ≤ y2.sum + J2.sum ∧ y2.sum + J2.sum ≤ b2 ∧
    a1 ≤ y1.sum + y4.sum + J1.sum ∧ y1.sum + y4.sum + J1.sum ≤ b1 ∧
    ∀ c : Rat, a1 ≤ c → c ≤ b1 →
      ∃ J' R' : List Rat, J1.Perm (J' ++ R') ∧
        2 * c + a3 ≤ y1.sum + J'.sum ∧ y1.sum + J'.sum ≤ 2 * c + b3

/-- A rough profile of a Table 3 modulus: `ys ∈ Ξ(B_{1,m}, B_{1,m′}, m, m′, δ)` for some
`m, m′ ≤ ⌊1/δ⌋` (the single band `j = j′ = 1`). -/
def Profile3 (ys : List Rat) : Prop :=
  ∃ m m', m ≤ floorInv δ ∧ m' ≤ floorInv δ ∧ Xi (B m) (B m') m m' δ ys

/-- Smooth prime logs: each below `δ`. -/
def Smooth (zs : List Rat) : Prop := ∀ z ∈ zs, z < δ

/-- **Type I, `γ ≤ 1/2`: `Q ⊆ D_I`.** Every Table 3 modulus above `x^{1/2 − ε₁}` has
`r | q` with `log_x r ∈ [γ − δ*(γ) − 3ε′, γ − 3ε′]`, for every `γ ∈ [ξ₁ − ϵ, 1/2]`. -/
def ContainIlow : Prop :=
  ∀ γ ε' ε0 ε1 : Rat, ξ1 - εa ≤ γ → γ ≤ 1 / 2 → 0 < ε' → 3 * ε' ≤ εa → 0 < ε0 → ε0 < 1 →
    0 ≤ ε1 → ε1 ≤ ε0 * (1 / 2 - (γ - dIlow ω11 γ εa - 3 * ε')) →
    ∀ ys zs, Profile3 ys → Smooth zs → 1 / 2 - ε1 < (1 - ε0) * ys.sum + zs.sum →
      HasDiv1 ε0 (γ - dIlow ω11 γ εa - 3 * ε') (γ - 3 * ε') ys zs

/-- **Type I, `γ ∈ (1/2, 1/2 + 2ω + ε′]`: `Q ⊆ D_I`.** Window
`[1 − γ − δ* − 3ε′, 1 − γ − 3ε′]` with `δ* = dIhigh`. -/
def ContainIhigh : Prop :=
  ∀ γ ε' ε0 ε1 : Rat, 1 / 2 < γ → γ ≤ 1 / 2 + 2 * ω11 + ε' → 0 < ε' → 3 * ε' ≤ εa →
    0 < ε0 → ε0 < 1 → 0 ≤ ε1 → ε1 ≤ ε0 * (1 / 2 - (1 - γ - dIhigh ω11 εa - 3 * ε')) →
    ∀ ys zs, Profile3 ys → Smooth zs → 1 / 2 - ε1 < (1 - ε0) * ys.sum + zs.sum →
      HasDiv1 ε0 (1 - γ - dIhigh ω11 εa - 3 * ε') (1 - γ - 3 * ε') ys zs

/-- **Type IIa: `Q ⊆ D_IIa`** for `γ ∈ [gIIa, 1/2]`; window `[γ − 3ε′ − δ*, γ − 3ε′]`. -/
def ContainIIa : Prop :=
  ∀ γ ε' ε0 ε1 : Rat, gIIa ω11 δ εa ≤ γ → γ ≤ 1 / 2 → 0 < ε' → 3 * ε' ≤ εa →
    0 < ε0 → ε0 < 1 → 0 ≤ ε1 → ε1 ≤ ε0 * (1 / 2 - (γ - 3 * ε' - dIIa ω11 γ εa)) →
    ∀ ys zs, Profile3 ys → Smooth zs → 1 / 2 - ε1 < (1 - ε0) * ys.sum + zs.sum →
      HasDiv1 ε0 (γ - 3 * ε' - dIIa ω11 γ εa) (γ - 3 * ε') ys zs

/-- **Type IIb: `Q ⊆ D_IIb`** for `γ ∈ (gIIc, gIIa)`; `r ∈ [γ − 3ε′ − δ*, γ − 3ε′]`,
`u ∈ [1/2 − γ − 2ω − 6ε′ − δ*, 1/2 − γ − 2ω − 6ε′]`. -/
def ContainIIb : Prop :=
  ∀ γ ε' ε0 ε1 : Rat, gIIc ω11 δ εa < γ → γ < gIIa ω11 δ εa → 0 < ε' → 9 * ε' ≤ εa →
    0 < ε0 → ε0 < 1 → 0 ≤ ε1 →
    ε1 ≤ ε0 * (1 / 2 - (γ - 3 * ε') - (1 / 2 - γ - 2 * ω11 - 6 * ε' - dIIb ω11 γ εa)) →
    ∀ ys zs, Profile3 ys → Smooth zs → 1 / 2 - ε1 < (1 - ε0) * ys.sum + zs.sum →
      HasDiv2 ε0 (γ - 3 * ε' - dIIb ω11 γ εa) (γ - 3 * ε')
        (1 / 2 - γ - 2 * ω11 - 6 * ε' - dIIb ω11 γ εa) (1 / 2 - γ - 2 * ω11 - 6 * ε') ys zs

/-- **Type IIc: `Q ⊆ D_IIc`** for `γ ∈ [ξ₂ − ϵ, gIIc]`, `ω₀ ∈ [0, ω]`, `δ* = δ`, on the block
`log_x q ≥ 1/2 + 2ω₀` (with `log_x d = 1/2 + 2ω₀` in the windows): `r ∈ [γ − 3ε′ − δ, γ − 3ε′]`,
`u ∈ [1 − γ − 6ε′ − δ − L, 1 − γ − 6ε′ − L]`, `d₁ ∈ [2c + 2 − γ − 52ε′ − δ − 4L, 2c + 2 − γ − 52ε′ − 4L]`,
`L = 1/2 + 2ω₀`. -/
def ContainIIc : Prop :=
  ∀ γ ω0 ε' : Rat, ξ2 - εa ≤ γ → γ ≤ gIIc ω11 δ εa → 0 ≤ ω0 → ω0 ≤ ω11 →
    0 ≤ ε' → 58 * ε' ≤ εa →
    ∀ ys zs, Profile3 ys → Smooth zs → 1 / 2 + 2 * ω0 ≤ ys.sum + zs.sum →
      HasDiv3 (γ - 3 * ε' - δ) (γ - 3 * ε')
        (1 - γ - 6 * ε' - δ - (1 / 2 + 2 * ω0)) (1 - γ - 6 * ε' - (1 / 2 + 2 * ω0))
        (2 - γ - 52 * ε' - δ - 4 * (1 / 2 + 2 * ω0)) (2 - γ - 52 * ε' - 4 * (1 / 2 + 2 * ω0))
        ys zs

/-- **Type III: `Q ⊆ D_III`**; window `[1/3 + 4δ*/3 − 4ω/3 − δ*, 1/3 + 4δ*/3 − 4ω/3]`,
`δ* = dIII`. -/
def ContainIII : Prop :=
  ∀ ε0 ε1 : Rat, 0 < ε0 → ε0 < 1 → 0 ≤ ε1 →
    ε1 ≤ ε0 * (1 / 2 - (1 / 3 + 4 * dIII ω11 ξ3 εa / 3 - 4 * ω11 / 3 - dIII ω11 ξ3 εa)) →
    ∀ ys zs, Profile3 ys → Smooth zs → 1 / 2 - ε1 < (1 - ε0) * ys.sum + zs.sum →
      HasDiv1 ε0 (1 / 3 + 4 * dIII ω11 ξ3 εa / 3 - 4 * ω11 / 3 - dIII ω11 ξ3 εa)
        (1 / 3 + 4 * dIII ω11 ξ3 εa / 3 - 4 * ω11 / 3) ys zs

/-! ## Theorem 7.11: the analytic inputs as named hypotheses -/

/-- **Named analytic inputs of Theorem 7.11.** Each field is a hypothesis, outside the proved
scope. The `Eq*` fields are the equidistribution statements of Definition 5.2 for the
modulus sets `D_X(x; ω, γ, δ; ε)` (opaque here); `PositiveLevel` is Proposition 7.8's
displayed bound for every `f ∈ H(ξ₁, ξ₂, ξ₃)` over `Q*`; `HalfLevel` is Theorem 8.3's. -/
structure AnalyticInputs where
  EqI : Rat → Rat → Rat → Rat → Prop
  EqIIa : Rat → Rat → Rat → Prop
  EqIIb : Rat → Rat → Rat → Prop
  EqIIc : Rat → Rat → Rat → Prop
  EqIII : Rat → Rat → Rat → Prop
  PositiveLevel : Prop
  HalfLevel : Prop
  /-- Lemma 5.3 (Type I; Baker–Irving). -/
  lemma_5_3 : ∀ ω' γ δs ε, PermI 0 ω' γ δs ε → EqI ω' γ δs ε
  /-- Lemma 5.4 (Type IIa; Polymath8a Theorem 2.8(iv)). -/
  lemma_5_4 : ∀ ω' γ δs, PermIIa 0 ω' γ δs → EqIIa ω' γ δs
  /-- Lemma 5.5 (Type IIb; Polymath8a Theorem 2.8(ii)). -/
  lemma_5_5 : ∀ ω' γ δs, PermIIb 0 ω' γ δs → EqIIb ω' γ δs
  /-- Lemma 5.6 (Type IIc; Stadlmann). -/
  lemma_5_6 : ∀ ω' γ δs, PermIIc 0 ω' γ δs → EqIIc ω' γ δs
  /-- Lemma 5.7 (Type III; Polymath8a Theorem 2.8(v)). -/
  lemma_5_7 : ∀ ω' γ δs, PermIII 0 ω' γ δs → EqIII ω' γ δs
  /-- The assembly step of Proposition 7.8 (with Remark 7.9's Lemma 8.1 for the moduli
  below `x^{1/2 − ε₁}`, Proposition 7.2's decomposition, and `log_x` of products): the
  estimates on the sets `D_X` at the proof's parameters, together with the containments
  `Q ⊆ D_X`, give the bound over `Q*`. -/
  prop_7_8_assembly :
    (∀ γ ε, ξ1 - εa ≤ γ → γ ≤ 1 / 2 → EqI ω11 γ (dIlow ω11 γ εa) ε) →
    (∀ γ ε, 1 / 2 < γ → γ ≤ 1 / 2 + 2 * ω11 + ε → EqI ω11 γ (dIhigh ω11 εa) ε) →
    (∀ γ, gIIa ω11 δ εa ≤ γ → γ ≤ 1 / 2 → EqIIa ω11 γ (dIIa ω11 γ εa)) →
    (∀ γ, gIIc ω11 δ εa < γ → γ < gIIa ω11 δ εa → EqIIb ω11 γ (dIIb ω11 γ εa)) →
    (∀ γ, ξ2 - εa ≤ γ → γ ≤ gIIc ω11 δ εa → EqIIc ω11 γ δ) →
    EqIII ω11 (ξ3 + εa) (dIII ω11 ξ3 εa) →
    ContainIlow → ContainIhigh → ContainIIa → ContainIIb → ContainIIc → ContainIII →
    PositiveLevel
  /-- Theorem 8.3 (half-level coverage: Lemma 8.1 on `Q_BV`, Table 2 and Lemma 8.2 on
  `Q_tr`, endpoint partitions on `Q₀`), from Proposition 7.8's packing hypotheses. -/
  theorem_8_3 :
    Prop78Packing 1 A3 B3 δ ξ1 ξ2 ξ3 εa → PositiveLevel → HalfLevel

end BGP212.T711
