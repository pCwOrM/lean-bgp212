/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Lemma 4.2 (p. 4), §7.2 and Lemmas 7.5–7.7 (pp. 28–31),
§8.2, Table 2 and Lemma 8.2 (p. 38), Lemma 9.2 (p. 41).
-/

/-! # A2: the combinatorial layer

Statements only; proofs live in `Solution/A2Combinatorial.lean`.

**Log-size form.** Lemmas 7.5–7.7 concern a modulus `q = e e′ ∏ fᵢ ∏ f′ᵢ`. Their proofs
work entirely with logarithmic sizes: rough-factor logs `yᵢ ≥ δ` and smooth prime-factor
logs `zᵢ < δ`, a divisor being a choice of factors and its log-size the sum. These
statements are exactly that log-size content. A selection of smooth primes is a list `J`
with `zs.Perm (J ++ R)`, so disjoint selections are disjoint sublists of the multiset
`zs`. The translation `log_x (∏ factors) = Σ log_x (factor)` is the standard
multiplicativity of `log` and stays outside this file.

**Explicit smallness.** Where a source proof says "provided ϵ is sufficiently small
compared to ε₀", the statement carries the exact inequality that proof uses. -/

namespace BGP212.Challenge

/-- **Lemma 4.2 (hereditary rough-mass bound).** `ys` lists the coordinates of `t`
exceeding `δ` (the set `I`); `B q` is the band's cap `B_{j,q}`, with the one-step bound
`B_{j,q+1} ≤ B_{j,q} + δ` of Definition 4.1. Every sub-collection `zs` of `I` (a subset
`I′ ⊆ I`) satisfies `Σ_{I′} tᵢ ≤ B_{j,|I′|}`. -/
theorem lemma_4_2 (δ : Rat) (B : Nat → Rat) (hB : ∀ q : Nat, B (q + 1) ≤ B q + δ)
    (ys : List Rat) (hrough : ∀ y ∈ ys, δ < y) (hcap : ys.sum ≤ B ys.length)
    (zs : List Rat) (hsub : zs.Sublist ys) :
    zs.sum ≤ B zs.length :=
  sorry

/-- **§7.2, the smooth-insertion mechanism** ("inserting its prime factors one at a time
moves a partial product by at most x^δ, so any target interval of logarithmic width at
least δ can be hit exactly"). From a start `s ≤ b` whose total reach `s + Σ zs` is at
least `a`, with every step `z < δ ≤ b − a`, some selection `J` of the steps lands
`s + Σ J` in `[a, b]`. -/
theorem smooth_insertion (a b δ : Rat) (hw : δ ≤ b - a) (zs : List Rat)
    (hz : ∀ z ∈ zs, z < δ) (s : Rat) (hs : s ≤ b) (hreach : a ≤ s + zs.sum) :
    ∃ J R : List Rat, zs.Perm (J ++ R) ∧ a ≤ s + J.sum ∧ s + J.sum ≤ b :=
  sorry

/-- **Lemma 7.5 (two-factor extraction), log-size form.** `y1`, `y2` are the parts
`I₁`, `I₂` of the rough profile (each `yᵢ ≥ δ`, scaled by `1/(1 − ε₀)` as in the source
proof); `zs` are the smooth prime logs; `q > x^{1/2 − ϵ}` reads as the strict lower bound
on the total log-size. Conclusion: a divisor `r` with `log_x r ∈ [a, b]`, built from the
`I₁` factors and a selection `J` of smooth primes. -/
theorem lemma_7_5 (a b δ ε0 ϵ : Rat)
    (ha : 0 < a) (hb : b < 1 / 2) (hδ0 : 0 < δ) (hδ : δ ≤ b - a)
    (hε0 : 0 < ε0) (hε1 : ε0 < 1) (hϵ0 : 0 ≤ ϵ) (hϵ : ϵ ≤ ε0 * (1 / 2 - a))
    (y1 y2 : List Rat) (hy : ∀ y ∈ y1 ++ y2, δ ≤ y)
    (hI1 : y1.sum ≤ b) (hI2 : y2.sum ≤ 1 / 2 - a)
    (zs : List Rat) (hz : ∀ z ∈ zs, z < δ)
    (hq : 1 / 2 - ϵ < (1 - ε0) * (y1.sum + y2.sum) + zs.sum) :
    ∃ J R : List Rat, zs.Perm (J ++ R) ∧
      a ≤ (1 - ε0) * y1.sum + J.sum ∧ (1 - ε0) * y1.sum + J.sum ≤ b :=
  sorry

/-- **Lemma 7.6 (three-factor extraction), log-size form.** Parts `I₁, I₂, I₃` with the
source's capacities `b₁`, `b₂`, `1/2 − b₁ − a₂`. Conclusion: disjoint smooth selections
`J₂` (for `u`) and `J₁` (for `r`) with `log_x u ∈ [a₂, b₂]` and `log_x r ∈ [a₁, b₁]`. -/
theorem lemma_7_6 (a1 a2 b1 b2 δ ε0 ϵ : Rat)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hb1 : b1 < 1 / 2) (hb2 : b2 < 1 / 2) (hδ0 : 0 < δ)
    (h12 : a1 - a2 ≤ b1 - b2) (hsum : b1 + b2 < 1 / 2)
    (hw1 : δ ≤ b1 - a1) (hw2 : δ ≤ b2 - a2)
    (hε0 : 0 < ε0) (hε1 : ε0 < 1) (hϵ0 : 0 ≤ ϵ) (hϵ : ϵ ≤ ε0 * (1 / 2 - b1 - a2))
    (y1 y2 y3 : List Rat) (hy : ∀ y ∈ y1 ++ y2 ++ y3, δ ≤ y)
    (hI1 : y1.sum ≤ b1) (hI2 : y2.sum ≤ b2) (hI3 : y3.sum ≤ 1 / 2 - b1 - a2)
    (zs : List Rat) (hz : ∀ z ∈ zs, z < δ)
    (hq : 1 / 2 - ϵ < (1 - ε0) * (y1.sum + y2.sum + y3.sum) + zs.sum) :
    ∃ J2 J1 R : List Rat, zs.Perm (J2 ++ J1 ++ R) ∧
      a2 ≤ (1 - ε0) * y2.sum + J2.sum ∧ (1 - ε0) * y2.sum + J2.sum ≤ b2 ∧
      a1 ≤ (1 - ε0) * y1.sum + J1.sum ∧ (1 - ε0) * y1.sum + J1.sum ≤ b1 :=
  sorry

/-- **Lemma 7.7 (four-factor extraction), log-size form.** Parts `I₁, …, I₄` with the
source's four capacities; `q ≍ x^{1/2 + 2ω₀}` enters as the lower bound
`1/2 + 2ω₀ ≤ log_x q`, the form its proof uses. Conclusion: disjoint selections giving
`u` (from `I₂, J₂`) and `r` (from `I₁, I₄, J₁`) in their windows, and for every
`c ∈ [a₁, b₁]` a sub-selection `J′` of `J₁` giving `d₁ | r` (from `I₁, J′`) with
`log_x d₁ ∈ [2c + a₃, 2c + b₃]`; taking `c = log_x r` gives `d₁ ∈ [r² x^{a₃}, r² x^{b₃}]`. -/
theorem lemma_7_7 (a1 a2 a3 b1 b2 b3 δ ω0 ε0 : Rat)
    (hc3 : 0 ≤ 3 * (b1 - a1) + (a3 - b3)) (h12 : a1 - a2 ≤ b1 - b2)
    (hw1 : δ ≤ b1 - a1) (hw2 : δ ≤ b2 - a2) (hw3 : δ ≤ b3 - a3) (hω0 : -ε0 ≤ ω0)
    (y1 y2 y3 y4 : List Rat)
    (hI1 : y1.sum ≤ 2 * a1 + b3) (hI2 : y2.sum ≤ b2)
    (hI3 : y3.sum ≤ 1 / 2 + 2 * ω0 - b1 - a2) (hI4 : y4.sum ≤ a1 - 2 * b1 - a3)
    (zs : List Rat) (hz : ∀ z ∈ zs, z < δ)
    (hq : 1 / 2 + 2 * ω0 ≤ y1.sum + y2.sum + y3.sum + y4.sum + zs.sum) :
    ∃ J2 J1 R : List Rat, zs.Perm (J2 ++ J1 ++ R) ∧
      a2 ≤ y2.sum + J2.sum ∧ y2.sum + J2.sum ≤ b2 ∧
      a1 ≤ y1.sum + y4.sum + J1.sum ∧ y1.sum + y4.sum + J1.sum ≤ b1 ∧
      ∀ c : Rat, a1 ≤ c → c ≤ b1 →
        ∃ J' R' : List Rat, J1.Perm (J' ++ R') ∧
          2 * c + a3 ≤ y1.sum + J'.sum ∧ y1.sum + J'.sum ≤ 2 * c + b3 :=
  sorry

/-- **Table 2 (§8.2).** With `θ = 1/2 − κ`, `εₜ = εₐ/100` and the unsimplified Type-IIc
intervals `a₁ … b₃` of §8.2, the four bin capacities `2a₁ + b₃`, `b₂`, `θ − b₁ − a₂`,
`a₁ − 2b₁ − a₃` equal the table's raw capacities; their differences from the endpoint
capacities are the table's last column; and all four differences are nonnegative for
`0 ≤ κ ≤ (11/80) εₐ`. -/
theorem table_2_transport (γ d κ εa : Rat) :
    (2 * (γ - 3 * (εa / 100) - d) + (2 - γ - 52 * (εa / 100) - 4 * (1 / 2 - κ))
        = γ - 2 * d + 4 * κ - 58 * (εa / 100)) ∧
    (1 - γ - 6 * (εa / 100) - (1 / 2 - κ) = 1 / 2 - γ + κ - 6 * (εa / 100)) ∧
    ((1 / 2 - κ) - (γ - 3 * (εa / 100)) - (1 - γ - 6 * (εa / 100) - (1 / 2 - κ) - d)
        = d - 2 * κ + 9 * (εa / 100)) ∧
    ((γ - 3 * (εa / 100) - d) - 2 * (γ - 3 * (εa / 100))
        - (2 - γ - 52 * (εa / 100) - d - 4 * (1 / 2 - κ)) = -4 * κ + 55 * (εa / 100)) ∧
    ((γ - 2 * d + 4 * κ - 58 * (εa / 100)) - (γ - 2 * d - εa) = 4 * κ + 42 * εa / 100) ∧
    ((1 / 2 - γ + κ - 6 * (εa / 100)) - (1 / 2 - γ - εa) = κ + 94 * εa / 100) ∧
    ((d - 2 * κ + 9 * (εa / 100)) - (d - εa) = 109 * εa / 100 - 2 * κ) ∧
    ((-4 * κ + 55 * (εa / 100)) - 0 = 55 * εa / 100 - 4 * κ) ∧
    (0 ≤ εa → 0 ≤ κ → κ ≤ 11 / 80 * εa →
      0 ≤ 4 * κ + 42 * εa / 100 ∧ 0 ≤ κ + 94 * εa / 100 ∧
      0 ≤ 109 * εa / 100 - 2 * κ ∧ 0 ≤ 55 * εa / 100 - 4 * κ) :=
  sorry

/-- **Lemma 8.2 (monotone endpoint transport).** Each bin is `(c, s, w)`: endpoint
capacity `c` at `θ = 1/2`, affine slope `s` (capacity `c + s (θ − 1/2)`), and partition
load `w`. If every slope satisfies `|s| ≤ L_leaf` and the endpoint partition has reserve
`η` in every bin (`w + η ≤ c`), then the partition stays valid for
`|θ − 1/2| < η / L_leaf`. -/
theorem lemma_8_2 (bins : List (Rat × Rat × Rat)) (Lleaf η θ : Rat) (hL : 0 < Lleaf)
    (hslope : ∀ b ∈ bins, -Lleaf ≤ b.2.1 ∧ b.2.1 ≤ Lleaf)
    (hres : ∀ b ∈ bins, b.2.2 + η ≤ b.1)
    (hθ1 : θ - 1 / 2 < η / Lleaf) (hθ2 : 1 / 2 - θ < η / Lleaf) :
    ∀ b ∈ bins, b.2.2 ≤ b.1 + b.2.1 * (θ - 1 / 2) :=
  sorry

/-- **Lemma 9.2 (moving marginal endpoint).** For `x̂ ∈ T̂` (total `S ≤ τ`, rough count
`s`, rough mass `ρ₁ ≤ C(s)`), the point `(x̂, u)` with `u ≥ 0` lies in the rescaled
support `T̃` (total `S + u ≤ L`; rough mass at most the cap of the new rough count, where
`u` is rough exactly when `u > g`) if and only if
`u ≤ U(x̂) = min{L − S, max{g, C(s + 1) − ρ₁}}`. -/
theorem lemma_9_2 (L τ g S ρ1 : Rat) (C : Nat → Rat) (s : Nat)
    (hS : S ≤ τ) (hρ : ρ1 ≤ C s) (u : Rat) (hu : 0 ≤ u) :
    (S + u ≤ L ∧ (if g < u then ρ1 + u ≤ C (s + 1) else ρ1 ≤ C s)) ↔
      u ≤ min (L - S) (max g (C (s + 1) - ρ1)) :=
  sorry

end BGP212.Challenge
