/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026), Table 3 (§9.1, p. 39) and the §9.3 dictionary (p. 40).
Specification of record: specs/A0_parameters.yaml.
-/


/-! # The parameter datum P (Table 3)

Every constant is transcribed from Table 3, the source's "single parameter point used
in both halves of the proof", as an exact rational in core Lean's `Rat`.
Physical normalization first, then the rescaled-by-4 column. -/



namespace BGP212.Params

/-- Table 3: number of shifts. -/
def k : Nat := 45
/-- Table 3: ω. -/
def ω : Rat := 7 / 1000
/-- Table 3: A₀. -/
def A0 : Rat := -1 / 125
/-- Table 3: A₁ (the single band, n = 1). -/
def A1 : Rat := 257 / 1000
/-- Table 3: εₛ. -/
def εs : Rat := 1 / 125
/-- Table 3: δ, the roughness threshold. -/
def δ : Rat := 41 / 2500
/-- Table 3: ξ₁, ξ₂, ξ₃. -/
def ξ1 : Rat := 19 / 50
def ξ2 : Rat := 2 / 5
def ξ3 : Rat := 2 / 5
/-- Table 3: εₐ = 10⁻¹⁰ (the ϵ of Proposition 7.8). -/
def εa : Rat := 1 / 10000000000

/-- Table 3: the cap numerators B₁,ₘ · 5000 for m = 1, …, 10. -/
def Bnum : List Nat := [777, 794, 875, 917, 953, 983, 1016, 1042, 1063, 1081]

/-- Table 3 with Definition 4.1's convention B₁,₀ = 0:
`B m` = B₁,ₘ for `1 ≤ m ≤ 10`, and 1081/5000 for `m ≥ 11`. -/
def B (m : Nat) : Rat :=
  if m = 0 then 0
  else if m ≤ 10 then ((Bnum[m - 1]! : Nat) : Rat) / 5000
  else 1081 / 5000

/-- Table 3, rescaled column: g = 4δ. -/
def g : Rat := 41 / 625
/-- Table 3, rescaled column: C(m) = 4·B₁,ₘ. -/
def C (m : Nat) : Rat := 4 * B m
/-- §9.3 dictionary: L (rescaled A₁ + εₛ). -/
def L : Rat := 53 / 50
/-- §9.3 dictionary: τ (rescaled A₁ − εₛ). -/
def τ : Rat := 249 / 250

end BGP212.Params
