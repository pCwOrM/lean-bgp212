/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Lemma 4.2 (p. 4), §7.2 and Lemmas 7.5–7.7 (pp. 28–31),
§8.2, Table 2 and Lemma 8.2 (p. 38), Lemma 9.2 (p. 41).
-/

/-! # A2: the combinatorial layer — proofs

Core Lean only. Linear arithmetic over `Rat` is closed by `grind`; each product of two
variables enters as an explicit fact from `Rat.mul_nonneg` or
`Rat.mul_le_mul_of_nonneg_left`. Every extraction lemma reuses `smooth_insertion`, the
source's own mechanism, once per target interval. -/

namespace BGP212.Challenge

/-! ## Helpers -/

theorem perm_sum {l1 l2 : List Rat} (h : l1.Perm l2) : l1.sum = l2.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap x y l => simp [List.sum_cons]; grind
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem sum_nonneg_of_ge {δ : Rat} (hδ : 0 < δ) :
    ∀ ys : List Rat, (∀ y ∈ ys, δ ≤ y) → 0 ≤ ys.sum
  | [], _ => by simp
  | y :: ys, h => by
      have h1 := h y (by simp)
      have h2 := sum_nonneg_of_ge hδ ys (fun z hz => h z (by simp [hz]))
      simp [List.sum_cons]; grind

/-- Removing `k` coordinates, each above `δ`, lowers the sum by at least `k δ`. -/
theorem sublist_sum_gap {δ : Rat} {zs ys : List Rat} (h : zs.Sublist ys)
    (hr : ∀ y ∈ ys, δ < y) :
    zs.sum + δ * ((ys.length - zs.length : Nat) : Rat) ≤ ys.sum := by
  induction h with
  | slnil => simp; grind
  | @cons l1 l2 a hs ih =>
      have hle := hs.length_le
      have ha := hr a (by simp)
      have ih' := ih (fun y hy => hr y (by simp [hy]))
      have hk : (l2.length + 1 - l1.length : Nat) = (l2.length - l1.length) + 1 := by omega
      simp only [List.length_cons, List.sum_cons, hk]
      have hc : (((l2.length - l1.length) + 1 : Nat) : Rat)
          = ((l2.length - l1.length : Nat) : Rat) + 1 := by grind
      rw [hc]
      grind
  | @cons_cons l1 l2 a hs ih =>
      have ih' := ih (fun y hy => hr y (by simp [hy]))
      have hk : (l2.length + 1 - (l1.length + 1) : Nat) = l2.length - l1.length := by omega
      simp only [List.length_cons, List.sum_cons, hk]
      grind

/-- Iterating `B (q + 1) ≤ B q + δ`. -/
theorem cap_iterate {δ : Rat} {B : Nat → Rat} (hB : ∀ q : Nat, B (q + 1) ≤ B q + δ) (r : Nat) :
    ∀ k : Nat, B (r + k) ≤ B r + δ * (k : Rat)
  | 0 => by simp; grind
  | k + 1 => by
      have ih := cap_iterate hB r k
      have h1 := hB (r + k)
      have hc : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
      rw [show r + (k + 1) = r + k + 1 by omega, hc]
      grind

/-! ## Lemma 4.2 -/

theorem lemma_4_2 (δ : Rat) (B : Nat → Rat) (hB : ∀ q : Nat, B (q + 1) ≤ B q + δ)
    (ys : List Rat) (hrough : ∀ y ∈ ys, δ < y) (hcap : ys.sum ≤ B ys.length)
    (zs : List Rat) (hsub : zs.Sublist ys) :
    zs.sum ≤ B zs.length := by
  have hgap := sublist_sum_gap hsub hrough
  have hle := hsub.length_le
  have hit := cap_iterate hB zs.length (ys.length - zs.length)
  rw [show zs.length + (ys.length - zs.length) = ys.length by omega] at hit
  grind

/-! ## §7.2 smooth insertion -/

theorem smooth_insertion (a b δ : Rat) (hw : δ ≤ b - a) (zs : List Rat)
    (hz : ∀ z ∈ zs, z < δ) (s : Rat) (hs : s ≤ b) (hreach : a ≤ s + zs.sum) :
    ∃ J R : List Rat, zs.Perm (J ++ R) ∧ a ≤ s + J.sum ∧ s + J.sum ≤ b := by
  induction zs generalizing s with
  | nil => exact ⟨[], [], List.Perm.refl _, by simp at hreach ⊢; grind, by simp; grind⟩
  | cons z zs ih =>
      by_cases h : a ≤ s
      · exact ⟨[], z :: zs, List.Perm.refl _, by simp; grind, by simp; grind⟩
      · have hzδ := hz z (by simp)
        have hreach' : a ≤ (s + z) + zs.sum := by simp [List.sum_cons] at hreach; grind
        obtain ⟨J, R, hp, h1, h2⟩ :=
          ih (fun x hx => hz x (by simp [hx])) (s + z) (by grind) hreach'
        refine ⟨z :: J, R, ?_, ?_, ?_⟩
        · exact hp.cons z
        · simp [List.sum_cons]; grind
        · simp [List.sum_cons]; grind

/-! ## Lemma 7.5 -/

theorem lemma_7_5 (a b δ ε0 ϵ : Rat)
    (_ha : 0 < a) (_hb : b < 1 / 2) (hδ0 : 0 < δ) (hδ : δ ≤ b - a)
    (hε0 : 0 < ε0) (hε1 : ε0 < 1) (_hϵ0 : 0 ≤ ϵ) (hϵ : ϵ ≤ ε0 * (1 / 2 - a))
    (y1 y2 : List Rat) (hy : ∀ y ∈ y1 ++ y2, δ ≤ y)
    (hI1 : y1.sum ≤ b) (hI2 : y2.sum ≤ 1 / 2 - a)
    (zs : List Rat) (hz : ∀ z ∈ zs, z < δ)
    (hq : 1 / 2 - ϵ < (1 - ε0) * (y1.sum + y2.sum) + zs.sum) :
    ∃ J R : List Rat, zs.Perm (J ++ R) ∧
      a ≤ (1 - ε0) * y1.sum + J.sum ∧ (1 - ε0) * y1.sum + J.sum ≤ b := by
  have hY1 := sum_nonneg_of_ge hδ0 y1 (fun y h => hy y (by simp [h]))
  -- (1 − ε₀) Y₁ ≤ Y₁ and (1 − ε₀) Y₂ ≤ (1 − ε₀)(1/2 − a)
  have p1 : 0 ≤ ε0 * y1.sum := Rat.mul_nonneg (by grind) hY1
  have p2 : (1 - ε0) * y2.sum ≤ (1 - ε0) * (1 / 2 - a) :=
    Rat.mul_le_mul_of_nonneg_left hI2 (by grind)
  have e1 : (1 - ε0) * y1.sum = y1.sum - ε0 * y1.sum := by grind
  have e2 : (1 - ε0) * (y1.sum + y2.sum) = (1 - ε0) * y1.sum + (1 - ε0) * y2.sum := by grind
  have e3 : (1 - ε0) * (1 / 2 - a) = (1 / 2 - a) - ε0 * (1 / 2 - a) := by grind
  exact smooth_insertion a b δ hδ zs hz ((1 - ε0) * y1.sum) (by grind) (by grind)

/-! ## Lemma 7.6 -/

theorem lemma_7_6 (a1 a2 b1 b2 δ ε0 ϵ : Rat)
    (_ha1 : 0 < a1) (_ha2 : 0 < a2) (_hb1 : b1 < 1 / 2) (_hb2 : b2 < 1 / 2) (hδ0 : 0 < δ)
    (h12 : a1 - a2 ≤ b1 - b2) (_hsum : b1 + b2 < 1 / 2)
    (hw1 : δ ≤ b1 - a1) (hw2 : δ ≤ b2 - a2)
    (hε0 : 0 < ε0) (hε1 : ε0 < 1) (_hϵ0 : 0 ≤ ϵ) (hϵ : ϵ ≤ ε0 * (1 / 2 - b1 - a2))
    (y1 y2 y3 : List Rat) (hy : ∀ y ∈ y1 ++ y2 ++ y3, δ ≤ y)
    (hI1 : y1.sum ≤ b1) (hI2 : y2.sum ≤ b2) (hI3 : y3.sum ≤ 1 / 2 - b1 - a2)
    (zs : List Rat) (hz : ∀ z ∈ zs, z < δ)
    (hq : 1 / 2 - ϵ < (1 - ε0) * (y1.sum + y2.sum + y3.sum) + zs.sum) :
    ∃ J2 J1 R : List Rat, zs.Perm (J2 ++ J1 ++ R) ∧
      a2 ≤ (1 - ε0) * y2.sum + J2.sum ∧ (1 - ε0) * y2.sum + J2.sum ≤ b2 ∧
      a1 ≤ (1 - ε0) * y1.sum + J1.sum ∧ (1 - ε0) * y1.sum + J1.sum ≤ b1 := by
  have hY1 := sum_nonneg_of_ge hδ0 y1 (fun y h => hy y (by simp [h]))
  have hY2 := sum_nonneg_of_ge hδ0 y2 (fun y h => hy y (by simp [h]))
  have p1 : 0 ≤ ε0 * y1.sum := Rat.mul_nonneg (by grind) hY1
  have p2 : 0 ≤ ε0 * y2.sum := Rat.mul_nonneg (by grind) hY2
  have p3 : (1 - ε0) * y3.sum ≤ (1 - ε0) * (1 / 2 - b1 - a2) :=
    Rat.mul_le_mul_of_nonneg_left hI3 (by grind)
  have e1 : (1 - ε0) * y1.sum = y1.sum - ε0 * y1.sum := by grind
  have e2 : (1 - ε0) * y2.sum = y2.sum - ε0 * y2.sum := by grind
  have e3 : (1 - ε0) * (y1.sum + y2.sum + y3.sum)
      = (1 - ε0) * y1.sum + (1 - ε0) * y2.sum + (1 - ε0) * y3.sum := by grind
  have e4 : (1 - ε0) * (1 / 2 - b1 - a2) = (1 / 2 - b1 - a2) - ε0 * (1 / 2 - b1 - a2) := by
    grind
  -- first insertion: the divisor u
  obtain ⟨J2, R2, hp2, hu1, hu2⟩ :=
    smooth_insertion a2 b2 δ hw2 zs hz ((1 - ε0) * y2.sum) (by grind) (by grind)
  have hs2 : zs.sum = J2.sum + R2.sum := by rw [perm_sum hp2, List.sum_append]
  -- second insertion, from the remaining smooth primes: the divisor r
  have hzR : ∀ z ∈ R2, z < δ := fun z hz' => hz z (hp2.symm.subset (by simp [hz']))
  obtain ⟨J1, R, hp1, hr1, hr2⟩ :=
    smooth_insertion a1 b1 δ hw1 R2 hzR ((1 - ε0) * y1.sum) (by grind) (by grind)
  refine ⟨J2, J1, R, ?_, hu1, hu2, hr1, hr2⟩
  rw [List.append_assoc]
  exact hp2.trans (List.Perm.append_left J2 hp1)

/-! ## Lemma 7.7 -/

theorem lemma_7_7 (a1 a2 a3 b1 b2 b3 δ ω0 ε0 : Rat)
    (hc3 : 0 ≤ 3 * (b1 - a1) + (a3 - b3)) (h12 : a1 - a2 ≤ b1 - b2)
    (hw1 : δ ≤ b1 - a1) (hw2 : δ ≤ b2 - a2) (hw3 : δ ≤ b3 - a3) (_hω0 : -ε0 ≤ ω0)
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
          2 * c + a3 ≤ y1.sum + J'.sum ∧ y1.sum + J'.sum ≤ 2 * c + b3 := by
  -- the divisor u
  obtain ⟨J2, R2, hp2, hu1, hu2⟩ :=
    smooth_insertion a2 b2 δ hw2 zs hz y2.sum hI2 (by grind)
  have hs2 : zs.sum = J2.sum + R2.sum := by rw [perm_sum hp2, List.sum_append]
  have hzR : ∀ z ∈ R2, z < δ := fun z hz' => hz z (hp2.symm.subset (by simp [hz']))
  -- the divisor r
  obtain ⟨J1, R, hp1, hr1, hr2⟩ :=
    smooth_insertion a1 b1 δ hw1 R2 hzR (y1.sum + y4.sum) (by grind) (by grind)
  have hzJ1 : ∀ z ∈ J1, z < δ := fun z hz' => hzR z (hp1.symm.subset (by simp [hz']))
  refine ⟨J2, J1, R, ?_, hu1, hu2, hr1, hr2, ?_⟩
  · rw [List.append_assoc]
    exact hp2.trans (List.Perm.append_left J2 hp1)
  · -- the divisor d₁ of r, for every c ∈ [a₁, b₁]
    intro c hc1 hc2
    exact smooth_insertion (2 * c + a3) (2 * c + b3) δ (by grind) J1 hzJ1 y1.sum
      (by grind) (by grind)

/-! ## Table 2 and Lemma 8.2 -/

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
      0 ≤ 109 * εa / 100 - 2 * κ ∧ 0 ≤ 55 * εa / 100 - 4 * κ) := by
  refine ⟨by grind, by grind, by grind, by grind, by grind, by grind, by grind, by grind, ?_⟩
  intro h1 h2 h3
  exact ⟨by grind, by grind, by grind, by grind⟩

theorem lemma_8_2 (bins : List (Rat × Rat × Rat)) (Lleaf η θ : Rat) (hL : 0 < Lleaf)
    (hslope : ∀ b ∈ bins, -Lleaf ≤ b.2.1 ∧ b.2.1 ≤ Lleaf)
    (hres : ∀ b ∈ bins, b.2.2 + η ≤ b.1)
    (hθ1 : θ - 1 / 2 < η / Lleaf) (hθ2 : 1 / 2 - θ < η / Lleaf) :
    ∀ b ∈ bins, b.2.2 ≤ b.1 + b.2.1 * (θ - 1 / 2) := by
  intro b hb
  obtain ⟨hs1, hs2⟩ := hslope b hb
  have hr := hres b hb
  -- `Lleaf · |θ − 1/2| < η`, from the two one-sided bounds
  have hLne : Lleaf ≠ 0 := by grind
  have k1 : Lleaf * (θ - 1 / 2) < Lleaf * (η / Lleaf) := by
    have := Rat.mul_lt_mul_of_pos_left hθ1 hL
    exact this
  have k2 : Lleaf * (1 / 2 - θ) < Lleaf * (η / Lleaf) := by
    have := Rat.mul_lt_mul_of_pos_left hθ2 hL
    exact this
  have hcancel : Lleaf * (η / Lleaf) = η := by
    rw [Rat.mul_comm, Rat.div_mul_cancel hLne]
  -- slope · offset ≥ −Lleaf · |offset|, by the sign of the offset
  by_cases hu : 0 ≤ θ - 1 / 2
  · have m : 0 ≤ (b.2.1 + Lleaf) * (θ - 1 / 2) := Rat.mul_nonneg (by grind) hu
    have e : (b.2.1 + Lleaf) * (θ - 1 / 2) = b.2.1 * (θ - 1 / 2) + Lleaf * (θ - 1 / 2) := by
      grind
    grind
  · have m : 0 ≤ (Lleaf - b.2.1) * (1 / 2 - θ) := Rat.mul_nonneg (by grind) (by grind)
    have e : (Lleaf - b.2.1) * (1 / 2 - θ) = Lleaf * (1 / 2 - θ) + b.2.1 * (θ - 1 / 2) := by
      grind
    grind

/-! ## Lemma 9.2 -/

theorem lemma_9_2 (L τ g S ρ1 : Rat) (C : Nat → Rat) (s : Nat)
    (_hS : S ≤ τ) (hρ : ρ1 ≤ C s) (u : Rat) (_hu : 0 ≤ u) :
    (S + u ≤ L ∧ (if g < u then ρ1 + u ≤ C (s + 1) else ρ1 ≤ C s)) ↔
      u ≤ min (L - S) (max g (C (s + 1) - ρ1)) := by
  by_cases h : g < u
  · simp only [h, if_true]; grind
  · simp only [h, if_false]; grind

end BGP212.Challenge
