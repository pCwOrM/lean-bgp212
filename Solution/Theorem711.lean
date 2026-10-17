/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Proposition 7.8 and its proof (pp. 31–36), Lemma 7.10 and
Theorem 7.11 (p. 36).
-/
import BGP212.Theorem711
import Solution.PackingC
import Solution.A2Combinatorial
import Solution.AppendixB

/-! # A4: from Lemma 7.10 to Theorem 7.11 (proofs)

* `conds_table3`: the case split. Every tuple of `Ξ(B₁,ₘ, B₁,ₘ′, m, m′, δ)`, for all
  `m, m′ ≥ 0`, satisfies (A)–(E): `m, m′ ≤ 13` is forced by the caps; `m ≤ m′` is a root of
  Lemma 7.10; `m > m′` is the root `(m′, m)` with the sides exchanged; a side with no
  coordinates is the root `(1, ·)` with a part of size `δ` adjoined and then deleted (the
  argument in the proof of Lemma 7.10); the empty tuple packs because every capacity is
  nonnegative.
* Parameter bounds: Definition 4.1 and (I)–(III) at Table 3; the permissible triples of
  Lemmas 5.3–5.7 at the proof's `δ*(γ)`, with margin `εₐ`, over each full `γ`-range.
* Containments `Q ⊆ D_X`: (A)–(E) composed with Lemmas 7.5–7.7 (A2). -/

namespace BGP212.T711

open BGP212.Params BGP212.Packing BGP212.Challenge

/-! ## Packing helpers -/

theorem packs_nil (caps : List Rat) (h : ∀ k, k < caps.length → 0 ≤ caps[k]!) :
    Packs caps [] :=
  ⟨[], rfl, by simp, fun k hk => by
    show binSum [] [] k ≤ caps[k]!
    simp only [binSum, List.zip_nil_left, List.filter_nil, List.map_nil, List.sum_nil]
    exact h k hk⟩

theorem packs_of_cons {caps : List Rat} {x : Rat} {l : List Rat} (hx : 0 ≤ x)
    (h : Packs caps (x :: l)) : Packs caps l := by
  obtain ⟨as, hlen, hin, hb⟩ := h
  match as, hlen, hin, hb with
  | a :: as', hlen', hin', hb' =>
    refine ⟨as', by simpa using hlen', fun b hb'' => hin' b (by simp [hb'']), fun k hk => ?_⟩
    have := hb' k hk
    rw [binSum_cons] at this
    by_cases hak : a = k <;> simp [hak] at this <;> grind

theorem B_le (m : Nat) : B m ≤ 1081 / 5000 := by
  by_cases h : m < 11
  · have key : ∀ m, m < 11 → B m ≤ 1081 / 5000 := by decide +kernel
    exact key m h
  · simp only [B]
    have h0 : m ≠ 0 := by omega
    have h10 : ¬ m ≤ 10 := by omega
    simp [h0, h10]

theorem B_pos (m : Nat) (hm : 1 ≤ m) : δ ≤ B m := by
  by_cases h : m < 11
  · have key : ∀ m, m < 11 → 1 ≤ m → δ ≤ B m := by decide +kernel
    exact key m h hm
  · simp only [B]
    have h0 : m ≠ 0 := by omega
    have h10 : ¬ m ≤ 10 := by omega
    simp [h0, h10, δ]
    decide +kernel

/-- A side with at least 14 coordinates, each at least `δ`, exceeds every cap. -/
theorem side_le_13 (l : List Rat) (hδ : ∀ y ∈ l, δ ≤ y) (m : Nat) (hsum : l.sum ≤ B m) :
    l.length ≤ 13 := by
  have h1 := sum_ge_length_mul δ l hδ
  have h2 := B_le m
  rcases Nat.lt_or_ge l.length 14 with hc | hc
  · omega
  exfalso
  have h3 : (14 : Rat) ≤ (l.length : Rat) := by exact_mod_cast hc
  have h4 : (14 : Rat) * δ ≤ (l.length : Rat) * δ :=
    Rat.mul_le_mul_of_nonneg_right h3 (by simp [δ]; decide +kernel)
  simp [δ] at h1 h4
  grind

/-- **The case split.** A capacity list that every root of Lemma 7.10 packs, and whose
capacities are nonnegative, packs every tuple of `Ξ(B₁,ₘ, B₁,ₘ′, m, m′, δ)` for all `m, m′`. -/
theorem packs_xi (caps : List Rat) (hcap : ∀ k, k < caps.length → 0 ≤ caps[k]!)
    (hroot : ∀ m m', 1 ≤ m → m ≤ m' → m' ≤ 13 → ∀ s1 s2,
      InXi (B m) (B m') m m' s1 s2 → Packs caps (s1 ++ s2)) :
    ∀ m m' ys, Xi (B m) (B m') m m' δ ys → Packs caps ys := by
  intro m m' ys hX
  obtain ⟨hlen, hr, h1, h2⟩ := hX
  have hl1 : (ys.take m).length = m := by simp [hlen]
  have hl2 : (ys.drop m).length = m' := by simp [hlen]
  have hr1 : ∀ y ∈ ys.take m, δ ≤ y ∧ y ≤ 1 := fun y hy => hr y (List.mem_of_mem_take hy)
  have hr2 : ∀ y ∈ ys.drop m, δ ≤ y ∧ y ≤ 1 := fun y hy => hr y (List.mem_of_mem_drop hy)
  have hm : m ≤ 13 := hl1 ▸ side_le_13 _ (fun y hy => (hr1 y hy).1) m h1
  have hm' : m' ≤ 13 := hl2 ▸ side_le_13 _ (fun y hy => (hr2 y hy).1) m' h2
  have hδ1 : δ ≤ 1 := by simp [δ]; decide +kernel
  have hδ0 : 0 ≤ δ := by simp [δ]; decide +kernel
  have hsplit : ys = ys.take m ++ ys.drop m := (List.take_append_drop m ys).symm
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rcases Nat.eq_zero_or_pos m' with rfl | hm'pos
    · have : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; exact packs_nil caps hcap
    · -- one side empty: adjoin a part of size δ, use the root (1, m'), delete it
      have hX' : InXi (B 1) (B m') 1 m' [δ] ys := by
        refine ⟨rfl, by simpa using hl2, ?_, by have := B_pos 1 (Nat.le_refl 1); simp only [List.sum_cons, List.sum_nil]; grind, by simpa using h2⟩
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · simp at h; subst h; exact ⟨Rat.le_refl, hδ1⟩
        · exact hr y h
      exact packs_of_cons hδ0 (hroot 1 m' (Nat.le_refl 1) hm'pos hm' [δ] ys hX')
  · rcases Nat.eq_zero_or_pos m' with rfl | hm'pos
    · have hys : ys.take m = ys := List.take_of_length_le (by omega)
      have hX' : InXi (B 1) (B m) 1 m [δ] (ys.take m) := by
        refine ⟨rfl, hl1, ?_, by have := B_pos 1 (Nat.le_refl 1); simp only [List.sum_cons, List.sum_nil]; grind, h1⟩
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · simp at h; subst h; exact ⟨Rat.le_refl, hδ1⟩
        · exact hr1 y h
      have := packs_of_cons hδ0 (hroot 1 m (Nat.le_refl 1) hmpos hm [δ] _ hX')
      rwa [hys] at this
    · by_cases hle : m ≤ m'
      · have hX' : InXi (B m) (B m') m m' (ys.take m) (ys.drop m) :=
          ⟨hl1, hl2, fun y hy => by rw [← hsplit] at hy; exact hr y hy, h1, h2⟩
        rw [hsplit]; exact hroot m m' hmpos hle hm' _ _ hX'
      · have hX' : InXi (B m') (B m) m' m (ys.drop m) (ys.take m) :=
          ⟨hl2, hl1, fun y hy => hr y (by
            rcases List.mem_append.mp hy with h | h
            · exact List.mem_of_mem_drop h
            · exact List.mem_of_mem_take h), h2, h1⟩
        have := hroot m' m hm'pos (by omega) hm _ _ hX'
        rw [hsplit]
        exact packs_perm List.perm_append_comm this

theorem omega_table3 : omegaJJ A3 1 1 = ω11 ∧ ω11 = ω := by
  refine ⟨by simp [omegaJJ, A3, ω11], by simp [ω11, A1, ω]; decide +kernel⟩

/-- Lemma 7.10 as a hypothesis on a capacity list, per condition. -/
theorem root_packs (c : Cond) (P : List Rat → List Rat → Prop)
    (hP : ∀ m m', Root c m m' → ∀ s1 s2, InXi (B m) (B m') m m' s1 s2 → P s1 s2) :
    ∀ m m', 1 ≤ m → m ≤ m' → m' ≤ 13 → ∀ s1 s2, InXi (B m) (B m') m m' s1 s2 → P s1 s2 :=
  fun m m' h1 h2 h3 => hP m m' (lemma_7_10 c m m' h1 h2 h3)

/-- **The case split, Table 3.** Every tuple of `Ξ(B₁,ₘ, B₁,ₘ′, m, m′, δ)`, for all
`m, m′ ≥ 0`, satisfies conditions (A)–(E) of Proposition 7.8 at `ω = ω(1,1)`. -/
theorem conds_table3 :
    ∀ m m' ys, Xi (B m) (B m') m m' δ ys → CondsAE ξ1 ξ2 ξ3 ω11 δ εa ys := by
  intro m m' ys hX
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact packs_xi capsA1 (by decide +kernel)
      (root_packs .A _ fun m m' h s1 s2 hx => (h s1 s2 hx).1) m m' ys hX
  · exact packs_xi capsA2 (by decide +kernel)
      (root_packs .A _ fun m m' h s1 s2 hx => (h s1 s2 hx).2) m m' ys hX
  · exact packs_xi capsB (by decide +kernel)
      (root_packs .B _ fun m m' h s1 s2 hx => h s1 s2 hx) m m' ys hX
  · exact packs_xi capsC (by decide +kernel)
      (root_packs .C _ fun m m' h s1 s2 hx => h s1 s2 hx) m m' ys hX
  · intro ω0 γ h1 h2 h3 h4
    have h3' : 2 / 5 - εa ≤ γ := by simpa [ξ2] using h3
    have h4' : γ ≤ 1 / 3 + 8 * ω11 + 7 * δ / 3 + 3 * εa := by grind
    have hc : ∀ k, k < (capsD γ ω0).length → 0 ≤ (capsD γ ω0)[k]! := by
      intro k hk
      simp only [capsD, List.length_cons, List.length_nil] at hk
      simp only [ω11, A1, δ, εa] at h2 h3' h4'
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
        simp [capsD, δ, εa] <;> grind
    exact packs_xi (capsD γ ω0) hc
      (root_packs .D _ fun m m' h s1 s2 hx => h s1 s2 hx γ ω0 h1 h2 h3' h4') m m' ys hX
  · exact packs_xi capsE (by decide +kernel)
      (root_packs .E _ fun m m' h s1 s2 hx => h s1 s2 hx) m m' ys hX

/-- **Proposition 7.8's packing hypotheses hold at Table 3**, quantified as printed. -/
theorem prop_7_8_packing_table3 : Prop78Packing 1 A3 B3 δ ξ1 ξ2 ξ3 εa := by
  intro j j' hj hj1 hj' hj'1 m m' _ _ _ ys hX
  have e1 : j = 1 := by omega
  have e2 : j' = 1 := by omega
  subst e1 e2
  rw [omega_table3.1]
  exact conds_table3 m m' ys hX

/-! ## Parameter bounds -/

theorem floorInv_table3 : floorInv δ = 60 := by decide +kernel

/-- **Definition 4.1 at Table 3** (`n = 1`, `ε = εₛ`). -/
theorem support_datum_table3 : SupportDatum 1 A3 B3 δ εs ∧ floorInv δ = 60 := by
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel, ?_⟩,
    floorInv_table3⟩
  · intro j hj
    have : j = 0 := by omega
    subst this; decide +kernel
  · intro j _ _
    refine ⟨rfl, fun m hm _ => (definition_4_1_caps m hm).1,
      fun m hm _ => ⟨(definition_4_1_caps m hm).2.1, (definition_4_1_caps m hm).2.2⟩⟩

/-- **Proposition 7.8 (I)–(III) at Table 3.** -/
theorem prop_7_8_scalar_table3 : Prop78Scalar 1 A3 δ ξ1 ξ2 ξ3 εa := by
  unfold Prop78Scalar; decide +kernel

/-- The Type II range `[ξ₂ − ϵ, 1/2]` is covered by the IIc, IIb and IIa ranges, in order. -/
theorem type_II_cover :
    ξ2 - εa < gIIc ω11 δ εa ∧ gIIc ω11 δ εa < gIIa ω11 δ εa ∧ gIIa ω11 δ εa < 1 / 2 ∧
    ∀ γ, ξ2 - εa ≤ γ → γ ≤ 1 / 2 →
      γ ≤ gIIc ω11 δ εa ∨ (gIIc ω11 δ εa < γ ∧ γ < gIIa ω11 δ εa) ∨ gIIa ω11 δ εa ≤ γ := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun γ _ _ => ?_⟩
  by_cases h1 : γ ≤ gIIc ω11 δ εa
  · exact Or.inl h1
  · by_cases h2 : γ < gIIa ω11 δ εa
    · exact Or.inr (Or.inl ⟨by grind, h2⟩)
    · exact Or.inr (Or.inr (by grind))

theorem perm_I_low (γ ε : Rat) (h1 : ξ1 - εa ≤ γ) (h2 : γ ≤ 1 / 2) :
    PermI εa ω11 γ (dIlow ω11 γ εa) ε ∧ δ ≤ dIlow ω11 γ εa := by
  simp only [PermI, dIlow, ω11, A1, ξ1, εa, δ] at *
  exact ⟨⟨fun _ => by grind, fun h => absurd h (by grind)⟩, by grind⟩

theorem perm_I_high (γ ε : Rat) (h1 : 1 / 2 < γ) (_h2 : γ ≤ 1 / 2 + 2 * ω11 + ε) :
    PermI εa ω11 γ (dIhigh ω11 εa) ε ∧ δ ≤ dIhigh ω11 εa := by
  simp only [PermI, dIhigh, ω11, A1, εa, δ] at *
  exact ⟨⟨fun h => absurd h (by grind), fun _ _ => by grind⟩, by grind⟩

theorem perm_IIa (γ : Rat) (h1 : gIIa ω11 δ εa ≤ γ) (h2 : γ ≤ 1 / 2) :
    PermIIa εa ω11 γ (dIIa ω11 γ εa) ∧ δ ≤ dIIa ω11 γ εa := by
  simp only [PermIIa, dIIa, gIIa, ω11, A1, εa, δ] at *
  exact ⟨⟨by grind, by grind⟩, by grind⟩

theorem perm_IIb (γ : Rat) (h1 : gIIc ω11 δ εa < γ) (h2 : γ < gIIa ω11 δ εa) :
    PermIIb εa ω11 γ (dIIb ω11 γ εa) ∧ δ ≤ dIIb ω11 γ εa := by
  simp only [PermIIb, dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *
  exact ⟨⟨by grind, by grind⟩, by grind⟩

/-- Type IIc with `δ*(γ) = δ`: the printed admissible interval
`δ ≤ δ*(γ) ≤ min{1/4 − 2ω − γ/2, γ/10 − 32ω/10, γ/4 − 1/16 − 3ω − ϵ}` contains `δ` over the
whole range, and `(ω, γ, δ)` is permissible with margin `εₐ`. -/
theorem perm_IIc (γ : Rat) (h1 : ξ2 - εa ≤ γ) (h2 : γ ≤ gIIc ω11 δ εa) :
    PermIIc εa ω11 γ δ ∧
    δ ≤ 1 / 4 - 2 * ω11 - γ / 2 ∧ δ ≤ γ / 10 - 32 * ω11 / 10 ∧
    δ ≤ γ / 4 - 1 / 16 - 3 * ω11 - εa := by
  simp only [PermIIc, gIIc, ω11, A1, ξ2, εa, δ] at *
  exact ⟨⟨by grind, by grind, by grind⟩, by grind, by grind, by grind⟩

/-- Type III at Lemma 5.7's `γ = ξ₃ + ϵ` (the least `γ` covering Definition 7.1 (III)'s
`N_i ≤ x^{ξ₃+ϵ}`), with A4's width `dIII`. -/
theorem perm_III : PermIII εa ω11 (ξ3 + εa) (dIII ω11 ξ3 εa) ∧ δ < dIII ω11 ξ3 εa := by
  unfold PermIII; decide +kernel

/-- **Finding (Type III width).** With the printed `δ* = 1/2 − 7ω/2 − 9ξ₃/8 − ϵ`, the
triple is permissible at `γ = ξ₃` and fails at `γ = ξ₃ + ϵ`: `28ω + 9(ξ₃ + ϵ) + 8δ* = 4 + ϵ`.
A4's `dIII` (`− 11ϵ/8`) is permissible there, and (III), (E) still suffice for it. -/
theorem type_III_printed_gap :
    PermIII 0 ω11 ξ3 (dIIIprinted ω11 ξ3 εa) ∧
    ¬ PermIII 0 ω11 (ξ3 + εa) (dIIIprinted ω11 ξ3 εa) ∧
    28 * ω11 + 9 * (ξ3 + εa) + 8 * dIIIprinted ω11 ξ3 εa = 4 + εa := by
  unfold PermIII; decide +kernel

/-- **Finding (Type I, `γ > 1/2`).** The proof allows "any `δ*(γ) ∈ [δ, 1/14 − 68ω/14 − ϵ]`";
the partition (7.6) yields Lemma 7.5's hypothesis only for `δ*` near the top. At
`γ = 1/2 + 1/1000`, `ε′ = ϵ/3`, the choice `δ* = δ` leaves the second part's bound
`1/2 − a = γ − 1/2 + δ* + 3ε′` below (7.6)'s capacity `1/14 − 68ω/14 − 2ϵ`. -/
theorem type_I_high_choice :
    (1 / 2 + 1 / 1000) - 1 / 2 + δ + 3 * (εa / 3) < 1 / 14 - 68 / 14 * ω11 - 2 * εa ∧
    1 / 14 - 68 / 14 * ω11 - 2 * εa ≤ (1 / 2 + 1 / 1000) - 1 / 2 + dIhigh ω11 εa + 3 * (εa / 3) := by
  decide +kernel

/-! ## From an assignment to the parts `I₁ ∪ ⋯ ∪ I_K` -/

/-- Part `k` of an assignment: the items sent to bin `k`. -/
def part (items : List Rat) (as : List Nat) (k : Nat) : List Rat :=
  ((items.zip as).filter (fun p => p.2 == k)).map (·.1)

theorem binSum_eq_part (items : List Rat) (as : List Nat) (k : Nat) :
    binSum items as k = (part items as k).sum := rfl

theorem part_cons (x : Rat) (xs : List Rat) (a : Nat) (as : List Nat) (k : Nat) :
    part (x :: xs) (a :: as) k = if a = k then x :: part xs as k else part xs as k := by
  unfold part
  by_cases h : a = k
  · subst h; simp
  · simp [h]

theorem flatMap_congr' {f g : Nat → List Rat} :
    ∀ L : List Nat, (∀ k ∈ L, f k = g k) → L.flatMap f = L.flatMap g
  | [], _ => rfl
  | b :: L, h => by
      simp only [List.flatMap_cons]
      rw [h b (by simp), flatMap_congr' L (fun k hk => h k (by simp [hk]))]

theorem flatMap_insert (x : Rat) (P : Nat → List Rat) (a : Nat) :
    ∀ L : List Nat, a ∈ L → L.Nodup →
      (L.flatMap fun k => if a = k then x :: P k else P k).Perm (x :: L.flatMap P)
  | [], h, _ => by simp at h
  | b :: L, h, hnd => by
      have hnd' := List.nodup_cons.mp hnd
      simp only [List.flatMap_cons]
      by_cases hab : a = b
      · subst hab
        have hrest : (L.flatMap fun k => if a = k then x :: P k else P k) = L.flatMap P := by
          apply flatMap_congr' L
          intro k hk
          have : a ≠ k := fun e => hnd'.1 (e ▸ hk)
          simp [this]
        simp [hrest]
      · have hb : a ∈ L := by
          rcases List.mem_cons.mp h with h1 | h1
          · exact absurd h1 hab
          · exact h1
        have ih := flatMap_insert x P a L hb hnd'.2
        simp only [hab, ite_false]
        exact (ih.append_left (P b)).trans List.perm_middle

theorem perm_parts (K : Nat) : ∀ (items : List Rat) (as : List Nat), as.length = items.length →
    (∀ a ∈ as, a < K) → items.Perm ((List.range K).flatMap (part items as))
  | [], [], _, _ => by simp [part]
  | x :: xs, a :: as, hl, hin => by
      have ih := perm_parts K xs as (by simpa using hl) (fun b hb => hin b (by simp [hb]))
      have ha : a ∈ List.range K := List.mem_range.mpr (hin a (by simp))
      have := flatMap_insert x (part xs as) a (List.range K) ha List.nodup_range
      have e : part (x :: xs) (a :: as) =
          fun k => if a = k then x :: part xs as k else part xs as k :=
        funext (part_cons x xs a as)
      rw [e]
      exact (ih.cons x).trans this.symm
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem parts2 {c0 c1 : Rat} {ys : List Rat} (h : Packs [c0, c1] ys) :
    ∃ y1 y2 : List Rat, ys.Perm (y1 ++ y2) ∧ y1.sum ≤ c0 ∧ y2.sum ≤ c1 := by
  obtain ⟨as, hl, hin, hb⟩ := h
  have hp := perm_parts 2 ys as hl (by simpa using hin)
  refine ⟨part ys as 0, part ys as 1, by simpa [List.range_succ] using hp, ?_, ?_⟩
  · simpa [← binSum_eq_part] using hb 0 (by simp)
  · simpa [← binSum_eq_part] using hb 1 (by simp)

theorem parts3 {c0 c1 c2 : Rat} {ys : List Rat} (h : Packs [c0, c1, c2] ys) :
    ∃ y1 y2 y3 : List Rat, ys.Perm (y1 ++ y2 ++ y3) ∧ y1.sum ≤ c0 ∧ y2.sum ≤ c1 ∧
      y3.sum ≤ c2 := by
  obtain ⟨as, hl, hin, hb⟩ := h
  have hp := perm_parts 3 ys as hl (by simpa using hin)
  refine ⟨part ys as 0, part ys as 1, part ys as 2, by simpa [List.range_succ] using hp,
    ?_, ?_, ?_⟩
  · simpa [← binSum_eq_part] using hb 0 (by simp)
  · simpa [← binSum_eq_part] using hb 1 (by simp)
  · simpa [← binSum_eq_part] using hb 2 (by simp)

theorem parts4 {c0 c1 c2 c3 : Rat} {ys : List Rat} (h : Packs [c0, c1, c2, c3] ys) :
    ∃ y1 y2 y3 y4 : List Rat, ys.Perm (y1 ++ y2 ++ y3 ++ y4) ∧ y1.sum ≤ c0 ∧ y2.sum ≤ c1 ∧
      y3.sum ≤ c2 ∧ y4.sum ≤ c3 := by
  obtain ⟨as, hl, hin, hb⟩ := h
  have hp := perm_parts 4 ys as hl (by simpa using hin)
  refine ⟨part ys as 0, part ys as 1, part ys as 2, part ys as 3,
    by simpa [List.range_succ] using hp, ?_, ?_, ?_, ?_⟩
  · simpa [← binSum_eq_part] using hb 0 (by simp)
  · simpa [← binSum_eq_part] using hb 1 (by simp)
  · simpa [← binSum_eq_part] using hb 2 (by simp)
  · simpa [← binSum_eq_part] using hb 3 (by simp)

/-! ## The containments `Q ⊆ D_X` (Proposition 7.8's proof) -/

/-- Linear arithmetic over the Table 3 constants. -/
local macro "arith" : tactic => `(tactic| ((try simp only [δ] at *); grind))

theorem profile_rough {ys : List Rat} (h : Profile3 ys) : ∀ y ∈ ys, δ ≤ y := by
  obtain ⟨_, _, _, _, hX⟩ := h
  exact fun y hy => (hX.2.1 y hy).1

theorem profile_conds {ys : List Rat} (h : Profile3 ys) : CondsAE ξ1 ξ2 ξ3 ω11 δ εa ys := by
  obtain ⟨m, m', _, _, hX⟩ := h
  exact conds_table3 m m' ys hX

theorem δ_pos : (0 : Rat) < δ := by simp [δ]; decide +kernel

theorem div1 (a b ε0 ε1 : Rat) (ha : 0 < a) (hb : b < 1 / 2) (hw : δ ≤ b - a)
    (hε0 : 0 < ε0) (hε0' : ε0 < 1) (hε1 : 0 ≤ ε1) (hε1' : ε1 ≤ ε0 * (1 / 2 - a))
    (ys zs y1 y2 : List Rat) (hp : ys.Perm (y1 ++ y2)) (hy : ∀ y ∈ ys, δ ≤ y)
    (hI1 : y1.sum ≤ b) (hI2 : y2.sum ≤ 1 / 2 - a) (hz : Smooth zs)
    (hq : 1 / 2 - ε1 < (1 - ε0) * ys.sum + zs.sum) : HasDiv1 ε0 a b ys zs := by
  have hsum : ys.sum = y1.sum + y2.sum := by rw [perm_sum hp, List.sum_append]
  obtain ⟨J, R, h1, h2, h3⟩ := lemma_7_5 a b δ ε0 ε1 ha hb δ_pos hw hε0 hε0' hε1 hε1' y1 y2
    (fun y hy' => hy y (hp.symm.subset hy')) hI1 hI2 zs hz (by rw [← hsum]; exact hq)
  exact ⟨y1, y2, J, R, hp, h1, h2, h3⟩

/-- **Type I, `γ ≤ 1/2`.** (A)'s first partition and Lemma 7.5. -/
theorem contain_I_low : ContainIlow := by
  intro γ ε' ε0 ε1 h1 h2 h3 h4 h5 h6 h7 h8 ys zs hP hS hq
  obtain ⟨y1, y2, hp, hs1, hs2⟩ := parts2 (profile_conds hP).1.1
  have hd := (perm_I_low γ 0 h1 h2).2
  try simp only [capsA1G] at hs1 hs2
  simp only [dIlow, ω11, A1, ξ1, εa, δ] at *
  exact div1 _ _ ε0 ε1 (by arith) (by arith) (by arith) h5 h6 h7 h8 ys zs y1 y2 hp
    (profile_rough hP) (by arith) (by arith) hS hq

/-- **Type I, `γ ∈ (1/2, 1/2 + 2ω + ε′]`.** (A)'s second partition and Lemma 7.5. -/
theorem contain_I_high : ContainIhigh := by
  intro γ ε' ε0 ε1 h1 h2 h3 h4 h5 h6 h7 h8 ys zs hP hS hq
  obtain ⟨y1, y2, hp, hs1, hs2⟩ := parts2 (profile_conds hP).1.2
  have hd := (perm_I_high γ ε' h1 h2).2
  try simp only [capsA2G] at hs1 hs2
  simp only [dIhigh, ω11, A1, εa, δ] at *
  exact div1 _ _ ε0 ε1 (by arith) (by arith) (by arith) h5 h6 h7 h8 ys zs y1 y2 hp
    (profile_rough hP) (by arith) (by arith) hS hq

/-- **Type IIa.** (B) and Lemma 7.5. -/
theorem contain_IIa : ContainIIa := by
  intro γ ε' ε0 ε1 h1 h2 h3 h4 h5 h6 h7 h8 ys zs hP hS hq
  obtain ⟨y1, y2, hp, hs1, hs2⟩ := parts2 (profile_conds hP).2.1
  have hd := (perm_IIa γ h1 h2).2
  try simp only [capsBG] at hs1 hs2
  simp only [dIIa, gIIa, ω11, A1, εa, δ] at *
  exact div1 _ _ ε0 ε1 (by arith) (by arith) (by arith) h5 h6 h7 h8 ys zs y1 y2 hp
    (profile_rough hP) (by arith) (by arith) hS hq

/-- **Type III.** (E) and Lemma 7.5, at A4's width `dIII`. -/
theorem contain_III : ContainIII := by
  intro ε0 ε1 h5 h6 h7 h8 ys zs hP hS hq
  obtain ⟨y1, y2, hp, hs1, hs2⟩ := parts2 (profile_conds hP).2.2.2.2
  try simp only [capsEG] at hs1 hs2
  simp only [dIII, ω11, A1, ξ3, εa] at *
  exact div1 _ _ ε0 ε1 (by arith) (by arith) (by arith) h5 h6 h7 h8 ys zs y1 y2 hp
    (profile_rough hP) (by arith) (by arith) hS hq

/-- **Type IIb.** (C) and Lemma 7.6. -/
theorem contain_IIb : ContainIIb := by
  intro γ ε' ε0 ε1 h1 h2 h3 h4 h5 h6 h7 h8 ys zs hP hS hq
  obtain ⟨y1, y2, y3, hp, hs1, hs2, hs3⟩ := parts3 (profile_conds hP).2.2.1
  have hd := (perm_IIb γ h1 h2).2
  have hy := profile_rough hP
  have hsum : ys.sum = y1.sum + y2.sum + y3.sum := by
    rw [perm_sum hp, List.sum_append, List.sum_append]
  obtain ⟨J2, J1, R, hJ, k1, k2, k3, k4⟩ := lemma_7_6
    (γ - 3 * ε' - dIIb ω11 γ εa) (1 / 2 - γ - 2 * ω11 - 6 * ε' - dIIb ω11 γ εa)
    (γ - 3 * ε') (1 / 2 - γ - 2 * ω11 - 6 * ε') δ ε0 ε1
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    δ_pos
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    h5 h6 h7 h8 y1 y2 y3 (fun y hy' => hy y (hp.symm.subset hy'))
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    (by simp only [dIIb, gIIa, gIIc, ω11, A1, εa, δ] at *; grind)
    zs hS (by rw [← hsum]; exact hq)
  exact ⟨y1, y2, y3, J2, J1, R, hp, hJ, k1, k2, k3, k4⟩

/-- **Type IIc.** (D) at `(γ, ω₀)` and Lemma 7.7, with `δ*(γ) = δ`. -/
theorem contain_IIc : ContainIIc := by
  intro γ ω0 ε' h1 h2 h3 h4 h5 h6 ys zs hP hS hq
  obtain ⟨y1, y2, y3, y4, hp, hs1, hs2, hs3, hs4⟩ :=
    parts4 ((profile_conds hP).2.2.2.1 ω0 γ h3 h4 h1 h2)
  have hy := profile_rough hP
  have hsum : ys.sum = y1.sum + y2.sum + y3.sum + y4.sum := by
    rw [perm_sum hp, List.sum_append, List.sum_append, List.sum_append]
  have hδ := δ_pos
  obtain ⟨J2, J1, R, hJ, k1, k2, k3, k4, k5⟩ := lemma_7_7
    (γ - 3 * ε' - δ) (1 - γ - 6 * ε' - δ - (1 / 2 + 2 * ω0))
    (2 - γ - 52 * ε' - δ - 4 * (1 / 2 + 2 * ω0))
    (γ - 3 * ε') (1 - γ - 6 * ε' - (1 / 2 + 2 * ω0)) (2 - γ - 52 * ε' - 4 * (1 / 2 + 2 * ω0))
    δ ω0 0
    (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
    y1 y2 y3 y4
    (by (try simp only [capsDG] at *); grind) (by (try simp only [capsDG] at *); grind)
    (by (try simp only [capsDG] at *); grind) (by (try simp only [capsDG] at *); grind)
    zs hS (by rw [← hsum]; exact hq)
  exact ⟨y1, y2, y3, y4, J2, J1, R, hp, hJ, k1, k2, k3, k4, k5⟩

/-! ## Theorem 7.11 relative to the named analytic inputs -/

theorem εa_nonneg : (0 : Rat) ≤ εa := by simp [εa]; decide +kernel

theorem permI_zero {ω' γ δs ε : Rat} (h : PermI εa ω' γ δs ε) : PermI 0 ω' γ δs ε := by
  have := εa_nonneg
  simp only [PermI] at *
  exact ⟨fun h1 => by have := h.1 h1; grind, fun h1 h2 => by have := h.2 h1 h2; grind⟩

theorem permIIa_zero {ω' γ δs : Rat} (h : PermIIa εa ω' γ δs) : PermIIa 0 ω' γ δs := by
  have := εa_nonneg; simp only [PermIIa] at *; grind

theorem permIIb_zero {ω' γ δs : Rat} (h : PermIIb εa ω' γ δs) : PermIIb 0 ω' γ δs := by
  have := εa_nonneg; simp only [PermIIb] at *; grind

theorem permIIc_zero {ω' γ δs : Rat} (h : PermIIc εa ω' γ δs) : PermIIc 0 ω' γ δs := by
  have := εa_nonneg; simp only [PermIIc] at *; grind

theorem permIII_zero {ω' γ δs : Rat} (h : PermIII εa ω' γ δs) : PermIII 0 ω' γ δs := by
  have := εa_nonneg; simp only [PermIII] at *; grind

/-- **Theorem 7.11, relative to its named analytic inputs.** Every combinatorial antecedent
(Definition 4.1, Proposition 7.8 (I)–(III) and (A)–(E), the permissible triples at the
proof's `δ*(γ)` over every `γ`-range, and the containments `Q ⊆ D_X`) is discharged here. -/
theorem theorem_7_11 (H : AnalyticInputs) : H.PositiveLevel ∧ H.HalfLevel := by
  have hpos : H.PositiveLevel := H.prop_7_8_assembly
    (fun γ ε h1 h2 => H.lemma_5_3 _ _ _ _ (permI_zero (perm_I_low γ ε h1 h2).1))
    (fun γ ε h1 h2 => H.lemma_5_3 _ _ _ _ (permI_zero (perm_I_high γ ε h1 h2).1))
    (fun γ h1 h2 => H.lemma_5_4 _ _ _ (permIIa_zero (perm_IIa γ h1 h2).1))
    (fun γ h1 h2 => H.lemma_5_5 _ _ _ (permIIb_zero (perm_IIb γ h1 h2).1))
    (fun γ h1 h2 => H.lemma_5_6 _ _ _ (permIIc_zero (perm_IIc γ h1 h2).1))
    (H.lemma_5_7 _ _ _ (permIII_zero perm_III.1))
    contain_I_low contain_I_high contain_IIa contain_IIb contain_IIc contain_III
  exact ⟨hpos, H.theorem_8_3 prop_7_8_packing_table3 hpos⟩

end BGP212.T711

namespace BGP212.Challenge

open BGP212.Params BGP212.Packing BGP212.T711

theorem definition_4_1_table3 : SupportDatum 1 A3 B3 δ εs ∧ floorInv δ = 60 :=
  support_datum_table3

theorem omega_11_table3 : omegaJJ A3 1 1 = ω11 ∧ ω11 = ω := omega_table3

theorem prop_7_8_I_III_table3 : Prop78Scalar 1 A3 δ ξ1 ξ2 ξ3 εa := prop_7_8_scalar_table3

theorem lemma_7_10_case_split :
    ∀ m m' ys, Xi (B m) (B m') m m' δ ys → CondsAE ξ1 ξ2 ξ3 ω11 δ εa ys :=
  conds_table3

theorem prop_7_8_A_E_table3 : Prop78Packing 1 A3 B3 δ ξ1 ξ2 ξ3 εa := prop_7_8_packing_table3

theorem type_II_cover :
    ξ2 - εa < gIIc ω11 δ εa ∧ gIIc ω11 δ εa < gIIa ω11 δ εa ∧ gIIa ω11 δ εa < 1 / 2 ∧
    ∀ γ, ξ2 - εa ≤ γ → γ ≤ 1 / 2 →
      γ ≤ gIIc ω11 δ εa ∨ (gIIc ω11 δ εa < γ ∧ γ < gIIa ω11 δ εa) ∨ gIIa ω11 δ εa ≤ γ :=
  BGP212.T711.type_II_cover

theorem perm_type_I_low (γ ε : Rat) (h1 : ξ1 - εa ≤ γ) (h2 : γ ≤ 1 / 2) :
    PermI εa ω11 γ (dIlow ω11 γ εa) ε ∧ δ ≤ dIlow ω11 γ εa :=
  perm_I_low γ ε h1 h2

theorem perm_type_I_high (γ ε : Rat) (h1 : 1 / 2 < γ) (_h2 : γ ≤ 1 / 2 + 2 * ω11 + ε) :
    PermI εa ω11 γ (dIhigh ω11 εa) ε ∧ δ ≤ dIhigh ω11 εa :=
  perm_I_high γ ε h1 _h2

theorem perm_type_IIa (γ : Rat) (h1 : gIIa ω11 δ εa ≤ γ) (h2 : γ ≤ 1 / 2) :
    PermIIa εa ω11 γ (dIIa ω11 γ εa) ∧ δ ≤ dIIa ω11 γ εa :=
  perm_IIa γ h1 h2

theorem perm_type_IIb (γ : Rat) (h1 : gIIc ω11 δ εa < γ) (h2 : γ < gIIa ω11 δ εa) :
    PermIIb εa ω11 γ (dIIb ω11 γ εa) ∧ δ ≤ dIIb ω11 γ εa :=
  perm_IIb γ h1 h2

theorem perm_type_IIc (γ : Rat) (h1 : ξ2 - εa ≤ γ) (h2 : γ ≤ gIIc ω11 δ εa) :
    PermIIc εa ω11 γ δ ∧
    δ ≤ 1 / 4 - 2 * ω11 - γ / 2 ∧ δ ≤ γ / 10 - 32 * ω11 / 10 ∧
    δ ≤ γ / 4 - 1 / 16 - 3 * ω11 - εa :=
  perm_IIc γ h1 h2

theorem perm_type_III : PermIII εa ω11 (ξ3 + εa) (dIII ω11 ξ3 εa) ∧ δ < dIII ω11 ξ3 εa :=
  perm_III

theorem type_III_printed_gap :
    PermIII 0 ω11 ξ3 (dIIIprinted ω11 ξ3 εa) ∧
    ¬ PermIII 0 ω11 (ξ3 + εa) (dIIIprinted ω11 ξ3 εa) ∧
    28 * ω11 + 9 * (ξ3 + εa) + 8 * dIIIprinted ω11 ξ3 εa = 4 + εa :=
  BGP212.T711.type_III_printed_gap

theorem type_I_high_choice :
    (1 / 2 + 1 / 1000) - 1 / 2 + δ + 3 * (εa / 3) < 1 / 14 - 68 / 14 * ω11 - 2 * εa ∧
    1 / 14 - 68 / 14 * ω11 - 2 * εa ≤ (1 / 2 + 1 / 1000) - 1 / 2 + dIhigh ω11 εa + 3 * (εa / 3) :=
  BGP212.T711.type_I_high_choice

theorem type_IIc_mixed_monotonicity (γ ω0 d d' ϵ : Rat) (h : d ≤ d') :
    (capsDG γ ω0 d' ϵ)[0]! ≤ (capsDG γ ω0 d ϵ)[0]! ∧
    (capsDG γ ω0 d ϵ)[2]! ≤ (capsDG γ ω0 d' ϵ)[2]! := by
  simp [capsDG]; constructor <;> grind

theorem lemma_4_2_step_at_zero : ¬ (B 1 ≤ B 0 + δ) ∧ ∀ q : Nat, 1 ≤ q → B (q + 1) ≤ B q + δ :=
  ⟨by decide +kernel, fun q hq => (definition_4_1_caps q hq).2.2⟩

theorem containment_I_low : ContainIlow := contain_I_low
theorem containment_I_high : ContainIhigh := contain_I_high
theorem containment_IIa : ContainIIa := contain_IIa
theorem containment_IIb : ContainIIb := contain_IIb
theorem containment_IIc : ContainIIc := contain_IIc
theorem containment_III : ContainIII := contain_III

theorem theorem_7_11_core :
    SupportDatum 1 A3 B3 δ εs ∧ Prop78Scalar 1 A3 δ ξ1 ξ2 ξ3 εa ∧
    Prop78Packing 1 A3 B3 δ ξ1 ξ2 ξ3 εa ∧
    ContainIlow ∧ ContainIhigh ∧ ContainIIa ∧ ContainIIb ∧ ContainIIc ∧ ContainIII :=
  ⟨support_datum_table3.1, prop_7_8_scalar_table3, prop_7_8_packing_table3,
    contain_I_low, contain_I_high, contain_IIa, contain_IIb, contain_IIc, contain_III⟩

theorem theorem_7_11 (H : AnalyticInputs) : H.PositiveLevel ∧ H.HalfLevel :=
  BGP212.T711.theorem_7_11 H

end BGP212.Challenge
