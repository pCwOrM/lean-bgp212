/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 7.4, Proposition 7.8 (A)–(E), Lemma 7.10 (p. 36).
-/
import BGP212.Packing

/-! # A3a: packing proofs

Core Lean only.

* `greedy_pack`: fill the selected bins in turn; each filled bin wastes less than `s`.
* `largest_coordinate`: on a side of `k` coordinates, each is at most `B − (k − 1)δ`.
* The 295 settled roots of conditions (A), (B), (C), (E) come with a certificate, the bin
  selection(s) in `certTable`; `certValid` re-checks every inequality in exact rationals
  inside the kernel (`decide +kernel`), and `pack_of_cert` turns a valid certificate into the
  root. The certificate table only chooses bins; it asserts nothing the kernel does not check.
* The settled (D) root `(1, 1)` is proved by hand, uniformly over the full `(γ, ω₀)` box. -/

namespace BGP212.Packing

open BGP212.Params BGP212.Ledger

/-! ## Bin loads -/

theorem binSum_nil_left (as : List Nat) (k : Nat) : binSum [] as k = 0 := by
  simp [binSum]

theorem binSum_cons (x : Rat) (xs : List Rat) (a : Nat) (as : List Nat) (k : Nat) :
    binSum (x :: xs) (a :: as) k = (if a = k then x else 0) + binSum xs as k := by
  unfold binSum
  by_cases h : a = k
  · subst h; simp
  · simp [h]; grind

theorem binSum_append : ∀ (xs ys : List Rat) (as bs : List Nat), as.length = xs.length →
    ∀ k, binSum (xs ++ ys) (as ++ bs) k = binSum xs as k + binSum ys bs k
  | [], ys, [], bs, _, k => by simp [binSum_nil_left]; grind
  | x :: xs, ys, a :: as, bs, h, k => by
      simp only [List.cons_append, binSum_cons]
      rw [binSum_append xs ys as bs (by simpa using h) k]
      grind
  | [], _, _ :: _, _, h, _ => by simp at h
  | _ :: _, _, [], _, h, _ => by simp at h

theorem binSum_replicate (i k : Nat) : ∀ xs : List Rat,
    binSum xs (List.replicate xs.length i) k = if i = k then xs.sum else 0
  | [] => by simp [binSum_nil_left]
  | x :: xs => by
      rw [List.length_cons, List.replicate_succ, binSum_cons, binSum_replicate i k xs]
      by_cases h : i = k <;> simp [h, List.sum_cons] <;> grind

theorem binSum_avoid (k : Nat) : ∀ (xs : List Rat) (as : List Nat), (∀ a ∈ as, a ≠ k) →
    binSum xs as k = 0
  | [], _, _ => binSum_nil_left _ _
  | _ :: _, [], _ => by simp [binSum]
  | x :: xs, a :: as, h => by
      rw [binSum_cons, binSum_avoid k xs as (fun b hb => h b (by simp [hb]))]
      simp [h a (by simp)]; grind

/-! ## Filling one bin -/

theorem fill (s : Rat) : ∀ (items : List Rat) (c : Rat), 0 ≤ c → (∀ y ∈ items, y ≤ s) →
    ∃ j, j ≤ items.length ∧ (items.take j).sum ≤ c ∧
      (j = items.length ∨ c - s < (items.take j).sum)
  | [], c, hc, _ => ⟨0, by simp, by simp; grind, Or.inl rfl⟩
  | y :: ys, c, hc, hs => by
      by_cases hy : y ≤ c
      · obtain ⟨j, hj, h1, h2⟩ := fill s ys (c - y) (by grind) (fun z hz => hs z (by simp [hz]))
        refine ⟨j + 1, by simp; omega, ?_, ?_⟩
        · simp only [List.take_succ_cons, List.sum_cons]; grind
        · rcases h2 with h | h
          · left; simp [h]
          · right; simp only [List.take_succ_cons, List.sum_cons]; grind
      · have := hs y (by simp)
        exact ⟨0, by simp, by simp; grind, Or.inr (by simp; grind)⟩

/-! ## Greedy packing -/

theorem greedy_core (caps : List Rat) (s : Rat) (hcap : ∀ k, k < caps.length → 0 ≤ caps[k]!) :
    ∀ (sel : List Nat), sel ≠ [] → sel.Nodup → (∀ i ∈ sel, i < caps.length) →
    ∀ (items : List Rat), (∀ y ∈ items, y ≤ s) →
      items.sum ≤ (sel.map fun i => caps[i]!).sum - ((sel.length : Rat) - 1) * s →
      ∃ assign : List Nat, assign.length = items.length ∧ (∀ a ∈ assign, a ∈ sel) ∧
        ∀ k ∈ sel, binSum items assign k ≤ caps[k]!
  | [], h, _, _, _, _, _ => absurd rfl h
  | [i], _, _, _, items, _, hT => by
      refine ⟨List.replicate items.length i, by simp, ?_, ?_⟩
      · intro a ha; simp [List.mem_replicate] at ha; simp [ha.2]
      · intro k hk
        simp only [List.mem_singleton] at hk
        subst hk
        rw [binSum_replicate]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.length_singleton, ite_true] at hT ⊢
        grind
  | i :: i2 :: rest, _, hnd, hin, items, hs, hT => by
      have hc : 0 ≤ caps[i]! := hcap i (hin i (by simp))
      have hi_notin : i ∉ i2 :: rest := (List.nodup_cons.mp hnd).1
      obtain ⟨j, hj, h1, h2⟩ := fill s items (caps[i]!) hc hs
      rcases h2 with hfull | hpart
      · refine ⟨List.replicate items.length i, by simp, ?_, ?_⟩
        · intro a ha; simp [List.mem_replicate] at ha; simp [ha.2]
        · intro k hk
          rw [binSum_replicate]
          by_cases hik : i = k
          · subst hik; simp only [ite_true]; rw [hfull, List.take_length] at h1; exact h1
          · simp only [hik, ite_false]; exact hcap k (hin k hk)
      · have hsplit : items = items.take j ++ items.drop j := (List.take_append_drop j items).symm
        have hsum : items.sum = (items.take j).sum + (items.drop j).sum := by
          have := congrArg List.sum hsplit
          rw [List.sum_append] at this
          exact this
        have hT' : (items.drop j).sum ≤ ((i2 :: rest).map fun i => caps[i]!).sum -
            (((i2 :: rest).length : Rat) - 1) * s := by
          simp only [List.map_cons, List.sum_cons, List.length_cons] at hT ⊢
          push_cast at hT ⊢
          grind
        obtain ⟨aR, hlen, hmem, hbound⟩ := greedy_core caps s hcap (i2 :: rest) (by simp)
          (List.nodup_cons.mp hnd).2 (fun k hk => hin k (by simp [hk])) (items.drop j)
          (fun y hy => hs y (List.mem_of_mem_drop hy)) hT'
        have htl : (items.take j).length = j := by simp; omega
        refine ⟨List.replicate j i ++ aR, ?_, ?_, ?_⟩
        · simp [hlen]; omega
        · intro a ha
          rcases List.mem_append.mp ha with h | h
          · simp [List.mem_replicate] at h; simp [h.2]
          · exact List.mem_cons_of_mem i (hmem a h)
        · intro k hk
          have hb : binSum items (List.replicate j i ++ aR) k =
              binSum (items.take j) (List.replicate j i) k + binSum (items.drop j) aR k := by
            have := binSum_append (items.take j) (items.drop j) (List.replicate j i) aR
              (by simp [htl]) k
            rw [← hsplit] at this
            exact this
          rw [hb, show List.replicate j i = List.replicate (items.take j).length i by rw [htl],
            binSum_replicate]
          rcases List.mem_cons.mp hk with hki | hk'
          · subst hki
            have h0 : binSum (items.drop j) aR k = 0 :=
              binSum_avoid k _ _ (fun a ha hak => hi_notin (hak ▸ hmem a ha))
            simp only [ite_true, h0]; grind
          · have hik : i ≠ k := fun h => hi_notin (h ▸ hk')
            simp only [hik, ite_false]
            have := hbound k hk'
            grind

end BGP212.Packing

namespace BGP212.Challenge

open BGP212.Params BGP212.Ledger BGP212.Packing

theorem greedy_pack (caps items : List Rat) (s : Rat) (sel : List Nat)
    (hsel : sel ≠ []) (hnd : sel.Nodup) (hin : ∀ i ∈ sel, i < caps.length)
    (hcap : ∀ k, k < caps.length → 0 ≤ caps[k]!) (hs : ∀ y ∈ items, y ≤ s)
    (hT : items.sum ≤ (sel.map fun i => caps[i]!).sum - ((sel.length : Rat) - 1) * s) :
    Packs caps items := by
  obtain ⟨assign, hlen, hmem, hbound⟩ := greedy_core caps s hcap sel hsel hnd hin items hs hT
  refine ⟨assign, hlen, fun a ha => hin a (hmem a ha), fun k hk => ?_⟩
  by_cases hks : k ∈ sel
  · exact hbound k hks
  · rw [binSum_avoid k items assign (fun a ha hak => hks (hak ▸ hmem a ha))]
    exact hcap k hk

theorem perm_sum' {l1 l2 : List Rat} (h : l1.Perm l2) : l1.sum = l2.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap x y l => simp [List.sum_cons]; grind
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem sum_ge_length_mul (δ' : Rat) : ∀ ys : List Rat, (∀ y ∈ ys, δ' ≤ y) →
    (ys.length : Rat) * δ' ≤ ys.sum
  | [], _ => by simp
  | y :: ys, h => by
      have h1 := h y (by simp)
      have h2 := sum_ge_length_mul δ' ys (fun z hz => h z (by simp [hz]))
      simp only [List.length_cons, List.sum_cons]
      push_cast
      grind

theorem largest_coordinate (δ' Bc : Rat) (ys : List Rat) (hδ : ∀ y ∈ ys, δ' ≤ y)
    (hsum : ys.sum ≤ Bc) :
    ∀ y ∈ ys, y ≤ Bc - ((ys.length : Rat) - 1) * δ' := by
  intro y hy
  have hp := List.perm_cons_erase hy
  have hs : ys.sum = y + (ys.erase y).sum := by
    have := perm_sum' hp
    simpa [List.sum_cons] using this
  have hl : ys.length = (ys.erase y).length + 1 := by
    have := hp.length_eq
    simpa using this
  have hge := sum_ge_length_mul δ' (ys.erase y)
    (fun z hz => hδ z (List.mem_of_mem_erase hz))
  rw [hl]
  push_cast
  grind

theorem omega_matches_table3 : ω11 = ω := by
  decide +kernel

theorem root_ledger :
    settledRoots.length = 296 ∧ openRoots.length = 159 ∧
    (settledRoots ++ openRoots).Perm allRoots ∧ allRoots.length = 455 := by
  decide +kernel

/-! ## Certificates for the constant-capacity conditions -/

/-- The per-profile item bound `max(B₁,ₘ − (m−1)δ, B₁,ₘ′ − (m′−1)δ)`. -/
def smax (m m' : Nat) : Rat := max (B m - ((m : Rat) - 1) * δ) (B m' - ((m' : Rat) - 1) * δ)

/-- A greedy certificate: bins `sel` of `caps` absorb total `T` with item bound `s`. -/
def CertOK (caps : List Rat) (T s : Rat) (sel : List Nat) : Prop :=
  sel ≠ [] ∧ sel.Nodup ∧ (∀ i ∈ sel, i < caps.length) ∧
    (∀ k, k < caps.length → 0 ≤ caps[k]!) ∧
    T ≤ (sel.map fun i => caps[i]!).sum - ((sel.length : Rat) - 1) * s

instance (caps : List Rat) (T s : Rat) (sel : List Nat) : Decidable (CertOK caps T s sel) := by
  unfold CertOK; infer_instance

/-- A certificate row: condition, `m`, `m′`, the bin selection, and for (A) the selection
for its second partition. -/
def certValid : Cond × Nat × Nat × List Nat × List Nat → Prop
  | (.A, m, m', s1, s2) => CertOK capsA1 (B m + B m') (smax m m') s1 ∧
      CertOK capsA2 (B m + B m') (smax m m') s2
  | (.B, m, m', s1, _) => CertOK capsB (B m + B m') (smax m m') s1
  | (.C, m, m', s1, _) => CertOK capsC (B m + B m') (smax m m') s1
  | (.E, m, m', s1, _) => CertOK capsE (B m + B m') (smax m m') s1
  | (.D, _, _, _, _) => False

instance (x : Cond × Nat × Nat × List Nat × List Nat) : Decidable (certValid x) := by
  rcases x with ⟨c, m, m', s1, s2⟩; cases c <;> unfold certValid <;> infer_instance

/-- The certificate table for the 295 settled roots of (A), (B), (C), (E), generated by
specs/checks/packing_ledger.py and stored in specs/certificates/packing_a3a.json. -/
def certTable : List (Cond × Nat × Nat × List Nat × List Nat) := [
    (.A, 1, 1, [0], [0]),
    (.A, 1, 2, [0], [0]),
    (.A, 1, 3, [0], [0]),
    (.A, 1, 4, [0], [0]),
    (.A, 1, 5, [0], [0]),
    (.A, 1, 6, [0], [0]),
    (.A, 1, 7, [0], [0]),
    (.A, 1, 8, [0], [0]),
    (.A, 1, 9, [0], [0]),
    (.A, 1, 10, [0], [0]),
    (.A, 1, 11, [0], [0]),
    (.A, 1, 12, [0], [0]),
    (.A, 1, 13, [0], [0]),
    (.A, 2, 2, [0], [0]),
    (.A, 2, 3, [0], [0]),
    (.A, 2, 4, [0], [0]),
    (.A, 2, 5, [0], [0]),
    (.A, 2, 6, [0], [0]),
    (.A, 2, 7, [0], [0]),
    (.A, 2, 8, [0], [0]),
    (.A, 2, 9, [0], [0]),
    (.A, 2, 10, [0], [0]),
    (.A, 2, 11, [0], [0]),
    (.A, 2, 12, [0], [0]),
    (.A, 2, 13, [0], [0]),
    (.A, 3, 3, [0], [0]),
    (.A, 3, 4, [0], [0]),
    (.A, 3, 5, [0], [0]),
    (.A, 3, 6, [0], [0]),
    (.A, 3, 7, [0], [0]),
    (.A, 4, 4, [0], [0]),
    (.A, 4, 5, [0], [0]),
    (.A, 4, 6, [0, 1], [0]),
    (.A, 5, 5, [0, 1], [0]),
    (.A, 5, 6, [0, 1], [0]),
    (.A, 6, 6, [0, 1], [0]),
    (.A, 6, 7, [0, 1], [0]),
    (.A, 7, 7, [0, 1], [0]),
    (.A, 7, 8, [0, 1], [0]),
    (.A, 8, 8, [0, 1], [0]),
    (.A, 8, 9, [0, 1], [0]),
    (.A, 8, 10, [0, 1], [0]),
    (.A, 8, 11, [0, 1], [0]),
    (.A, 8, 12, [0, 1], [0]),
    (.A, 8, 13, [0, 1], [0]),
    (.A, 9, 9, [0, 1], [0]),
    (.A, 9, 10, [0, 1], [0]),
    (.A, 9, 11, [0, 1], [0]),
    (.A, 9, 12, [0, 1], [0]),
    (.A, 9, 13, [0, 1], [0]),
    (.A, 10, 10, [0, 1], [0]),
    (.A, 10, 11, [0, 1], [0]),
    (.A, 10, 12, [0, 1], [0]),
    (.A, 10, 13, [0, 1], [0]),
    (.A, 11, 11, [0, 1], [0]),
    (.A, 11, 12, [0, 1], [0]),
    (.A, 11, 13, [0, 1], [0]),
    (.A, 12, 12, [0, 1], [0]),
    (.A, 12, 13, [0, 1], [0]),
    (.A, 13, 13, [0, 1], [0]),
    (.B, 1, 1, [0], []),
    (.B, 1, 2, [0], []),
    (.B, 1, 3, [0], []),
    (.B, 1, 4, [0], []),
    (.B, 1, 5, [0], []),
    (.B, 1, 6, [0], []),
    (.B, 1, 7, [0], []),
    (.B, 1, 8, [0], []),
    (.B, 1, 9, [0], []),
    (.B, 1, 10, [0], []),
    (.B, 1, 11, [0], []),
    (.B, 1, 12, [0], []),
    (.B, 1, 13, [0], []),
    (.B, 2, 2, [0], []),
    (.B, 2, 3, [0], []),
    (.B, 2, 4, [0], []),
    (.B, 2, 5, [0], []),
    (.B, 2, 6, [0], []),
    (.B, 2, 7, [0], []),
    (.B, 2, 8, [0], []),
    (.B, 2, 9, [0], []),
    (.B, 2, 10, [0], []),
    (.B, 2, 11, [0], []),
    (.B, 2, 12, [0], []),
    (.B, 2, 13, [0], []),
    (.B, 3, 3, [0], []),
    (.B, 3, 4, [0], []),
    (.B, 3, 5, [0], []),
    (.B, 3, 6, [0], []),
    (.B, 3, 7, [0], []),
    (.B, 3, 8, [0], []),
    (.B, 3, 9, [0], []),
    (.B, 3, 10, [0], []),
    (.B, 3, 11, [0], []),
    (.B, 3, 12, [0], []),
    (.B, 3, 13, [0], []),
    (.B, 4, 4, [0], []),
    (.B, 4, 5, [0], []),
    (.B, 4, 6, [0], []),
    (.B, 4, 7, [0], []),
    (.B, 4, 8, [0], []),
    (.B, 4, 9, [0], []),
    (.B, 4, 10, [0], []),
    (.B, 4, 11, [0], []),
    (.B, 4, 12, [0], []),
    (.B, 4, 13, [0], []),
    (.B, 5, 5, [0], []),
    (.B, 5, 6, [0], []),
    (.B, 5, 7, [0], []),
    (.B, 5, 8, [0], []),
    (.B, 5, 9, [0], []),
    (.B, 5, 10, [0], []),
    (.B, 5, 11, [0], []),
    (.B, 5, 12, [0], []),
    (.B, 5, 13, [0], []),
    (.B, 6, 6, [0], []),
    (.B, 6, 7, [0], []),
    (.B, 6, 8, [0], []),
    (.B, 6, 9, [0], []),
    (.B, 6, 10, [0], []),
    (.B, 6, 11, [0], []),
    (.B, 6, 12, [0], []),
    (.B, 6, 13, [0], []),
    (.B, 7, 7, [0], []),
    (.B, 7, 8, [0], []),
    (.B, 7, 9, [0], []),
    (.B, 7, 10, [0], []),
    (.B, 7, 11, [0], []),
    (.B, 7, 12, [0], []),
    (.B, 7, 13, [0], []),
    (.B, 8, 8, [0], []),
    (.B, 8, 9, [0], []),
    (.B, 8, 10, [0], []),
    (.B, 8, 11, [0], []),
    (.B, 8, 12, [0], []),
    (.B, 8, 13, [0], []),
    (.B, 9, 9, [0], []),
    (.B, 9, 10, [0], []),
    (.B, 9, 11, [0], []),
    (.B, 9, 12, [0], []),
    (.B, 9, 13, [0], []),
    (.B, 10, 10, [0], []),
    (.B, 10, 11, [0], []),
    (.B, 10, 12, [0], []),
    (.B, 10, 13, [0], []),
    (.B, 11, 11, [0], []),
    (.B, 11, 12, [0], []),
    (.B, 11, 13, [0], []),
    (.B, 12, 12, [0], []),
    (.B, 12, 13, [0], []),
    (.B, 13, 13, [0], []),
    (.C, 1, 1, [0], []),
    (.C, 1, 2, [0], []),
    (.C, 1, 3, [0], []),
    (.C, 1, 4, [0], []),
    (.C, 1, 5, [0], []),
    (.C, 1, 6, [0], []),
    (.C, 1, 7, [0], []),
    (.C, 1, 8, [0], []),
    (.C, 1, 9, [0], []),
    (.C, 1, 10, [0], []),
    (.C, 1, 11, [0], []),
    (.C, 1, 12, [0], []),
    (.C, 1, 13, [0], []),
    (.C, 2, 2, [0], []),
    (.C, 2, 3, [0], []),
    (.C, 2, 4, [0], []),
    (.C, 2, 5, [0], []),
    (.C, 2, 6, [0], []),
    (.C, 2, 7, [0], []),
    (.C, 2, 8, [0], []),
    (.C, 2, 9, [0], []),
    (.C, 2, 10, [0], []),
    (.C, 2, 11, [0], []),
    (.C, 2, 12, [0], []),
    (.C, 2, 13, [0], []),
    (.C, 3, 3, [0], []),
    (.C, 3, 4, [0], []),
    (.C, 3, 5, [0], []),
    (.C, 3, 6, [0], []),
    (.C, 3, 7, [0], []),
    (.C, 3, 8, [0], []),
    (.C, 3, 9, [0], []),
    (.C, 3, 10, [0], []),
    (.C, 3, 11, [0], []),
    (.C, 3, 12, [0], []),
    (.C, 3, 13, [0], []),
    (.C, 4, 4, [0], []),
    (.C, 4, 5, [0], []),
    (.C, 4, 6, [0], []),
    (.C, 4, 7, [0], []),
    (.C, 4, 8, [0], []),
    (.C, 4, 9, [0], []),
    (.C, 4, 10, [0], []),
    (.C, 4, 11, [0], []),
    (.C, 4, 12, [0], []),
    (.C, 4, 13, [0], []),
    (.C, 5, 5, [0], []),
    (.C, 5, 6, [0], []),
    (.C, 5, 7, [0], []),
    (.C, 5, 8, [0], []),
    (.C, 5, 9, [0], []),
    (.C, 5, 10, [0], []),
    (.C, 5, 11, [0], []),
    (.C, 5, 12, [0], []),
    (.C, 5, 13, [0], []),
    (.C, 6, 6, [0], []),
    (.C, 6, 7, [0], []),
    (.C, 6, 8, [0], []),
    (.C, 6, 9, [0], []),
    (.C, 6, 10, [0], []),
    (.C, 6, 11, [0], []),
    (.C, 6, 12, [0], []),
    (.C, 6, 13, [0], []),
    (.C, 7, 7, [0], []),
    (.C, 7, 8, [0], []),
    (.C, 7, 9, [0], []),
    (.C, 7, 10, [0], []),
    (.C, 7, 11, [0], []),
    (.C, 7, 12, [0], []),
    (.C, 7, 13, [0], []),
    (.C, 8, 8, [0], []),
    (.C, 8, 9, [0], []),
    (.C, 8, 10, [0], []),
    (.C, 8, 11, [0], []),
    (.C, 8, 12, [0], []),
    (.C, 8, 13, [0], []),
    (.C, 9, 9, [0], []),
    (.C, 13, 13, [0, 1], []),
    (.E, 1, 1, [0], []),
    (.E, 1, 2, [0], []),
    (.E, 1, 3, [0], []),
    (.E, 1, 4, [0], []),
    (.E, 1, 5, [0], []),
    (.E, 1, 6, [0], []),
    (.E, 1, 7, [0, 1], []),
    (.E, 1, 8, [0, 1], []),
    (.E, 1, 9, [0, 1], []),
    (.E, 2, 2, [0], []),
    (.E, 2, 3, [0], []),
    (.E, 2, 4, [0], []),
    (.E, 2, 5, [0], []),
    (.E, 2, 6, [0], []),
    (.E, 2, 7, [0, 1], []),
    (.E, 2, 8, [0, 1], []),
    (.E, 2, 9, [0, 1], []),
    (.E, 2, 10, [0, 1], []),
    (.E, 2, 11, [0, 1], []),
    (.E, 2, 12, [0, 1], []),
    (.E, 2, 13, [0, 1], []),
    (.E, 3, 3, [0], []),
    (.E, 3, 4, [0, 1], []),
    (.E, 3, 5, [0, 1], []),
    (.E, 3, 6, [0, 1], []),
    (.E, 3, 7, [0, 1], []),
    (.E, 4, 4, [0, 1], []),
    (.E, 4, 5, [0, 1], []),
    (.E, 4, 6, [0, 1], []),
    (.E, 4, 7, [0, 1], []),
    (.E, 5, 5, [0, 1], []),
    (.E, 5, 6, [0, 1], []),
    (.E, 5, 7, [0, 1], []),
    (.E, 5, 8, [0, 1], []),
    (.E, 6, 6, [0, 1], []),
    (.E, 6, 7, [0, 1], []),
    (.E, 6, 8, [0, 1], []),
    (.E, 6, 9, [0, 1], []),
    (.E, 7, 7, [0, 1], []),
    (.E, 7, 8, [0, 1], []),
    (.E, 7, 9, [0, 1], []),
    (.E, 7, 10, [0, 1], []),
    (.E, 7, 11, [0, 1], []),
    (.E, 7, 12, [0, 1], []),
    (.E, 7, 13, [0, 1], []),
    (.E, 8, 8, [0, 1], []),
    (.E, 8, 9, [0, 1], []),
    (.E, 8, 10, [0, 1], []),
    (.E, 8, 11, [0, 1], []),
    (.E, 8, 12, [0, 1], []),
    (.E, 8, 13, [0, 1], []),
    (.E, 9, 9, [0, 1], []),
    (.E, 9, 10, [0, 1], []),
    (.E, 9, 11, [0, 1], []),
    (.E, 9, 12, [0, 1], []),
    (.E, 9, 13, [0, 1], []),
    (.E, 10, 10, [0, 1], []),
    (.E, 10, 11, [0, 1], []),
    (.E, 10, 12, [0, 1], []),
    (.E, 10, 13, [0, 1], []),
    (.E, 11, 11, [0, 1], []),
    (.E, 11, 12, [0, 1], []),
    (.E, 11, 13, [0, 1], []),
    (.E, 12, 12, [0, 1], []),
    (.E, 12, 13, [0, 1], []),
    (.E, 13, 13, [0, 1], []) ]

theorem pack_of_cert {caps : List Rat} {m m' : Nat} {sel : List Nat}
    (hc : CertOK caps (B m + B m') (smax m m') sel) {ys ys' : List Rat}
    (hX : InXi (B m) (B m') m m' ys ys') : Packs caps (ys ++ ys') := by
  obtain ⟨hlen, hlen', hrange, hs1, hs2⟩ := hX
  obtain ⟨hne, hnd, hin, hcap, hT⟩ := hc
  apply greedy_pack caps (ys ++ ys') (smax m m') sel hne hnd hin hcap
  · intro y hy
    rcases List.mem_append.mp hy with h | h
    · have := largest_coordinate δ (B m) ys
        (fun z hz => (hrange z (List.mem_append_left _ hz)).1) hs1 y h
      rw [hlen] at this
      unfold smax; grind
    · have := largest_coordinate δ (B m') ys'
        (fun z hz => (hrange z (List.mem_append_right _ hz)).1) hs2 y h
      rw [hlen'] at this
      unfold smax; grind
  · rw [List.sum_append]; grind

theorem root_of_cert : ∀ x, certValid x → Root x.1 x.2.1 x.2.2.1
  | (.A, _, _, _, _), h => fun _ _ hX => ⟨pack_of_cert h.1 hX, pack_of_cert h.2 hX⟩
  | (.B, _, _, _, _), h => fun _ _ hX => pack_of_cert h hX
  | (.C, _, _, _, _), h => fun _ _ hX => pack_of_cert h hX
  | (.E, _, _, _, _), h => fun _ _ hX => pack_of_cert h hX
  | (.D, _, _, _, _), h => h.elim

theorem certTable_valid : ∀ x ∈ certTable, certValid x := by
  decide +kernel

theorem settled_covered :
    ∀ r ∈ settledRoots, r = (Cond.D, 1, 1) ∨ ∃ x ∈ certTable, (x.1, x.2.1, x.2.2.1) = r := by
  decide +kernel

/-! ## The settled (D) root, uniformly over the box -/

theorem root_D_1_1 : Root .D 1 1 := by
  intro ys ys' hX γ ω0 hω1 hω2 hγ1 hγ2
  have hB1 : B 1 = 777 / 5000 := by decide +kernel
  obtain ⟨hlen, hlen', hrange, hs1, hs2⟩ := hX
  have hδ : δ = 41 / 2500 := rfl
  have hε : εa = 1 / 10000000000 := rfl
  have hω : ω11 = 7 / 1000 := by decide +kernel
  apply greedy_pack (capsD γ ω0) (ys ++ ys') (B 1) [0] (by simp) (by simp) (by simp [capsD])
  · intro k hk
    simp only [capsD, List.length_cons, List.length_nil] at hk
    rw [hω] at hω2 hγ2
    rw [hε] at hγ1 hγ2
    rw [hδ] at hγ2
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp only [capsD, List.getElem!_cons_zero, List.getElem!_cons_succ, hδ, hε] <;> grind
  · intro y hy
    rcases List.mem_append.mp hy with h | h
    · have := largest_coordinate δ (B 1) ys
        (fun z hz => (hrange z (List.mem_append_left _ hz)).1) hs1 y h
      rw [hlen] at this; grind
    · have := largest_coordinate δ (B 1) ys'
        (fun z hz => (hrange z (List.mem_append_right _ hz)).1) hs2 y h
      rw [hlen'] at this; grind
  · simp only [capsD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.getElem!_cons_zero, List.length_singleton, List.sum_append]
    rw [hB1] at hs1 hs2
    rw [hδ, hε]
    rw [hω] at hω2
    rw [hε] at hγ1
    grind

theorem lemma_7_10_settled :
    ∀ r ∈ settledRoots, Root r.1 r.2.1 r.2.2 := by
  intro r hr
  rcases settled_covered r hr with h | ⟨x, hx, hxr⟩
  · subst h; exact root_D_1_1
  · rw [← hxr]; exact root_of_cert x (certTable_valid x hx)

end BGP212.Challenge
