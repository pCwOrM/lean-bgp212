/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 7.4, Proposition 7.8 (A)–(E), Lemma 7.10 (p. 36).
-/
import Solution.Packing

/-! # A3b: the certificate checker and its soundness

Core Lean. A certificate is a subdivision tree over a cell of linear constraints.

* Coordinates: `v = sort↓(side 1) ++ sort↓(side 2) ++ extras`, with `extras = [γ, ω₀]` for
  condition (D) and `[]` otherwise.
* `baseCell`: each side sorted decreasingly, its last coordinate at least `δ`, its sum at most
  `B₁,ₘ`; for (D) also the full `(γ, ω₀)` box of Proposition 7.8.
* `split a b l r` covers its cell by `a·v ≤ b` (left) and `−a·v ≤ −b` (right).
* A leaf gives an assignment of the sorted coordinates to bins and, per bin, a sparse Farkas
  certificate: nonnegative multipliers on the cell's constraints whose combination is exactly
  the bin's load inequality.

`checkTree_sound` proves that a checked tree yields a valid assignment at every point of its
cell; nothing in the certificate data is trusted. -/

namespace BGP212.PackingCert

open BGP212.Params BGP212.Ledger BGP212.Packing

/-! ## Linear algebra on lists -/

def dot : List Rat → List Rat → Rat
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

theorem dot_nil_left (v : List Rat) : dot [] v = 0 := by cases v <;> rfl

theorem dot_cons_cons (x y : Rat) (xs ys : List Rat) : dot (x :: xs) (y :: ys) = x * y + dot xs ys :=
  rfl

theorem dot_add : ∀ (a b v : List Rat), a.length = b.length →
    dot (List.zipWith (· + ·) a b) v = dot a v + dot b v
  | [], [], v, _ => by simp [dot_nil_left] <;> grind
  | x :: xs, y :: ys, [], _ => by simp [dot] <;> grind
  | x :: xs, y :: ys, z :: zs, h => by
      simp only [List.zipWith_cons_cons, dot_cons_cons]
      rw [dot_add xs ys zs (by simpa using h)]
      grind
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem dot_scale (l : Rat) : ∀ (a v : List Rat), dot (a.map (l * ·)) v = l * dot a v
  | [], v => by simp [dot_nil_left] <;> grind
  | x :: xs, [] => by simp [dot] <;> grind
  | x :: xs, y :: ys => by
      simp only [List.map_cons, dot_cons_cons]
      rw [dot_scale l xs ys]
      grind

theorem dot_neg : ∀ (a v : List Rat), dot (a.map (- ·)) v = - dot a v
  | [], v => by simp [dot_nil_left] <;> grind
  | x :: xs, [] => by simp [dot] <;> grind
  | x :: xs, y :: ys => by
      simp only [List.map_cons, dot_cons_cons]
      rw [dot_neg xs ys]
      grind

theorem dot_zeros : ∀ (N : Nat) (v : List Rat), dot (List.replicate N 0) v = 0
  | 0, v => dot_nil_left v
  | N + 1, [] => rfl
  | N + 1, y :: ys => by
      simp only [List.replicate_succ, dot_cons_cons]
      rw [dot_zeros N ys]
      grind

theorem dot_append : ∀ (a b x y : List Rat), a.length = x.length →
    dot (a ++ b) (x ++ y) = dot a x + dot b y
  | [], b, [], y, _ => by simp [dot_nil_left] <;> grind
  | p :: ps, b, q :: qs, y, h => by
      simp only [List.cons_append, dot_cons_cons]
      rw [dot_append ps b qs y (by simpa using h)]
      grind
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

theorem dot_ones : ∀ (l : List Rat), dot (List.replicate l.length 1) l = l.sum
  | [] => rfl
  | y :: ys => by
      simp only [List.length_cons, List.replicate_succ, dot_cons_cons, List.sum_cons]
      rw [dot_ones ys]
      grind

/-! ## Constraints, Farkas certificates, trees -/

/-- A linear constraint `a·v ≤ b`. -/
abbrev LinCon := List Rat × Rat

def negCon (c : LinCon) : LinCon := (c.1.map (- ·), - c.2)

/-- A rational from certificate data: numerator over denominator. -/
def q (n : Int) (d : Nat) : Rat := (n : Rat) / (d : Rat)

def combVec (N : Nat) (cell : List LinCon) : List (Nat × Int × Nat) → List Rat
  | [] => List.replicate N 0
  | (j, n, d) :: rest =>
      List.zipWith (· + ·) ((cell[j]!).1.map (q n d * ·)) (combVec N cell rest)

def combRhs (cell : List LinCon) : List (Nat × Int × Nat) → Rat
  | [] => 0
  | (j, n, d) :: rest => q n d * (cell[j]!).2 + combRhs cell rest

/-- A sparse Farkas certificate for `target·v ≤ rhs` on `cell`. -/
def farkasB (N : Nat) (cell : List LinCon) (lam : List (Nat × Int × Nat))
    (target : List Rat) (rhs : Rat) : Bool :=
  lam.all (fun p => decide (p.1 < cell.length) && decide (0 ≤ q p.2.1 p.2.2)) &&
    decide (combVec N cell lam = target) && decide (combRhs cell lam ≤ rhs)

/-- The load indicator of bin `k`. -/
def indicator (assign : List Nat) (k : Nat) : List Rat :=
  assign.map fun a => if a = k then 1 else 0

/-- A certificate tree. Rationals in the data are `(numerator, denominator)` pairs. -/
inductive Tree
  | leaf (assign : List Nat) (certs : List (List (Nat × Int × Nat)))
  | split (a : List Int) (bn : Int) (bd : Nat) (l r : Tree)

/-- Bin data: for bin `k`, `(extraT k, c k)` with `cap k = c k − extraT k · extras`. -/
abbrev CapData := List (List Rat × Rat)

def leafB (n N : Nat) (cd : CapData) (cell : List LinCon) (assign : List Nat)
    (certs : List (List (Nat × Int × Nat))) : Bool :=
  decide (assign.length = n) && assign.all (fun a => decide (a < cd.length)) &&
    decide (certs.length = cd.length) &&
    (List.range cd.length).all fun k =>
      farkasB N cell (certs[k]!) (indicator assign k ++ (cd[k]!).1) (cd[k]!).2

def checkTree (n N : Nat) (cd : CapData) : List LinCon → Tree → Bool
  | cell, .leaf assign certs => leafB n N cd cell assign certs
  | cell, .split a bn bd l r =>
      decide (a.length = N) &&
        checkTree n N cd (cell ++ [(a.map (fun x : Int => (x : Rat)), q bn bd)]) l &&
        checkTree n N cd (cell ++ [negCon (a.map (fun x : Int => (x : Rat)), q bn bd)]) r

/-- `v` satisfies every constraint of `cell`, each of length `N`. -/
def Sat (N : Nat) (cell : List LinCon) (v : List Rat) : Prop :=
  ∀ c ∈ cell, c.1.length = N ∧ dot c.1 v ≤ c.2

/-! ## Soundness -/

theorem combVec_length (N : Nat) (cell : List LinCon) (hl : ∀ c ∈ cell, c.1.length = N) :
    ∀ lam : List (Nat × Int × Nat), (∀ p ∈ lam, p.1 < cell.length) →
      (combVec N cell lam).length = N
  | [], _ => by simp [combVec]
  | (j, n, d) :: rest, h => by
      have hj := h (j, n, d) (by simp)
      have hmem : cell[j]! ∈ cell := by
        rw [getElem!_pos cell j hj]; exact List.getElem_mem hj
      simp only [combVec, List.length_zipWith, List.length_map, hl _ hmem]
      rw [combVec_length N cell hl rest (fun p hp => h p (by simp [hp]))]
      omega

theorem farkas_core (N : Nat) (cell : List LinCon) (v : List Rat) (hs : Sat N cell v) :
    ∀ lam : List (Nat × Int × Nat), (∀ p ∈ lam, p.1 < cell.length ∧ 0 ≤ q p.2.1 p.2.2) →
      dot (combVec N cell lam) v ≤ combRhs cell lam
  | [], _ => by simp [combVec, combRhs, dot_zeros] <;> grind
  | (j, n, d) :: rest, h => by
      have hj := h (j, n, d) (by simp)
      have hmem : cell[j]! ∈ cell := by
        rw [getElem!_pos cell j hj.1]; exact List.getElem_mem hj.1
      have hc := hs _ hmem
      have hlen : ((cell[j]!).1.map (q n d * ·)).length = (combVec N cell rest).length := by
        rw [List.length_map, hc.1, combVec_length N cell (fun c hc' => (hs c hc').1) rest
          (fun p hp => (h p (by simp [hp])).1)]
      simp only [combVec, combRhs]
      rw [dot_add _ _ _ hlen, dot_scale]
      have ih := farkas_core N cell v hs rest (fun p hp => h p (by simp [hp]))
      have hmul : q n d * dot (cell[j]!).1 v ≤ q n d * (cell[j]!).2 :=
        Rat.mul_le_mul_of_nonneg_left hc.2 hj.2
      grind

theorem farkasB_sound {N : Nat} {cell : List LinCon} {v : List Rat} (hs : Sat N cell v)
    {lam : List (Nat × Int × Nat)} {target : List Rat} {rhs : Rat}
    (h : farkasB N cell lam target rhs = true) : dot target v ≤ rhs := by
  simp only [farkasB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hall, hvec⟩, hrhs⟩ := h
  have := farkas_core N cell v hs lam (fun p hp => hall p hp)
  rw [hvec] at this
  grind

/-- What a checked tree delivers at a point: an assignment within every bin's capacity. -/
def Good (n : Nat) (cd : CapData) (v : List Rat) : Prop :=
  ∃ assign : List Nat, assign.length = n ∧ (∀ a ∈ assign, a < cd.length) ∧
    ∀ k, k < cd.length → dot (indicator assign k ++ (cd[k]!).1) v ≤ (cd[k]!).2

theorem checkTree_sound (n N : Nat) (cd : CapData) :
    ∀ (t : Tree) (cell : List LinCon) (v : List Rat), checkTree n N cd cell t = true →
      Sat N cell v → Good n cd v
  | .leaf assign certs, cell, v, h, hs => by
      simp only [checkTree, leafB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range] at h
      obtain ⟨⟨⟨hlen, hin⟩, _⟩, hk⟩ := h
      exact ⟨assign, hlen, hin, fun k hk' => farkasB_sound hs (hk k hk')⟩
  | .split a bn bd l r, cell, v, h, hs => by
      simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hal, hl⟩, hr⟩ := h
      by_cases hc : dot (a.map (fun x : Int => (x : Rat))) v ≤ q bn bd
      · apply checkTree_sound n N cd l _ v hl
        intro c hc'
        rcases List.mem_append.mp hc' with h1 | h1
        · exact hs c h1
        · simp only [List.mem_singleton] at h1; subst h1; simp [hal, hc]
      · apply checkTree_sound n N cd r _ v hr
        intro c hc'
        rcases List.mem_append.mp hc' with h1 | h1
        · exact hs c h1
        · simp only [List.mem_singleton] at h1; subst h1
          simp only [negCon, List.length_map, hal, true_and]
          rw [List.map_map, show ((- ·) ∘ fun x : Int => (x : Rat)) =
              (fun y : Rat => -y) ∘ (fun x : Int => (x : Rat)) from rfl, ← List.map_map,
            dot_neg]
          grind

/-! ## From dot products to bin loads -/

theorem dot_indicator : ∀ (items : List Rat) (assign : List Nat) (k : Nat),
    assign.length = items.length → dot (indicator assign k) items = binSum items assign k
  | [], [], k, _ => by simp [indicator, dot_nil_left, binSum_nil_left]
  | y :: ys, a :: as, k, h => by
      simp only [indicator, List.map_cons, dot_cons_cons, binSum_cons]
      have := dot_indicator ys as k (by simpa using h)
      simp only [indicator] at this
      rw [this]
      by_cases hak : a = k <;> simp [hak] <;> grind
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-! ## The sorted base cell -/

def adjCons : Nat → List LinCon
  | 0 => []
  | 1 => []
  | m + 2 => ((-1) :: 1 :: List.replicate m 0, 0) :: (adjCons (m + 1)).map fun c => (0 :: c.1, c.2)

def lowerVec : Nat → List Rat
  | 0 => []
  | 1 => [-1]
  | m + 2 => 0 :: lowerVec (m + 1)

/-- One sorted side of `m` coordinates with sum at most `Bm`. -/
def sideCons (m : Nat) (Bm : Rat) : List LinCon :=
  adjCons m ++ [(lowerVec m, -δ), (List.replicate m 1, Bm)]

def pad (pre post : Nat) (c : LinCon) : LinCon :=
  (List.replicate pre 0 ++ c.1 ++ List.replicate post 0, c.2)

/-- The `(γ, ω₀)` box of Proposition 7.8 (D) on the two extra coordinates. -/
def boxCons (n : Nat) : List LinCon :=
  [ (List.replicate n 0 ++ [-1, 0], -(2 / 5 - εa)),
    (List.replicate n 0 ++ [1, 0], 1 / 3 + 8 * ω11 + 7 * δ / 3 + 3 * εa),
    (List.replicate n 0 ++ [0, -1], 0),
    (List.replicate n 0 ++ [0, 1], ω11) ]

def baseCell (m m' extra : Nat) : List LinCon :=
  (sideCons m (B m)).map (pad 0 (m' + extra)) ++ (sideCons m' (B m')).map (pad m extra) ++
    (if extra = 2 then boxCons (m + m') else [])

/-- Sorted decreasingly. -/
def SortedDesc (l : List Rat) : Prop := List.Pairwise (fun a b => b ≤ a) l

theorem adjCons_sound : ∀ (l : List Rat), SortedDesc l →
    ∀ c ∈ adjCons l.length, c.1.length = l.length ∧ dot c.1 l ≤ c.2
  | [], _ => by simp [adjCons]
  | [_], _ => by simp [adjCons]
  | x :: y :: rest, hs => by
      intro c hc
      simp only [List.length_cons, adjCons, List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨c0, hc0, rfl⟩
      · have hxy : y ≤ x := (List.pairwise_cons.mp hs).1 y (by simp)
        simp only [List.length_cons, List.length_replicate, dot_cons_cons, dot_zeros, true_and]
        grind
      · have ih := adjCons_sound (y :: rest) (List.Pairwise.of_cons hs) c0
          (by simpa using hc0)
        simp only [List.length_cons] at ih ⊢
        refine ⟨by omega, ?_⟩
        rw [dot_cons_cons]
        grind

theorem lowerVec_dot : ∀ (l : List Rat) (x : Rat), dot (lowerVec (l ++ [x]).length) (l ++ [x]) = -x
  | [], x => by simp [lowerVec, dot]; grind
  | [y], x => by simp [lowerVec, dot]; grind
  | y :: z :: rest, x => by
      have := lowerVec_dot (z :: rest) x
      simp only [List.cons_append, List.length_cons] at this ⊢
      simp only [lowerVec, dot_cons_cons]
      rw [this]; grind

theorem lowerVec_length : ∀ m, (lowerVec m).length = m
  | 0 => rfl
  | 1 => rfl
  | m + 2 => by simp [lowerVec, lowerVec_length (m + 1)]

theorem sideCons_sound (l : List Rat) (Bm : Rat) (hs : SortedDesc l) (hne : l ≠ [])
    (hlast : δ ≤ l.getLast hne) (hsum : l.sum ≤ Bm) :
    ∀ c ∈ sideCons l.length Bm, c.1.length = l.length ∧ dot c.1 l ≤ c.2 := by
  intro c hc
  simp only [sideCons, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with h | rfl | rfl
  · exact adjCons_sound l hs c h
  · refine ⟨lowerVec_length _, ?_⟩
    have hl := List.dropLast_concat_getLast hne
    have := lowerVec_dot l.dropLast (l.getLast hne)
    rw [hl] at this
    simp only
    rw [this]; grind
  · exact ⟨by simp, by simp only; rw [dot_ones]; exact hsum⟩

theorem pad_sound (pre post : Nat) (c : LinCon) (A X C : List Rat) (hA : A.length = pre)
    (_hC : C.length = post) (hX : c.1.length = X.length) :
    (pad pre post c).1.length = pre + X.length + post ∧
      dot (pad pre post c).1 (A ++ X ++ C) = dot c.1 X := by
  refine ⟨by simp [pad, hX]; omega, ?_⟩
  simp only [pad]
  rw [dot_append _ _ _ _ (by simp [hX]; omega), dot_append _ _ _ _ (by simp; omega), dot_zeros,
    dot_zeros]
  grind

/-! ## Permutation invariance of packing -/

theorem binSum_perm_exists {l l' : List Rat} (hp : l.Perm l') :
    ∀ as : List Nat, as.length = l.length →
      ∃ as' : List Nat, as'.length = l'.length ∧ as'.Perm as ∧
        ∀ k, binSum l' as' k = binSum l as k := by
  induction hp with
  | nil => intro as h; exact ⟨as, h, List.Perm.refl _, fun _ => rfl⟩
  | cons x _ ih =>
      intro as h
      match as, h with
      | a :: as0, h' =>
          obtain ⟨as0', h1, h2, h3⟩ := ih as0 (by simpa using h')
          exact ⟨a :: as0', by simpa using h1, h2.cons a, fun k => by simp [binSum_cons, h3]⟩
      | [], h' => simp at h'
  | swap x y l =>
      intro as h
      match as, h with
      | a :: b :: as0, h' =>
          refine ⟨b :: a :: as0, by simpa using h', List.Perm.swap a b as0, fun k => ?_⟩
          simp only [binSum_cons]; grind
      | [], h' => simp at h'
      | [_], h' => simp at h'
  | trans _ _ ih1 ih2 =>
      intro as h
      obtain ⟨as1, h1, h2, h3⟩ := ih1 as h
      obtain ⟨as2, h4, h5, h6⟩ := ih2 as1 h1
      exact ⟨as2, h4, h5.trans h2, fun k => (h6 k).trans (h3 k)⟩

theorem packs_perm' {caps items items' : List Rat} (hp : items.Perm items')
    (h : Packs caps items) : Packs caps items' := by
  obtain ⟨as, hlen, hin, hb⟩ := h
  obtain ⟨as', h1, h2, h3⟩ := binSum_perm_exists hp as hlen
  exact ⟨as', h1, fun a ha => hin a (h2.subset ha), fun k hk => by rw [h3 k]; exact hb k hk⟩

/-! ## Sorting a side and placing a profile in the base cell -/

def sortDesc (l : List Rat) : List Rat := l.mergeSort (fun a b => decide (b ≤ a))

theorem sortDesc_perm (l : List Rat) : (sortDesc l).Perm l := List.mergeSort_perm _ _

theorem sortDesc_sorted (l : List Rat) : SortedDesc (sortDesc l) := by
  have h := List.pairwise_mergeSort (le := fun a b : Rat => decide (b ≤ a))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; grind)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; grind) l
  exact h.imp (fun hab => by simpa using hab)

theorem side_sat (l : List Rat) (Bm : Rat) (m : Nat) (hm : 1 ≤ m) (hlen : l.length = m)
    (hδ : ∀ y ∈ l, δ ≤ y) (hsum : l.sum ≤ Bm) :
    ∀ c ∈ sideCons m Bm, c.1.length = m ∧ dot c.1 (sortDesc l) ≤ c.2 := by
  have hp := sortDesc_perm l
  have hlen' : (sortDesc l).length = m := by rw [hp.length_eq, hlen]
  have hne : sortDesc l ≠ [] := by
    intro h; rw [h] at hlen'; simp at hlen'; omega
  have hsum' : (sortDesc l).sum ≤ Bm := by rw [BGP212.Challenge.perm_sum' hp]; exact hsum
  have hlast : δ ≤ (sortDesc l).getLast hne :=
    hδ _ (hp.subset (List.getLast_mem hne))
  have := sideCons_sound (sortDesc l) Bm (sortDesc_sorted l) hne hlast hsum'
  rw [hlen'] at this
  intro c hc
  have h2 := this c hc
  exact ⟨h2.1, h2.2⟩

/-- The box of Proposition 7.8 (D). -/
def InBox (γ ω0 : Rat) : Prop :=
  0 ≤ ω0 ∧ ω0 ≤ ω11 ∧ 2 / 5 - εa ≤ γ ∧ γ ≤ 1 / 3 + 8 * ω11 + 7 * δ / 3 + 3 * εa

theorem baseCell_sat (m m' extra : Nat) (hm : 1 ≤ m) (hm' : 1 ≤ m') (ys ys' extras : List Rat)
    (hX : InXi (B m) (B m') m m' ys ys') (hex : extras.length = extra)
    (hbox : extra = 2 → ∃ γ ω0, extras = [γ, ω0] ∧ InBox γ ω0) :
    Sat (m + m' + extra) (baseCell m m' extra) (sortDesc ys ++ sortDesc ys' ++ extras) := by
  obtain ⟨hl, hl', hr, hs, hs'⟩ := hX
  have h1 := side_sat ys (B m) m hm hl (fun y hy => (hr y (List.mem_append_left _ hy)).1) hs
  have h2 := side_sat ys' (B m') m' hm' hl' (fun y hy => (hr y (List.mem_append_right _ hy)).1) hs'
  have hL1 : (sortDesc ys).length = m := by rw [(sortDesc_perm ys).length_eq, hl]
  have hL2 : (sortDesc ys').length = m' := by rw [(sortDesc_perm ys').length_eq, hl']
  intro c hc
  simp only [baseCell, List.mem_append, List.mem_map] at hc
  rcases hc with (⟨c0, hc0, rfl⟩ | ⟨c0, hc0, rfl⟩) | hcb
  · have hc1 := h1 c0 hc0
    have := pad_sound 0 (m' + extra) c0 [] (sortDesc ys) (sortDesc ys' ++ extras) rfl
      (by simp [hL2, hex]) (by rw [hc1.1, hL1])
    rw [List.nil_append] at this
    rw [List.append_assoc]
    refine ⟨by rw [this.1]; omega, by rw [this.2]; exact hc1.2⟩
  · have hc2 := h2 c0 hc0
    have := pad_sound m extra c0 (sortDesc ys) (sortDesc ys') extras hL1 hex (by rw [hc2.1, hL2])
    refine ⟨by rw [this.1]; omega, by rw [this.2]; exact hc2.2⟩
  · by_cases he : extra = 2
    · obtain ⟨γ, ω0, rfl, hb⟩ := hbox he
      simp only [he, ite_true, boxCons, List.mem_cons, List.mem_nil_iff, or_false] at hcb
      have hn : (sortDesc ys ++ sortDesc ys').length = m + m' := by simp [hL1, hL2]
      have key : ∀ (x : List Rat), x.length = 2 →
          dot (List.replicate (m + m') 0 ++ x) (sortDesc ys ++ sortDesc ys' ++ [γ, ω0]) =
            dot x [γ, ω0] := by
        intro x _
        rw [dot_append _ _ _ _ (by simp [hn]), dot_zeros]; grind
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
      rcases hcb with rfl | rfl | rfl | rfl <;>
        refine ⟨by simp; omega, ?_⟩ <;> rw [key _ (by rfl)] <;> simp [dot] <;> grind
    · simp [he] at hcb

/-! ## From a checked tree to packing -/

/-- Capacity data for a constant-capacity condition. -/
def cdConst (caps : List Rat) : CapData := caps.map fun c => ([], c)

/-- Capacity data for (D): `capsD γ ω₀ = c − extraT · [γ, ω₀]` bin by bin. -/
def cdD : CapData :=
  [([-1, 8], -2 * δ - εa), ([1, 2], 1 / 2 - εa), ([0, -4], δ - εa), ([0, -8], 0)]

theorem packs_of_good {n : Nat} {cd : CapData} {items extras caps : List Rat}
    (hn : items.length = n) (hcl : caps.length = cd.length)
    (hcap : ∀ k, k < cd.length → caps[k]! = (cd[k]!).2 - dot (cd[k]!).1 extras)
    (hg : Good n cd (items ++ extras)) : Packs caps items := by
  obtain ⟨assign, hlen, hin, hk⟩ := hg
  refine ⟨assign, by rw [hlen, hn], fun a ha => by rw [hcl]; exact hin a ha, fun k hk' => ?_⟩
  rw [hcl] at hk'
  have h := hk k hk'
  rw [dot_append _ _ _ _ (by simp [indicator, hlen, hn]),
    dot_indicator items assign k (by rw [hlen, hn])] at h
  rw [hcap k hk']
  grind

theorem packs_of_tree_const (caps : List Rat) (m m' : Nat) (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (t : Tree) (h : checkTree (m + m') (m + m' + 0) (cdConst caps) (baseCell m m' 0) t = true)
    (ys ys' : List Rat) (hX : InXi (B m) (B m') m m' ys ys') : Packs caps (ys ++ ys') := by
  have hs := baseCell_sat m m' 0 hm hm' ys ys' [] hX rfl (by intro h; omega)
  have hg := checkTree_sound (m + m') (m + m' + 0) (cdConst caps) t _ _ h hs
  have hL1 : (sortDesc ys).length = m := by rw [(sortDesc_perm ys).length_eq, hX.1]
  have hL2 : (sortDesc ys').length = m' := by rw [(sortDesc_perm ys').length_eq, hX.2.1]
  have hp : Packs caps (sortDesc ys ++ sortDesc ys') :=
    packs_of_good (by simp [hL1, hL2]) (by simp [cdConst])
      (fun k hk => by simp [cdConst] at hk ⊢; simp [hk, dot_nil_left]; grind) hg
  exact packs_perm' ((sortDesc_perm ys).append (sortDesc_perm ys')) hp

theorem capsD_eq (γ ω0 : Rat) :
    ∀ k, k < cdD.length → (capsD γ ω0)[k]! = (cdD[k]!).2 - dot (cdD[k]!).1 [γ, ω0] := by
  intro k hk
  simp only [cdD, List.length_cons, List.length_nil] at hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp [capsD, cdD, dot] <;> grind

theorem packs_of_tree_D (m m' : Nat) (hm : 1 ≤ m) (hm' : 1 ≤ m') (t : Tree)
    (h : checkTree (m + m') (m + m' + 2) cdD (baseCell m m' 2) t = true)
    (ys ys' : List Rat) (hX : InXi (B m) (B m') m m' ys ys') (γ ω0 : Rat) (hb : InBox γ ω0) :
    Packs (capsD γ ω0) (ys ++ ys') := by
  have hs := baseCell_sat m m' 2 hm hm' ys ys' [γ, ω0] hX rfl (fun _ => ⟨γ, ω0, rfl, hb⟩)
  have hg := checkTree_sound (m + m') (m + m' + 2) cdD t _ _ h hs
  have hL1 : (sortDesc ys).length = m := by rw [(sortDesc_perm ys).length_eq, hX.1]
  have hL2 : (sortDesc ys').length = m' := by rw [(sortDesc_perm ys').length_eq, hX.2.1]
  have hp : Packs (capsD γ ω0) (sortDesc ys ++ sortDesc ys') :=
    packs_of_good (by simp [hL1, hL2]) (by simp [capsD, cdD]) (capsD_eq γ ω0) hg
  exact packs_perm' ((sortDesc_perm ys).append (sortDesc_perm ys')) hp

/-! ## Certificate rows -/

/-- A certificate row: condition, `m`, `m′`, and its trees ((A) has one per partition). -/
abbrev CertRow := Cond × Nat × Nat × List Tree

def rowB : CertRow → Bool
  | (.A, m, m', [t1, t2]) => decide (1 ≤ m) && decide (1 ≤ m') &&
      checkTree (m + m') (m + m' + 0) (cdConst capsA1) (baseCell m m' 0) t1 &&
      checkTree (m + m') (m + m' + 0) (cdConst capsA2) (baseCell m m' 0) t2
  | (.B, m, m', [t]) => decide (1 ≤ m) && decide (1 ≤ m') &&
      checkTree (m + m') (m + m' + 0) (cdConst capsB) (baseCell m m' 0) t
  | (.C, m, m', [t]) => decide (1 ≤ m) && decide (1 ≤ m') &&
      checkTree (m + m') (m + m' + 0) (cdConst capsC) (baseCell m m' 0) t
  | (.E, m, m', [t]) => decide (1 ≤ m) && decide (1 ≤ m') &&
      checkTree (m + m') (m + m' + 0) (cdConst capsE) (baseCell m m' 0) t
  | (.D, m, m', [t]) => decide (1 ≤ m) && decide (1 ≤ m') &&
      checkTree (m + m') (m + m' + 2) cdD (baseCell m m' 2) t
  | _ => false

theorem rowB_sound : ∀ x : CertRow, rowB x = true → Root x.1 x.2.1 x.2.2.1
  | (.A, m, m', [t1, t2]), h => by
      simp only [rowB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hm, hm'⟩, h1⟩, h2⟩ := h
      exact fun ys ys' hX => ⟨packs_of_tree_const _ m m' hm hm' t1 h1 ys ys' hX,
        packs_of_tree_const _ m m' hm hm' t2 h2 ys ys' hX⟩
  | (.B, m, m', [t]), h => by
      simp only [rowB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact fun ys ys' hX => packs_of_tree_const _ m m' h.1.1 h.1.2 t h.2 ys ys' hX
  | (.C, m, m', [t]), h => by
      simp only [rowB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact fun ys ys' hX => packs_of_tree_const _ m m' h.1.1 h.1.2 t h.2 ys ys' hX
  | (.E, m, m', [t]), h => by
      simp only [rowB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact fun ys ys' hX => packs_of_tree_const _ m m' h.1.1 h.1.2 t h.2 ys ys' hX
  | (.D, m, m', [t]), h => by
      simp only [rowB, Bool.and_eq_true, decide_eq_true_eq] at h
      intro ys ys' hX γ ω0 h1 h2 h3 h4
      exact packs_of_tree_D m m' h.1.1 h.1.2 t h.2 ys ys' hX γ ω0 ⟨h1, h2, h3, h4⟩
  | (.A, _, _, []), h | (.A, _, _, [_]), h | (.A, _, _, _ :: _ :: _ :: _), h
  | (.B, _, _, []), h | (.B, _, _, _ :: _ :: _), h
  | (.C, _, _, []), h | (.C, _, _, _ :: _ :: _), h
  | (.E, _, _, []), h | (.E, _, _, _ :: _ :: _), h
  | (.D, _, _, []), h | (.D, _, _, _ :: _ :: _), h => by simp [rowB] at h

end BGP212.PackingCert

namespace BGP212.Challenge

open BGP212.Packing BGP212.PackingCert

theorem packs_perm {caps items items' : List Rat} (hp : items.Perm items')
    (h : Packs caps items) : Packs caps items' :=
  packs_perm' hp h

end BGP212.Challenge
