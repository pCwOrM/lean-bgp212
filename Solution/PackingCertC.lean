/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 7.4, Proposition 7.8 (D), Lemma 7.10 (p. 36).
-/
import Solution.PackingCert

/-! # A3c: certificate trees with profile cuts and certified empty cells

Core Lean. A3c extends A3b's checker (`Solution/PackingCert.lean`, unchanged) with a third
node kind:

* `leaf assign certs`: as in A3b; an assignment of the sorted coordinates to bins and, per
  bin, a sparse Farkas certificate for its load inequality on the cell.
* `split a b l r`: the cell is covered by `a·v ≤ b` (left) and `−a·v ≤ −b` (right). The cut
  `a` is any integer vector over all coordinates, so cuts on the profile coordinates
  (the sorted sides) and on the box coordinates `(γ, ω₀)` are both available.
* `empty lam`: an exact rational Farkas infeasibility certificate: nonnegative multipliers
  whose combination of the cell's constraints is `0·v ≤ c` with `c < 0`. Such a cell has no
  points (`emptyB_sound`), so it needs no assignment.

Leaf multipliers on cut cells come from an exact linear program (the generator re-solves the
dual support in exact rational arithmetic); the checker trusts none of the data. -/

namespace BGP212.PackingCert

open BGP212.Params BGP212.Ledger BGP212.Packing

/-! ## Empty cells -/

/-- A sparse Farkas infeasibility certificate for `cell`: nonnegative multipliers combining
the constraints into `0·v ≤ c` with `c < 0`. -/
def emptyB (N : Nat) (cell : List LinCon) (lam : List (Nat × Int × Nat)) : Bool :=
  lam.all (fun p => decide (p.1 < cell.length) && decide (0 ≤ q p.2.1 p.2.2)) &&
    decide (combVec N cell lam = List.replicate N 0) && decide (combRhs cell lam < 0)

/-- **Soundness of empty-cell detection.** A cell with a checked infeasibility certificate
contains no point. -/
theorem emptyB_sound {N : Nat} {cell : List LinCon} {lam : List (Nat × Int × Nat)}
    (h : emptyB N cell lam = true) (v : List Rat) : ¬ Sat N cell v := by
  intro hs
  simp only [emptyB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hall, hvec⟩, hneg⟩ := h
  have := farkas_core N cell v hs lam (fun p hp => hall p hp)
  rw [hvec, dot_zeros] at this
  grind

/-! ## Trees with empty cells -/

/-- A3c certificate tree. Rationals in the data are `(numerator, denominator)` pairs. -/
inductive Tree2
  | leaf (assign : List Nat) (certs : List (List (Nat × Int × Nat)))
  | split (a : List Int) (bn : Int) (bd : Nat) (l r : Tree2)
  | empty (lam : List (Nat × Int × Nat))

def checkTree2 (n N : Nat) (cd : CapData) : List LinCon → Tree2 → Bool
  | cell, .leaf assign certs => leafB n N cd cell assign certs
  | cell, .split a bn bd l r =>
      decide (a.length = N) &&
        checkTree2 n N cd (cell ++ [(a.map (fun x : Int => (x : Rat)), q bn bd)]) l &&
        checkTree2 n N cd (cell ++ [negCon (a.map (fun x : Int => (x : Rat)), q bn bd)]) r
  | cell, .empty lam => emptyB N cell lam

/-- **Soundness of the A3c checker**, for any capacity data: a checked tree yields a valid
assignment at every point of its cell. -/
theorem checkTree2_sound (n N : Nat) (cd : CapData) :
    ∀ (t : Tree2) (cell : List LinCon) (v : List Rat), checkTree2 n N cd cell t = true →
      Sat N cell v → Good n cd v
  | .leaf assign certs, cell, v, h, hs => by
      simp only [checkTree2, leafB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range] at h
      obtain ⟨⟨⟨hlen, hin⟩, _⟩, hk⟩ := h
      exact ⟨assign, hlen, hin, fun k hk' => farkasB_sound hs (hk k hk')⟩
  | .empty lam, cell, v, h, hs => absurd hs (emptyB_sound h v)
  | .split a bn bd l r, cell, v, h, hs => by
      simp only [checkTree2, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hal, hl⟩, hr⟩ := h
      by_cases hc : dot (a.map (fun x : Int => (x : Rat))) v ≤ q bn bd
      · apply checkTree2_sound n N cd l _ v hl
        intro c hc'
        rcases List.mem_append.mp hc' with h1 | h1
        · exact hs c h1
        · simp only [List.mem_singleton] at h1; subst h1; simp [hal, hc]
      · apply checkTree2_sound n N cd r _ v hr
        intro c hc'
        rcases List.mem_append.mp hc' with h1 | h1
        · exact hs c h1
        · simp only [List.mem_singleton] at h1; subst h1
          simp only [negCon, List.length_map, hal, true_and]
          rw [List.map_map, show ((- ·) ∘ fun x : Int => (x : Rat)) =
              (fun y : Rat => -y) ∘ (fun x : Int => (x : Rat)) from rfl, ← List.map_map,
            dot_neg]
          grind

/-- Every A3b tree is an A3c tree with the same verdict. -/
def Tree.toTree2 : Tree → Tree2
  | .leaf assign certs => .leaf assign certs
  | .split a bn bd l r => .split a bn bd l.toTree2 r.toTree2

theorem checkTree2_toTree2 (n N : Nat) (cd : CapData) :
    ∀ (t : Tree) (cell : List LinCon), checkTree2 n N cd cell t.toTree2 = checkTree n N cd cell t
  | .leaf _ _, _ => rfl
  | .split a bn bd l r, cell => by
      simp only [Tree.toTree2, checkTree2, checkTree, checkTree2_toTree2 n N cd l,
        checkTree2_toTree2 n N cd r]

/-! ## Checking a tree in pieces

Kernel memory grows with the size of a single `decide`. A large tree is therefore checked one
piece at a time: each subtree is checked on its own cell, written as the base cell plus the
cuts on the path to it, and `checkTree2_split_path` assembles the pieces. -/

/-- A cut on a path: `(a, bn, bd, true)` is the side `a·v ≤ bn/bd`, `(a, bn, bd, false)` the
side `−a·v ≤ −bn/bd`. -/
abbrev Cut := List Int × Int × Nat × Bool

def cutCon : Cut → LinCon
  | (a, bn, bd, true) => (a.map (fun x : Int => (x : Rat)), q bn bd)
  | (a, bn, bd, false) => negCon (a.map (fun x : Int => (x : Rat)), q bn bd)

/-- The cell reached from `base` along `path`. -/
def pathCell (base : List LinCon) (path : List Cut) : List LinCon := base ++ path.map cutCon

theorem pathCell_snoc (base : List LinCon) (path : List Cut) (c : Cut) :
    pathCell base (path ++ [c]) = pathCell base path ++ [cutCon c] := by
  simp [pathCell]

theorem checkTree2_split_path {n N : Nat} {cd : CapData} {base : List LinCon}
    {path : List Cut} {a : List Int} {bn : Int} {bd : Nat} {l r : Tree2}
    (ha : a.length = N)
    (hl : checkTree2 n N cd (pathCell base (path ++ [(a, bn, bd, true)])) l = true)
    (hr : checkTree2 n N cd (pathCell base (path ++ [(a, bn, bd, false)])) r = true) :
    checkTree2 n N cd (pathCell base path) (.split a bn bd l r) = true := by
  rw [pathCell_snoc] at hl hr
  simp only [checkTree2, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨ha, hl⟩, hr⟩

/-! ## Condition (D) -/

theorem packs_of_tree2_D (m m' : Nat) (hm : 1 ≤ m) (hm' : 1 ≤ m') (t : Tree2)
    (h : checkTree2 (m + m') (m + m' + 2) cdD (baseCell m m' 2) t = true)
    (ys ys' : List Rat) (hX : InXi (B m) (B m') m m' ys ys') (γ ω0 : Rat) (hb : InBox γ ω0) :
    Packs (capsD γ ω0) (ys ++ ys') := by
  have hs := baseCell_sat m m' 2 hm hm' ys ys' [γ, ω0] hX rfl (fun _ => ⟨γ, ω0, rfl, hb⟩)
  have hg := checkTree2_sound (m + m') (m + m' + 2) cdD t _ _ h hs
  have hL1 : (sortDesc ys).length = m := by rw [(sortDesc_perm ys).length_eq, hX.1]
  have hL2 : (sortDesc ys').length = m' := by rw [(sortDesc_perm ys').length_eq, hX.2.1]
  have hp : Packs (capsD γ ω0) (sortDesc ys ++ sortDesc ys') :=
    packs_of_good (by simp [hL1, hL2]) (by simp [capsD, cdD]) (capsD_eq γ ω0) hg
  exact packs_perm' ((sortDesc_perm ys).append (sortDesc_perm ys')) hp

/-- An A3c certificate row for condition (D): `m`, `m′`, and the tree. -/
abbrev CertRowC := Nat × Nat × Tree2

def rowC : CertRowC → Bool
  | (m, m', t) => decide (1 ≤ m) && decide (1 ≤ m') &&
      checkTree2 (m + m') (m + m' + 2) cdD (baseCell m m' 2) t

theorem rowC_intro {m m' : Nat} {t : Tree2} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : checkTree2 (m + m') (m + m' + 2) cdD (pathCell (baseCell m m' 2) []) t = true) :
    rowC (m, m', t) = true := by
  simp only [pathCell, List.map_nil, List.append_nil] at h
  simp [rowC, hm, hm', h]

theorem rowC_sound : ∀ x : CertRowC, rowC x = true → Root .D x.1 x.2.1
  | (m, m', t), h => by
      simp only [rowC, Bool.and_eq_true, decide_eq_true_eq] at h
      intro ys ys' hX γ ω0 h1 h2 h3 h4
      exact packs_of_tree2_D m m' h.1.1 h.1.2 t h.2 ys ys' hX γ ω0 ⟨h1, h2, h3, h4⟩

/-! ## A certified empty cell

The cut `y₁ ≥ 1/2` on the (D, 1, 3) base cell meets the side bound `y₁ ≤ B₁,₁ = 777/5000`:
multipliers `1` on the cut (constraint 10) and `1` on the side-1 sum bound (constraint 1)
combine to `0·v ≤ 777/5000 − 1/2 < 0`. The checker accepts the cell as empty, with no
assignment. (The 43 trees of A3c need no empty cells: every cut the generator makes passes
through points of its cell.) -/

theorem empty_cell_example :
    checkTree2 4 6 cdD (pathCell (baseCell 1 3 2) [([-1, 0, 0, 0, 0, 0], -1, 2, true)])
      (.empty [(1, 1, 1), (10, 1, 1)]) = true := by
  decide +kernel

end BGP212.PackingCert
