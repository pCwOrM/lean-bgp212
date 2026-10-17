/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026), Definition 4.5 (the W-trick) and §12 (H₄₅).
-/
import BGP212.Basic
import BGP212.MultiShift
import Mathlib.Data.Nat.Squarefree

/-! # The W-trick data

`H45Z` is the tuple `H₄₅` of Lemma 12.1 (`BGP212.H45`) as a finite set of integer shifts,
the form the multi-shift theorem takes. `W23 = 2·3·5·7·11·13·17·19·23`, the product of the
primes up to 23: the primes at which `H₄₅` leaves exactly one free class. -/

namespace BGP212.WTrick

/-- `H₄₅` as a finite set of integer shifts. -/
def H45Z : Finset ℤ := (BGP212.H45.map (fun h : ℕ => (h : ℤ))).toFinset

/-- `W = 2·3·5·7·11·13·17·19·23 = 223092870`. -/
def W23 : ℕ := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23

end BGP212.WTrick
