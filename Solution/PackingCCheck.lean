/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Emitted by specs/checks/packing_a3c_emit.py.
-/
import Solution.PackingCData

/-! # A3c: the kernel runs the verified checker on every certificate piece

Each subtree of at most 8 leaves is checked by `decide +kernel` on its own cell (the base cell
plus the cuts on its path); `checkTree2_split_path` assembles the pieces and `rowC_intro`
closes each row. -/

namespace BGP212.PackingCert

theorem certRowC0_0_valid :
    checkTree2 4 6 cdD (pathCell (baseCell 1 3 2)
      []) certRowC0_0 = true := by
  decide +kernel

/-- (D, 1, 3). -/
theorem certRowC0_valid : rowC certRowC0 = true :=
  rowC_intro (by decide) (by decide) certRowC0_0_valid

theorem certRowC1_0_valid :
    checkTree2 5 7 cdD (pathCell (baseCell 1 4 2)
      []) certRowC1_0 = true := by
  decide +kernel

/-- (D, 1, 4). -/
theorem certRowC1_valid : rowC certRowC1 = true :=
  rowC_intro (by decide) (by decide) certRowC1_0_valid

theorem certRowC2_0_valid :
    checkTree2 4 6 cdD (pathCell (baseCell 2 2 2)
      []) certRowC2_0 = true := by
  decide +kernel

/-- (D, 2, 2). -/
theorem certRowC2_valid : rowC certRowC2 = true :=
  rowC_intro (by decide) (by decide) certRowC2_0_valid

theorem certRowC3_0_valid :
    checkTree2 5 7 cdD (pathCell (baseCell 2 3 2)
      []) certRowC3_0 = true := by
  decide +kernel

/-- (D, 2, 3). -/
theorem certRowC3_valid : rowC certRowC3 = true :=
  rowC_intro (by decide) (by decide) certRowC3_0_valid

theorem certRowC4_0_valid :
    checkTree2 6 8 cdD (pathCell (baseCell 2 4 2)
      []) certRowC4_0 = true := by
  decide +kernel

/-- (D, 2, 4). -/
theorem certRowC4_valid : rowC certRowC4 = true :=
  rowC_intro (by decide) (by decide) certRowC4_0_valid

theorem certRowC5_2_valid :
    checkTree2 6 8 cdD (pathCell (baseCell 3 3 2)
      [([0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC5_2 = true := by
  decide +kernel

theorem certRowC5_1_valid :
    checkTree2 6 8 cdD (pathCell (baseCell 3 3 2)
      [([0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC5_1 = true := by
  decide +kernel

theorem certRowC5_0_valid :
    checkTree2 6 8 cdD (pathCell (baseCell 3 3 2)
      []) certRowC5_0 = true :=
  checkTree2_split_path (by decide) certRowC5_1_valid certRowC5_2_valid

/-- (D, 3, 3). -/
theorem certRowC5_valid : rowC certRowC5 = true :=
  rowC_intro (by decide) (by decide) certRowC5_0_valid

theorem certRowC6_2_valid :
    checkTree2 7 9 cdD (pathCell (baseCell 3 4 2)
      [([0, 1, 1, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC6_2 = true := by
  decide +kernel

theorem certRowC6_1_valid :
    checkTree2 7 9 cdD (pathCell (baseCell 3 4 2)
      [([0, 1, 1, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC6_1 = true := by
  decide +kernel

theorem certRowC6_0_valid :
    checkTree2 7 9 cdD (pathCell (baseCell 3 4 2)
      []) certRowC6_0 = true :=
  checkTree2_split_path (by decide) certRowC6_1_valid certRowC6_2_valid

/-- (D, 3, 4). -/
theorem certRowC6_valid : rowC certRowC6 = true :=
  rowC_intro (by decide) (by decide) certRowC6_0_valid

theorem certRowC7_0_valid :
    checkTree2 8 10 cdD (pathCell (baseCell 3 5 2)
      []) certRowC7_0 = true := by
  decide +kernel

/-- (D, 3, 5). -/
theorem certRowC7_valid : rowC certRowC7 = true :=
  rowC_intro (by decide) (by decide) certRowC7_0_valid

theorem certRowC8_2_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 3 6 2)
      [([0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC8_2 = true := by
  decide +kernel

theorem certRowC8_1_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 3 6 2)
      [([0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC8_1 = true := by
  decide +kernel

theorem certRowC8_0_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 3 6 2)
      []) certRowC8_0 = true :=
  checkTree2_split_path (by decide) certRowC8_1_valid certRowC8_2_valid

/-- (D, 3, 6). -/
theorem certRowC8_valid : rowC certRowC8 = true :=
  rowC_intro (by decide) (by decide) certRowC8_0_valid

theorem certRowC9_10_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC9_10 = true := by
  decide +kernel

theorem certRowC9_9_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC9_9 = true := by
  decide +kernel

theorem certRowC9_8_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC9_8 = true := by
  decide +kernel

theorem certRowC9_7_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC9_7 = true :=
  checkTree2_split_path (by decide) certRowC9_8_valid certRowC9_9_valid

theorem certRowC9_6_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC9_6 = true :=
  checkTree2_split_path (by decide) certRowC9_7_valid certRowC9_10_valid

theorem certRowC9_5_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC9_5 = true := by
  decide +kernel

theorem certRowC9_4_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC9_4 = true :=
  checkTree2_split_path (by decide) certRowC9_5_valid certRowC9_6_valid

theorem certRowC9_3_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC9_3 = true := by
  decide +kernel

theorem certRowC9_2_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC9_2 = true :=
  checkTree2_split_path (by decide) certRowC9_3_valid certRowC9_4_valid

theorem certRowC9_1_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      [([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC9_1 = true := by
  decide +kernel

theorem certRowC9_0_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 3 7 2)
      []) certRowC9_0 = true :=
  checkTree2_split_path (by decide) certRowC9_1_valid certRowC9_2_valid

/-- (D, 3, 7). -/
theorem certRowC9_valid : rowC certRowC9 = true :=
  rowC_intro (by decide) (by decide) certRowC9_0_valid

theorem certRowC10_0_valid :
    checkTree2 8 10 cdD (pathCell (baseCell 4 4 2)
      []) certRowC10_0 = true := by
  decide +kernel

/-- (D, 4, 4). -/
theorem certRowC10_valid : rowC certRowC10 = true :=
  rowC_intro (by decide) (by decide) certRowC10_0_valid

theorem certRowC11_6_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 4 5 2)
      [([0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC11_6 = true := by
  decide +kernel

theorem certRowC11_5_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 4 5 2)
      [([0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC11_5 = true := by
  decide +kernel

theorem certRowC11_4_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 4 5 2)
      [([0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC11_4 = true := by
  decide +kernel

theorem certRowC11_3_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 4 5 2)
      [([0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC11_3 = true :=
  checkTree2_split_path (by decide) certRowC11_4_valid certRowC11_5_valid

theorem certRowC11_2_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 4 5 2)
      [([0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC11_2 = true :=
  checkTree2_split_path (by decide) certRowC11_3_valid certRowC11_6_valid

theorem certRowC11_1_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 4 5 2)
      [([0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC11_1 = true := by
  decide +kernel

theorem certRowC11_0_valid :
    checkTree2 9 11 cdD (pathCell (baseCell 4 5 2)
      []) certRowC11_0 = true :=
  checkTree2_split_path (by decide) certRowC11_1_valid certRowC11_2_valid

/-- (D, 4, 5). -/
theorem certRowC11_valid : rowC certRowC11 = true :=
  rowC_intro (by decide) (by decide) certRowC11_0_valid

theorem certRowC12_2_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 4 6 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC12_2 = true := by
  decide +kernel

theorem certRowC12_1_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 4 6 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC12_1 = true := by
  decide +kernel

theorem certRowC12_0_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 4 6 2)
      []) certRowC12_0 = true :=
  checkTree2_split_path (by decide) certRowC12_1_valid certRowC12_2_valid

/-- (D, 4, 6). -/
theorem certRowC12_valid : rowC certRowC12 = true :=
  rowC_intro (by decide) (by decide) certRowC12_0_valid

theorem certRowC13_0_valid :
    checkTree2 11 13 cdD (pathCell (baseCell 4 7 2)
      []) certRowC13_0 = true := by
  decide +kernel

/-- (D, 4, 7). -/
theorem certRowC13_valid : rowC certRowC13 = true :=
  rowC_intro (by decide) (by decide) certRowC13_0_valid

theorem certRowC14_8_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC14_8 = true := by
  decide +kernel

theorem certRowC14_7_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC14_7 = true := by
  decide +kernel

theorem certRowC14_6_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC14_6 = true :=
  checkTree2_split_path (by decide) certRowC14_7_valid certRowC14_8_valid

theorem certRowC14_5_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC14_5 = true := by
  decide +kernel

theorem certRowC14_4_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC14_4 = true :=
  checkTree2_split_path (by decide) certRowC14_5_valid certRowC14_6_valid

theorem certRowC14_3_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC14_3 = true := by
  decide +kernel

theorem certRowC14_2_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC14_2 = true :=
  checkTree2_split_path (by decide) certRowC14_3_valid certRowC14_4_valid

theorem certRowC14_1_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC14_1 = true := by
  decide +kernel

theorem certRowC14_0_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 4 8 2)
      []) certRowC14_0 = true :=
  checkTree2_split_path (by decide) certRowC14_1_valid certRowC14_2_valid

/-- (D, 4, 8). -/
theorem certRowC14_valid : rowC certRowC14 = true :=
  rowC_intro (by decide) (by decide) certRowC14_0_valid

theorem certRowC15_10_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC15_10 = true := by
  decide +kernel

theorem certRowC15_9_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC15_9 = true := by
  decide +kernel

theorem certRowC15_8_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC15_8 = true := by
  decide +kernel

theorem certRowC15_7_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC15_7 = true := by
  decide +kernel

theorem certRowC15_6_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC15_6 = true :=
  checkTree2_split_path (by decide) certRowC15_7_valid certRowC15_8_valid

theorem certRowC15_5_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC15_5 = true :=
  checkTree2_split_path (by decide) certRowC15_6_valid certRowC15_9_valid

theorem certRowC15_4_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC15_4 = true := by
  decide +kernel

theorem certRowC15_3_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC15_3 = true :=
  checkTree2_split_path (by decide) certRowC15_4_valid certRowC15_5_valid

theorem certRowC15_2_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC15_2 = true :=
  checkTree2_split_path (by decide) certRowC15_3_valid certRowC15_10_valid

theorem certRowC15_1_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC15_1 = true := by
  decide +kernel

theorem certRowC15_0_valid :
    checkTree2 10 12 cdD (pathCell (baseCell 5 5 2)
      []) certRowC15_0 = true :=
  checkTree2_split_path (by decide) certRowC15_1_valid certRowC15_2_valid

/-- (D, 5, 5). -/
theorem certRowC15_valid : rowC certRowC15 = true :=
  rowC_intro (by decide) (by decide) certRowC15_0_valid

theorem certRowC16_6_valid :
    checkTree2 11 13 cdD (pathCell (baseCell 5 6 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC16_6 = true := by
  decide +kernel

theorem certRowC16_5_valid :
    checkTree2 11 13 cdD (pathCell (baseCell 5 6 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC16_5 = true := by
  decide +kernel

theorem certRowC16_4_valid :
    checkTree2 11 13 cdD (pathCell (baseCell 5 6 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC16_4 = true := by
  decide +kernel

theorem certRowC16_3_valid :
    checkTree2 11 13 cdD (pathCell (baseCell 5 6 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC16_3 = true :=
  checkTree2_split_path (by decide) certRowC16_4_valid certRowC16_5_valid

theorem certRowC16_2_valid :
    checkTree2 11 13 cdD (pathCell (baseCell 5 6 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC16_2 = true :=
  checkTree2_split_path (by decide) certRowC16_3_valid certRowC16_6_valid

theorem certRowC16_1_valid :
    checkTree2 11 13 cdD (pathCell (baseCell 5 6 2)
      [([0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC16_1 = true := by
  decide +kernel

theorem certRowC16_0_valid :
    checkTree2 11 13 cdD (pathCell (baseCell 5 6 2)
      []) certRowC16_0 = true :=
  checkTree2_split_path (by decide) certRowC16_1_valid certRowC16_2_valid

/-- (D, 5, 6). -/
theorem certRowC16_valid : rowC certRowC16 = true :=
  rowC_intro (by decide) (by decide) certRowC16_0_valid

theorem certRowC17_8_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC17_8 = true := by
  decide +kernel

theorem certRowC17_7_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC17_7 = true := by
  decide +kernel

theorem certRowC17_6_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC17_6 = true := by
  decide +kernel

theorem certRowC17_5_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC17_5 = true := by
  decide +kernel

theorem certRowC17_4_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC17_4 = true :=
  checkTree2_split_path (by decide) certRowC17_5_valid certRowC17_6_valid

theorem certRowC17_3_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC17_3 = true :=
  checkTree2_split_path (by decide) certRowC17_4_valid certRowC17_7_valid

theorem certRowC17_2_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC17_2 = true :=
  checkTree2_split_path (by decide) certRowC17_3_valid certRowC17_8_valid

theorem certRowC17_1_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      [([0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC17_1 = true := by
  decide +kernel

theorem certRowC17_0_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 5 7 2)
      []) certRowC17_0 = true :=
  checkTree2_split_path (by decide) certRowC17_1_valid certRowC17_2_valid

/-- (D, 5, 7). -/
theorem certRowC17_valid : rowC certRowC17 = true :=
  rowC_intro (by decide) (by decide) certRowC17_0_valid

theorem certRowC18_28_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC18_28 = true := by
  decide +kernel

theorem certRowC18_27_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC18_27 = true := by
  decide +kernel

theorem certRowC18_26_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC18_26 = true := by
  decide +kernel

theorem certRowC18_25_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC18_25 = true := by
  decide +kernel

theorem certRowC18_24_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC18_24 = true := by
  decide +kernel

theorem certRowC18_23_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC18_23 = true :=
  checkTree2_split_path (by decide) certRowC18_24_valid certRowC18_25_valid

theorem certRowC18_22_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC18_22 = true :=
  checkTree2_split_path (by decide) certRowC18_23_valid certRowC18_26_valid

theorem certRowC18_21_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC18_21 = true :=
  checkTree2_split_path (by decide) certRowC18_22_valid certRowC18_27_valid

theorem certRowC18_20_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC18_20 = true := by
  decide +kernel

theorem certRowC18_19_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC18_19 = true :=
  checkTree2_split_path (by decide) certRowC18_20_valid certRowC18_21_valid

theorem certRowC18_18_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC18_18 = true :=
  checkTree2_split_path (by decide) certRowC18_19_valid certRowC18_28_valid

theorem certRowC18_17_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC18_17 = true := by
  decide +kernel

theorem certRowC18_16_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC18_16 = true :=
  checkTree2_split_path (by decide) certRowC18_17_valid certRowC18_18_valid

theorem certRowC18_15_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC18_15 = true := by
  decide +kernel

theorem certRowC18_14_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC18_14 = true :=
  checkTree2_split_path (by decide) certRowC18_15_valid certRowC18_16_valid

theorem certRowC18_13_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC18_13 = true := by
  decide +kernel

theorem certRowC18_12_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC18_12 = true :=
  checkTree2_split_path (by decide) certRowC18_13_valid certRowC18_14_valid

theorem certRowC18_11_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC18_11 = true := by
  decide +kernel

theorem certRowC18_10_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC18_10 = true :=
  checkTree2_split_path (by decide) certRowC18_11_valid certRowC18_12_valid

theorem certRowC18_9_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC18_9 = true := by
  decide +kernel

theorem certRowC18_8_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC18_8 = true := by
  decide +kernel

theorem certRowC18_7_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC18_7 = true := by
  decide +kernel

theorem certRowC18_6_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC18_6 = true := by
  decide +kernel

theorem certRowC18_5_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC18_5 = true :=
  checkTree2_split_path (by decide) certRowC18_6_valid certRowC18_7_valid

theorem certRowC18_4_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC18_4 = true := by
  decide +kernel

theorem certRowC18_3_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC18_3 = true :=
  checkTree2_split_path (by decide) certRowC18_4_valid certRowC18_5_valid

theorem certRowC18_2_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC18_2 = true :=
  checkTree2_split_path (by decide) certRowC18_3_valid certRowC18_8_valid

theorem certRowC18_1_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC18_1 = true :=
  checkTree2_split_path (by decide) certRowC18_2_valid certRowC18_9_valid

theorem certRowC18_0_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 5 8 2)
      []) certRowC18_0 = true :=
  checkTree2_split_path (by decide) certRowC18_1_valid certRowC18_10_valid

/-- (D, 5, 8). -/
theorem certRowC18_valid : rowC certRowC18 = true :=
  rowC_intro (by decide) (by decide) certRowC18_0_valid

theorem certRowC19_28_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC19_28 = true := by
  decide +kernel

theorem certRowC19_27_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC19_27 = true := by
  decide +kernel

theorem certRowC19_26_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC19_26 = true :=
  checkTree2_split_path (by decide) certRowC19_27_valid certRowC19_28_valid

theorem certRowC19_25_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC19_25 = true := by
  decide +kernel

theorem certRowC19_24_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC19_24 = true := by
  decide +kernel

theorem certRowC19_23_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC19_23 = true := by
  decide +kernel

theorem certRowC19_22_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC19_22 = true :=
  checkTree2_split_path (by decide) certRowC19_23_valid certRowC19_24_valid

theorem certRowC19_21_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC19_21 = true := by
  decide +kernel

theorem certRowC19_20_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC19_20 = true :=
  checkTree2_split_path (by decide) certRowC19_21_valid certRowC19_22_valid

theorem certRowC19_19_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC19_19 = true :=
  checkTree2_split_path (by decide) certRowC19_20_valid certRowC19_25_valid

theorem certRowC19_18_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC19_18 = true := by
  decide +kernel

theorem certRowC19_17_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC19_17 = true := by
  decide +kernel

theorem certRowC19_16_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC19_16 = true :=
  checkTree2_split_path (by decide) certRowC19_17_valid certRowC19_18_valid

theorem certRowC19_15_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC19_15 = true := by
  decide +kernel

theorem certRowC19_14_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC19_14 = true := by
  decide +kernel

theorem certRowC19_13_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC19_13 = true := by
  decide +kernel

theorem certRowC19_12_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC19_12 = true :=
  checkTree2_split_path (by decide) certRowC19_13_valid certRowC19_14_valid

theorem certRowC19_11_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC19_11 = true :=
  checkTree2_split_path (by decide) certRowC19_12_valid certRowC19_15_valid

theorem certRowC19_10_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC19_10 = true := by
  decide +kernel

theorem certRowC19_9_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC19_9 = true :=
  checkTree2_split_path (by decide) certRowC19_10_valid certRowC19_11_valid

theorem certRowC19_8_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC19_8 = true :=
  checkTree2_split_path (by decide) certRowC19_9_valid certRowC19_16_valid

theorem certRowC19_7_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC19_7 = true := by
  decide +kernel

theorem certRowC19_6_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC19_6 = true :=
  checkTree2_split_path (by decide) certRowC19_7_valid certRowC19_8_valid

theorem certRowC19_5_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC19_5 = true := by
  decide +kernel

theorem certRowC19_4_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC19_4 = true :=
  checkTree2_split_path (by decide) certRowC19_5_valid certRowC19_6_valid

theorem certRowC19_3_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC19_3 = true := by
  decide +kernel

theorem certRowC19_2_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC19_2 = true :=
  checkTree2_split_path (by decide) certRowC19_3_valid certRowC19_4_valid

theorem certRowC19_1_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      [([1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC19_1 = true :=
  checkTree2_split_path (by decide) certRowC19_2_valid certRowC19_19_valid

theorem certRowC19_0_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 5 9 2)
      []) certRowC19_0 = true :=
  checkTree2_split_path (by decide) certRowC19_1_valid certRowC19_26_valid

/-- (D, 5, 9). -/
theorem certRowC19_valid : rowC certRowC19 = true :=
  rowC_intro (by decide) (by decide) certRowC19_0_valid

theorem certRowC20_14_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC20_14 = true := by
  decide +kernel

theorem certRowC20_13_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC20_13 = true := by
  decide +kernel

theorem certRowC20_12_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC20_12 = true := by
  decide +kernel

theorem certRowC20_11_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC20_11 = true := by
  decide +kernel

theorem certRowC20_10_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC20_10 = true := by
  decide +kernel

theorem certRowC20_9_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC20_9 = true :=
  checkTree2_split_path (by decide) certRowC20_10_valid certRowC20_11_valid

theorem certRowC20_8_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC20_8 = true :=
  checkTree2_split_path (by decide) certRowC20_9_valid certRowC20_12_valid

theorem certRowC20_7_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC20_7 = true :=
  checkTree2_split_path (by decide) certRowC20_8_valid certRowC20_13_valid

theorem certRowC20_6_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC20_6 = true :=
  checkTree2_split_path (by decide) certRowC20_7_valid certRowC20_14_valid

theorem certRowC20_5_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC20_5 = true := by
  decide +kernel

theorem certRowC20_4_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC20_4 = true :=
  checkTree2_split_path (by decide) certRowC20_5_valid certRowC20_6_valid

theorem certRowC20_3_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC20_3 = true := by
  decide +kernel

theorem certRowC20_2_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC20_2 = true :=
  checkTree2_split_path (by decide) certRowC20_3_valid certRowC20_4_valid

theorem certRowC20_1_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      [([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC20_1 = true := by
  decide +kernel

theorem certRowC20_0_valid :
    checkTree2 12 14 cdD (pathCell (baseCell 6 6 2)
      []) certRowC20_0 = true :=
  checkTree2_split_path (by decide) certRowC20_1_valid certRowC20_2_valid

/-- (D, 6, 6). -/
theorem certRowC20_valid : rowC certRowC20 = true :=
  rowC_intro (by decide) (by decide) certRowC20_0_valid

theorem certRowC21_12_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC21_12 = true := by
  decide +kernel

theorem certRowC21_11_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC21_11 = true := by
  decide +kernel

theorem certRowC21_10_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC21_10 = true := by
  decide +kernel

theorem certRowC21_9_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC21_9 = true := by
  decide +kernel

theorem certRowC21_8_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC21_8 = true := by
  decide +kernel

theorem certRowC21_7_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC21_7 = true :=
  checkTree2_split_path (by decide) certRowC21_8_valid certRowC21_9_valid

theorem certRowC21_6_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC21_6 = true :=
  checkTree2_split_path (by decide) certRowC21_7_valid certRowC21_10_valid

theorem certRowC21_5_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC21_5 = true := by
  decide +kernel

theorem certRowC21_4_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC21_4 = true :=
  checkTree2_split_path (by decide) certRowC21_5_valid certRowC21_6_valid

theorem certRowC21_3_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC21_3 = true :=
  checkTree2_split_path (by decide) certRowC21_4_valid certRowC21_11_valid

theorem certRowC21_2_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC21_2 = true :=
  checkTree2_split_path (by decide) certRowC21_3_valid certRowC21_12_valid

theorem certRowC21_1_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      [([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC21_1 = true := by
  decide +kernel

theorem certRowC21_0_valid :
    checkTree2 13 15 cdD (pathCell (baseCell 6 7 2)
      []) certRowC21_0 = true :=
  checkTree2_split_path (by decide) certRowC21_1_valid certRowC21_2_valid

/-- (D, 6, 7). -/
theorem certRowC21_valid : rowC certRowC21 = true :=
  rowC_intro (by decide) (by decide) certRowC21_0_valid

theorem certRowC22_10_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC22_10 = true := by
  decide +kernel

theorem certRowC22_9_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC22_9 = true := by
  decide +kernel

theorem certRowC22_8_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC22_8 = true :=
  checkTree2_split_path (by decide) certRowC22_9_valid certRowC22_10_valid

theorem certRowC22_7_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC22_7 = true := by
  decide +kernel

theorem certRowC22_6_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC22_6 = true :=
  checkTree2_split_path (by decide) certRowC22_7_valid certRowC22_8_valid

theorem certRowC22_5_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC22_5 = true := by
  decide +kernel

theorem certRowC22_4_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC22_4 = true :=
  checkTree2_split_path (by decide) certRowC22_5_valid certRowC22_6_valid

theorem certRowC22_3_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC22_3 = true := by
  decide +kernel

theorem certRowC22_2_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC22_2 = true :=
  checkTree2_split_path (by decide) certRowC22_3_valid certRowC22_4_valid

theorem certRowC22_1_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      [([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC22_1 = true := by
  decide +kernel

theorem certRowC22_0_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 6 8 2)
      []) certRowC22_0 = true :=
  checkTree2_split_path (by decide) certRowC22_1_valid certRowC22_2_valid

/-- (D, 6, 8). -/
theorem certRowC22_valid : rowC certRowC22 = true :=
  rowC_intro (by decide) (by decide) certRowC22_0_valid

theorem certRowC23_14_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC23_14 = true := by
  decide +kernel

theorem certRowC23_13_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC23_13 = true := by
  decide +kernel

theorem certRowC23_12_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC23_12 = true := by
  decide +kernel

theorem certRowC23_11_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC23_11 = true := by
  decide +kernel

theorem certRowC23_10_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC23_10 = true := by
  decide +kernel

theorem certRowC23_9_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC23_9 = true :=
  checkTree2_split_path (by decide) certRowC23_10_valid certRowC23_11_valid

theorem certRowC23_8_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC23_8 = true := by
  decide +kernel

theorem certRowC23_7_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC23_7 = true :=
  checkTree2_split_path (by decide) certRowC23_8_valid certRowC23_9_valid

theorem certRowC23_6_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC23_6 = true :=
  checkTree2_split_path (by decide) certRowC23_7_valid certRowC23_12_valid

theorem certRowC23_5_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC23_5 = true := by
  decide +kernel

theorem certRowC23_4_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC23_4 = true :=
  checkTree2_split_path (by decide) certRowC23_5_valid certRowC23_6_valid

theorem certRowC23_3_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC23_3 = true :=
  checkTree2_split_path (by decide) certRowC23_4_valid certRowC23_13_valid

theorem certRowC23_2_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC23_2 = true :=
  checkTree2_split_path (by decide) certRowC23_3_valid certRowC23_14_valid

theorem certRowC23_1_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      [([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC23_1 = true := by
  decide +kernel

theorem certRowC23_0_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 6 9 2)
      []) certRowC23_0 = true :=
  checkTree2_split_path (by decide) certRowC23_1_valid certRowC23_2_valid

/-- (D, 6, 9). -/
theorem certRowC23_valid : rowC certRowC23 = true :=
  rowC_intro (by decide) (by decide) certRowC23_0_valid

theorem certRowC24_16_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC24_16 = true := by
  decide +kernel

theorem certRowC24_15_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC24_15 = true := by
  decide +kernel

theorem certRowC24_14_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC24_14 = true :=
  checkTree2_split_path (by decide) certRowC24_15_valid certRowC24_16_valid

theorem certRowC24_13_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC24_13 = true := by
  decide +kernel

theorem certRowC24_12_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC24_12 = true := by
  decide +kernel

theorem certRowC24_11_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC24_11 = true := by
  decide +kernel

theorem certRowC24_10_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC24_10 = true :=
  checkTree2_split_path (by decide) certRowC24_11_valid certRowC24_12_valid

theorem certRowC24_9_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -8], (0), 1, false)]) certRowC24_9 = true :=
  checkTree2_split_path (by decide) certRowC24_10_valid certRowC24_13_valid

theorem certRowC24_8_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -8], (0), 1, true)]) certRowC24_8 = true := by
  decide +kernel

theorem certRowC24_7_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC24_7 = true :=
  checkTree2_split_path (by decide) certRowC24_8_valid certRowC24_9_valid

theorem certRowC24_6_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC24_6 = true :=
  checkTree2_split_path (by decide) certRowC24_7_valid certRowC24_14_valid

theorem certRowC24_5_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC24_5 = true := by
  decide +kernel

theorem certRowC24_4_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC24_4 = true :=
  checkTree2_split_path (by decide) certRowC24_5_valid certRowC24_6_valid

theorem certRowC24_3_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC24_3 = true := by
  decide +kernel

theorem certRowC24_2_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC24_2 = true :=
  checkTree2_split_path (by decide) certRowC24_3_valid certRowC24_4_valid

theorem certRowC24_1_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC24_1 = true := by
  decide +kernel

theorem certRowC24_0_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 6 10 2)
      []) certRowC24_0 = true :=
  checkTree2_split_path (by decide) certRowC24_1_valid certRowC24_2_valid

/-- (D, 6, 10). -/
theorem certRowC24_valid : rowC certRowC24 = true :=
  rowC_intro (by decide) (by decide) certRowC24_0_valid

theorem certRowC25_34_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC25_34 = true := by
  decide +kernel

theorem certRowC25_33_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC25_33 = true := by
  decide +kernel

theorem certRowC25_32_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC25_32 = true := by
  decide +kernel

theorem certRowC25_31_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC25_31 = true := by
  decide +kernel

theorem certRowC25_30_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC25_30 = true := by
  decide +kernel

theorem certRowC25_29_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC25_29 = true := by
  decide +kernel

theorem certRowC25_28_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC25_28 = true := by
  decide +kernel

theorem certRowC25_27_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC25_27 = true :=
  checkTree2_split_path (by decide) certRowC25_28_valid certRowC25_29_valid

theorem certRowC25_26_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC25_26 = true :=
  checkTree2_split_path (by decide) certRowC25_27_valid certRowC25_30_valid

theorem certRowC25_25_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC25_25 = true := by
  decide +kernel

theorem certRowC25_24_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC25_24 = true :=
  checkTree2_split_path (by decide) certRowC25_25_valid certRowC25_26_valid

theorem certRowC25_23_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC25_23 = true :=
  checkTree2_split_path (by decide) certRowC25_24_valid certRowC25_31_valid

theorem certRowC25_22_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC25_22 = true := by
  decide +kernel

theorem certRowC25_21_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC25_21 = true :=
  checkTree2_split_path (by decide) certRowC25_22_valid certRowC25_23_valid

theorem certRowC25_20_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC25_20 = true := by
  decide +kernel

theorem certRowC25_19_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC25_19 = true := by
  decide +kernel

theorem certRowC25_18_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC25_18 = true := by
  decide +kernel

theorem certRowC25_17_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC25_17 = true :=
  checkTree2_split_path (by decide) certRowC25_18_valid certRowC25_19_valid

theorem certRowC25_16_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC25_16 = true :=
  checkTree2_split_path (by decide) certRowC25_17_valid certRowC25_20_valid

theorem certRowC25_15_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC25_15 = true := by
  decide +kernel

theorem certRowC25_14_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false)]) certRowC25_14 = true :=
  checkTree2_split_path (by decide) certRowC25_15_valid certRowC25_16_valid

theorem certRowC25_13_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, true)]) certRowC25_13 = true := by
  decide +kernel

theorem certRowC25_12_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC25_12 = true :=
  checkTree2_split_path (by decide) certRowC25_13_valid certRowC25_14_valid

theorem certRowC25_11_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC25_11 = true :=
  checkTree2_split_path (by decide) certRowC25_12_valid certRowC25_21_valid

theorem certRowC25_10_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC25_10 = true :=
  checkTree2_split_path (by decide) certRowC25_11_valid certRowC25_32_valid

theorem certRowC25_9_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC25_9 = true :=
  checkTree2_split_path (by decide) certRowC25_10_valid certRowC25_33_valid

theorem certRowC25_8_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC25_8 = true :=
  checkTree2_split_path (by decide) certRowC25_9_valid certRowC25_34_valid

theorem certRowC25_7_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC25_7 = true := by
  decide +kernel

theorem certRowC25_6_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC25_6 = true := by
  decide +kernel

theorem certRowC25_5_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC25_5 = true :=
  checkTree2_split_path (by decide) certRowC25_6_valid certRowC25_7_valid

theorem certRowC25_4_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC25_4 = true := by
  decide +kernel

theorem certRowC25_3_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC25_3 = true :=
  checkTree2_split_path (by decide) certRowC25_4_valid certRowC25_5_valid

theorem certRowC25_2_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC25_2 = true := by
  decide +kernel

theorem certRowC25_1_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      [([0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC25_1 = true :=
  checkTree2_split_path (by decide) certRowC25_2_valid certRowC25_3_valid

theorem certRowC25_0_valid :
    checkTree2 14 16 cdD (pathCell (baseCell 7 7 2)
      []) certRowC25_0 = true :=
  checkTree2_split_path (by decide) certRowC25_1_valid certRowC25_8_valid

/-- (D, 7, 7). -/
theorem certRowC25_valid : rowC certRowC25 = true :=
  rowC_intro (by decide) (by decide) certRowC25_0_valid

theorem certRowC26_8_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC26_8 = true := by
  decide +kernel

theorem certRowC26_7_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC26_7 = true := by
  decide +kernel

theorem certRowC26_6_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC26_6 = true := by
  decide +kernel

theorem certRowC26_5_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC26_5 = true :=
  checkTree2_split_path (by decide) certRowC26_6_valid certRowC26_7_valid

theorem certRowC26_4_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC26_4 = true := by
  decide +kernel

theorem certRowC26_3_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC26_3 = true :=
  checkTree2_split_path (by decide) certRowC26_4_valid certRowC26_5_valid

theorem certRowC26_2_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC26_2 = true :=
  checkTree2_split_path (by decide) certRowC26_3_valid certRowC26_8_valid

theorem certRowC26_1_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC26_1 = true := by
  decide +kernel

theorem certRowC26_0_valid :
    checkTree2 15 17 cdD (pathCell (baseCell 7 8 2)
      []) certRowC26_0 = true :=
  checkTree2_split_path (by decide) certRowC26_1_valid certRowC26_2_valid

/-- (D, 7, 8). -/
theorem certRowC26_valid : rowC certRowC26 = true :=
  rowC_intro (by decide) (by decide) certRowC26_0_valid

theorem certRowC27_28_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC27_28 = true := by
  decide +kernel

theorem certRowC27_27_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC27_27 = true := by
  decide +kernel

theorem certRowC27_26_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC27_26 = true := by
  decide +kernel

theorem certRowC27_25_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC27_25 = true := by
  decide +kernel

theorem certRowC27_24_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC27_24 = true := by
  decide +kernel

theorem certRowC27_23_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC27_23 = true := by
  decide +kernel

theorem certRowC27_22_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC27_22 = true :=
  checkTree2_split_path (by decide) certRowC27_23_valid certRowC27_24_valid

theorem certRowC27_21_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC27_21 = true := by
  decide +kernel

theorem certRowC27_20_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC27_20 = true :=
  checkTree2_split_path (by decide) certRowC27_21_valid certRowC27_22_valid

theorem certRowC27_19_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC27_19 = true :=
  checkTree2_split_path (by decide) certRowC27_20_valid certRowC27_25_valid

theorem certRowC27_18_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC27_18 = true := by
  decide +kernel

theorem certRowC27_17_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC27_17 = true := by
  decide +kernel

theorem certRowC27_16_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC27_16 = true :=
  checkTree2_split_path (by decide) certRowC27_17_valid certRowC27_18_valid

theorem certRowC27_15_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC27_15 = true := by
  decide +kernel

theorem certRowC27_14_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC27_14 = true :=
  checkTree2_split_path (by decide) certRowC27_15_valid certRowC27_16_valid

theorem certRowC27_13_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC27_13 = true :=
  checkTree2_split_path (by decide) certRowC27_14_valid certRowC27_19_valid

theorem certRowC27_12_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC27_12 = true :=
  checkTree2_split_path (by decide) certRowC27_13_valid certRowC27_26_valid

theorem certRowC27_11_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC27_11 = true := by
  decide +kernel

theorem certRowC27_10_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC27_10 = true := by
  decide +kernel

theorem certRowC27_9_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC27_9 = true :=
  checkTree2_split_path (by decide) certRowC27_10_valid certRowC27_11_valid

theorem certRowC27_8_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC27_8 = true := by
  decide +kernel

theorem certRowC27_7_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC27_7 = true :=
  checkTree2_split_path (by decide) certRowC27_8_valid certRowC27_9_valid

theorem certRowC27_6_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC27_6 = true :=
  checkTree2_split_path (by decide) certRowC27_7_valid certRowC27_12_valid

theorem certRowC27_5_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC27_5 = true := by
  decide +kernel

theorem certRowC27_4_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC27_4 = true :=
  checkTree2_split_path (by decide) certRowC27_5_valid certRowC27_6_valid

theorem certRowC27_3_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC27_3 = true :=
  checkTree2_split_path (by decide) certRowC27_4_valid certRowC27_27_valid

theorem certRowC27_2_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC27_2 = true :=
  checkTree2_split_path (by decide) certRowC27_3_valid certRowC27_28_valid

theorem certRowC27_1_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC27_1 = true := by
  decide +kernel

theorem certRowC27_0_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 7 9 2)
      []) certRowC27_0 = true :=
  checkTree2_split_path (by decide) certRowC27_1_valid certRowC27_2_valid

/-- (D, 7, 9). -/
theorem certRowC27_valid : rowC certRowC27 = true :=
  rowC_intro (by decide) (by decide) certRowC27_0_valid

theorem certRowC28_20_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC28_20 = true := by
  decide +kernel

theorem certRowC28_19_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC28_19 = true := by
  decide +kernel

theorem certRowC28_18_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC28_18 = true := by
  decide +kernel

theorem certRowC28_17_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC28_17 = true :=
  checkTree2_split_path (by decide) certRowC28_18_valid certRowC28_19_valid

theorem certRowC28_16_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC28_16 = true := by
  decide +kernel

theorem certRowC28_15_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC28_15 = true := by
  decide +kernel

theorem certRowC28_14_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC28_14 = true :=
  checkTree2_split_path (by decide) certRowC28_15_valid certRowC28_16_valid

theorem certRowC28_13_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC28_13 = true := by
  decide +kernel

theorem certRowC28_12_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC28_12 = true :=
  checkTree2_split_path (by decide) certRowC28_13_valid certRowC28_14_valid

theorem certRowC28_11_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC28_11 = true := by
  decide +kernel

theorem certRowC28_10_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC28_10 = true :=
  checkTree2_split_path (by decide) certRowC28_11_valid certRowC28_12_valid

theorem certRowC28_9_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC28_9 = true := by
  decide +kernel

theorem certRowC28_8_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC28_8 = true :=
  checkTree2_split_path (by decide) certRowC28_9_valid certRowC28_10_valid

theorem certRowC28_7_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC28_7 = true := by
  decide +kernel

theorem certRowC28_6_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC28_6 = true :=
  checkTree2_split_path (by decide) certRowC28_7_valid certRowC28_8_valid

theorem certRowC28_5_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC28_5 = true := by
  decide +kernel

theorem certRowC28_4_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC28_4 = true :=
  checkTree2_split_path (by decide) certRowC28_5_valid certRowC28_6_valid

theorem certRowC28_3_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC28_3 = true :=
  checkTree2_split_path (by decide) certRowC28_4_valid certRowC28_17_valid

theorem certRowC28_2_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC28_2 = true :=
  checkTree2_split_path (by decide) certRowC28_3_valid certRowC28_20_valid

theorem certRowC28_1_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC28_1 = true := by
  decide +kernel

theorem certRowC28_0_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 7 10 2)
      []) certRowC28_0 = true :=
  checkTree2_split_path (by decide) certRowC28_1_valid certRowC28_2_valid

/-- (D, 7, 10). -/
theorem certRowC28_valid : rowC certRowC28 = true :=
  rowC_intro (by decide) (by decide) certRowC28_0_valid

theorem certRowC29_24_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC29_24 = true := by
  decide +kernel

theorem certRowC29_23_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC29_23 = true := by
  decide +kernel

theorem certRowC29_22_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC29_22 = true :=
  checkTree2_split_path (by decide) certRowC29_23_valid certRowC29_24_valid

theorem certRowC29_21_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC29_21 = true := by
  decide +kernel

theorem certRowC29_20_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC29_20 = true := by
  decide +kernel

theorem certRowC29_19_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC29_19 = true := by
  decide +kernel

theorem certRowC29_18_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC29_18 = true := by
  decide +kernel

theorem certRowC29_17_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC29_17 = true := by
  decide +kernel

theorem certRowC29_16_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC29_16 = true := by
  decide +kernel

theorem certRowC29_15_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC29_15 = true := by
  decide +kernel

theorem certRowC29_14_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC29_14 = true :=
  checkTree2_split_path (by decide) certRowC29_15_valid certRowC29_16_valid

theorem certRowC29_13_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC29_13 = true := by
  decide +kernel

theorem certRowC29_12_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC29_12 = true :=
  checkTree2_split_path (by decide) certRowC29_13_valid certRowC29_14_valid

theorem certRowC29_11_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC29_11 = true :=
  checkTree2_split_path (by decide) certRowC29_12_valid certRowC29_17_valid

theorem certRowC29_10_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC29_10 = true := by
  decide +kernel

theorem certRowC29_9_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC29_9 = true :=
  checkTree2_split_path (by decide) certRowC29_10_valid certRowC29_11_valid

theorem certRowC29_8_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC29_8 = true :=
  checkTree2_split_path (by decide) certRowC29_9_valid certRowC29_18_valid

theorem certRowC29_7_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC29_7 = true :=
  checkTree2_split_path (by decide) certRowC29_8_valid certRowC29_19_valid

theorem certRowC29_6_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC29_6 = true :=
  checkTree2_split_path (by decide) certRowC29_7_valid certRowC29_20_valid

theorem certRowC29_5_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC29_5 = true :=
  checkTree2_split_path (by decide) certRowC29_6_valid certRowC29_21_valid

theorem certRowC29_4_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC29_4 = true :=
  checkTree2_split_path (by decide) certRowC29_5_valid certRowC29_22_valid

theorem certRowC29_3_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC29_3 = true := by
  decide +kernel

theorem certRowC29_2_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC29_2 = true :=
  checkTree2_split_path (by decide) certRowC29_3_valid certRowC29_4_valid

theorem certRowC29_1_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC29_1 = true := by
  decide +kernel

theorem certRowC29_0_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 7 11 2)
      []) certRowC29_0 = true :=
  checkTree2_split_path (by decide) certRowC29_1_valid certRowC29_2_valid

/-- (D, 7, 11). -/
theorem certRowC29_valid : rowC certRowC29 = true :=
  rowC_intro (by decide) (by decide) certRowC29_0_valid

theorem certRowC30_32_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC30_32 = true := by
  decide +kernel

theorem certRowC30_31_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC30_31 = true := by
  decide +kernel

theorem certRowC30_30_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC30_30 = true := by
  decide +kernel

theorem certRowC30_29_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC30_29 = true := by
  decide +kernel

theorem certRowC30_28_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC30_28 = true := by
  decide +kernel

theorem certRowC30_27_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC30_27 = true := by
  decide +kernel

theorem certRowC30_26_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC30_26 = true := by
  decide +kernel

theorem certRowC30_25_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC30_25 = true := by
  decide +kernel

theorem certRowC30_24_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC30_24 = true :=
  checkTree2_split_path (by decide) certRowC30_25_valid certRowC30_26_valid

theorem certRowC30_23_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC30_23 = true := by
  decide +kernel

theorem certRowC30_22_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC30_22 = true :=
  checkTree2_split_path (by decide) certRowC30_23_valid certRowC30_24_valid

theorem certRowC30_21_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC30_21 = true :=
  checkTree2_split_path (by decide) certRowC30_22_valid certRowC30_27_valid

theorem certRowC30_20_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC30_20 = true := by
  decide +kernel

theorem certRowC30_19_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC30_19 = true :=
  checkTree2_split_path (by decide) certRowC30_20_valid certRowC30_21_valid

theorem certRowC30_18_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC30_18 = true :=
  checkTree2_split_path (by decide) certRowC30_19_valid certRowC30_28_valid

theorem certRowC30_17_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC30_17 = true := by
  decide +kernel

theorem certRowC30_16_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC30_16 = true :=
  checkTree2_split_path (by decide) certRowC30_17_valid certRowC30_18_valid

theorem certRowC30_15_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC30_15 = true := by
  decide +kernel

theorem certRowC30_14_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC30_14 = true :=
  checkTree2_split_path (by decide) certRowC30_15_valid certRowC30_16_valid

theorem certRowC30_13_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC30_13 = true := by
  decide +kernel

theorem certRowC30_12_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC30_12 = true :=
  checkTree2_split_path (by decide) certRowC30_13_valid certRowC30_14_valid

theorem certRowC30_11_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC30_11 = true :=
  checkTree2_split_path (by decide) certRowC30_12_valid certRowC30_29_valid

theorem certRowC30_10_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC30_10 = true :=
  checkTree2_split_path (by decide) certRowC30_11_valid certRowC30_30_valid

theorem certRowC30_9_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC30_9 = true :=
  checkTree2_split_path (by decide) certRowC30_10_valid certRowC30_31_valid

theorem certRowC30_8_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC30_8 = true :=
  checkTree2_split_path (by decide) certRowC30_9_valid certRowC30_32_valid

theorem certRowC30_7_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC30_7 = true := by
  decide +kernel

theorem certRowC30_6_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC30_6 = true := by
  decide +kernel

theorem certRowC30_5_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC30_5 = true :=
  checkTree2_split_path (by decide) certRowC30_6_valid certRowC30_7_valid

theorem certRowC30_4_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC30_4 = true := by
  decide +kernel

theorem certRowC30_3_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC30_3 = true :=
  checkTree2_split_path (by decide) certRowC30_4_valid certRowC30_5_valid

theorem certRowC30_2_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC30_2 = true :=
  checkTree2_split_path (by decide) certRowC30_3_valid certRowC30_8_valid

theorem certRowC30_1_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC30_1 = true := by
  decide +kernel

theorem certRowC30_0_valid :
    checkTree2 16 18 cdD (pathCell (baseCell 8 8 2)
      []) certRowC30_0 = true :=
  checkTree2_split_path (by decide) certRowC30_1_valid certRowC30_2_valid

/-- (D, 8, 8). -/
theorem certRowC30_valid : rowC certRowC30 = true :=
  rowC_intro (by decide) (by decide) certRowC30_0_valid

theorem certRowC31_40_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC31_40 = true := by
  decide +kernel

theorem certRowC31_39_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC31_39 = true := by
  decide +kernel

theorem certRowC31_38_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC31_38 = true := by
  decide +kernel

theorem certRowC31_37_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC31_37 = true := by
  decide +kernel

theorem certRowC31_36_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC31_36 = true := by
  decide +kernel

theorem certRowC31_35_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC31_35 = true := by
  decide +kernel

theorem certRowC31_34_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC31_34 = true :=
  checkTree2_split_path (by decide) certRowC31_35_valid certRowC31_36_valid

theorem certRowC31_33_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC31_33 = true := by
  decide +kernel

theorem certRowC31_32_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC31_32 = true :=
  checkTree2_split_path (by decide) certRowC31_33_valid certRowC31_34_valid

theorem certRowC31_31_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC31_31 = true :=
  checkTree2_split_path (by decide) certRowC31_32_valid certRowC31_37_valid

theorem certRowC31_30_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC31_30 = true := by
  decide +kernel

theorem certRowC31_29_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC31_29 = true :=
  checkTree2_split_path (by decide) certRowC31_30_valid certRowC31_31_valid

theorem certRowC31_28_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC31_28 = true :=
  checkTree2_split_path (by decide) certRowC31_29_valid certRowC31_38_valid

theorem certRowC31_27_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC31_27 = true :=
  checkTree2_split_path (by decide) certRowC31_28_valid certRowC31_39_valid

theorem certRowC31_26_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC31_26 = true := by
  decide +kernel

theorem certRowC31_25_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC31_25 = true := by
  decide +kernel

theorem certRowC31_24_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC31_24 = true :=
  checkTree2_split_path (by decide) certRowC31_25_valid certRowC31_26_valid

theorem certRowC31_23_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC31_23 = true := by
  decide +kernel

theorem certRowC31_22_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC31_22 = true :=
  checkTree2_split_path (by decide) certRowC31_23_valid certRowC31_24_valid

theorem certRowC31_21_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC31_21 = true :=
  checkTree2_split_path (by decide) certRowC31_22_valid certRowC31_27_valid

theorem certRowC31_20_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC31_20 = true := by
  decide +kernel

theorem certRowC31_19_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC31_19 = true := by
  decide +kernel

theorem certRowC31_18_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC31_18 = true :=
  checkTree2_split_path (by decide) certRowC31_19_valid certRowC31_20_valid

theorem certRowC31_17_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC31_17 = true := by
  decide +kernel

theorem certRowC31_16_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC31_16 = true := by
  decide +kernel

theorem certRowC31_15_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC31_15 = true := by
  decide +kernel

theorem certRowC31_14_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC31_14 = true :=
  checkTree2_split_path (by decide) certRowC31_15_valid certRowC31_16_valid

theorem certRowC31_13_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC31_13 = true :=
  checkTree2_split_path (by decide) certRowC31_14_valid certRowC31_17_valid

theorem certRowC31_12_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC31_12 = true := by
  decide +kernel

theorem certRowC31_11_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC31_11 = true :=
  checkTree2_split_path (by decide) certRowC31_12_valid certRowC31_13_valid

theorem certRowC31_10_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC31_10 = true :=
  checkTree2_split_path (by decide) certRowC31_11_valid certRowC31_18_valid

theorem certRowC31_9_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC31_9 = true :=
  checkTree2_split_path (by decide) certRowC31_10_valid certRowC31_21_valid

theorem certRowC31_8_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC31_8 = true := by
  decide +kernel

theorem certRowC31_7_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC31_7 = true := by
  decide +kernel

theorem certRowC31_6_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -8], (0), 1, false)]) certRowC31_6 = true :=
  checkTree2_split_path (by decide) certRowC31_7_valid certRowC31_8_valid

theorem certRowC31_5_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -8], (0), 1, true)]) certRowC31_5 = true := by
  decide +kernel

theorem certRowC31_4_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC31_4 = true :=
  checkTree2_split_path (by decide) certRowC31_5_valid certRowC31_6_valid

theorem certRowC31_3_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC31_3 = true :=
  checkTree2_split_path (by decide) certRowC31_4_valid certRowC31_9_valid

theorem certRowC31_2_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC31_2 = true :=
  checkTree2_split_path (by decide) certRowC31_3_valid certRowC31_40_valid

theorem certRowC31_1_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC31_1 = true := by
  decide +kernel

theorem certRowC31_0_valid :
    checkTree2 17 19 cdD (pathCell (baseCell 8 9 2)
      []) certRowC31_0 = true :=
  checkTree2_split_path (by decide) certRowC31_1_valid certRowC31_2_valid

/-- (D, 8, 9). -/
theorem certRowC31_valid : rowC certRowC31 = true :=
  rowC_intro (by decide) (by decide) certRowC31_0_valid

theorem certRowC32_42_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC32_42 = true := by
  decide +kernel

theorem certRowC32_41_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC32_41 = true := by
  decide +kernel

theorem certRowC32_40_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC32_40 = true := by
  decide +kernel

theorem certRowC32_39_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC32_39 = true := by
  decide +kernel

theorem certRowC32_38_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC32_38 = true :=
  checkTree2_split_path (by decide) certRowC32_39_valid certRowC32_40_valid

theorem certRowC32_37_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC32_37 = true := by
  decide +kernel

theorem certRowC32_36_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC32_36 = true :=
  checkTree2_split_path (by decide) certRowC32_37_valid certRowC32_38_valid

theorem certRowC32_35_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC32_35 = true := by
  decide +kernel

theorem certRowC32_34_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC32_34 = true := by
  decide +kernel

theorem certRowC32_33_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC32_33 = true := by
  decide +kernel

theorem certRowC32_32_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC32_32 = true :=
  checkTree2_split_path (by decide) certRowC32_33_valid certRowC32_34_valid

theorem certRowC32_31_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC32_31 = true :=
  checkTree2_split_path (by decide) certRowC32_32_valid certRowC32_35_valid

theorem certRowC32_30_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC32_30 = true := by
  decide +kernel

theorem certRowC32_29_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC32_29 = true :=
  checkTree2_split_path (by decide) certRowC32_30_valid certRowC32_31_valid

theorem certRowC32_28_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC32_28 = true := by
  decide +kernel

theorem certRowC32_27_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC32_27 = true :=
  checkTree2_split_path (by decide) certRowC32_28_valid certRowC32_29_valid

theorem certRowC32_26_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC32_26 = true :=
  checkTree2_split_path (by decide) certRowC32_27_valid certRowC32_36_valid

theorem certRowC32_25_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC32_25 = true := by
  decide +kernel

theorem certRowC32_24_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC32_24 = true :=
  checkTree2_split_path (by decide) certRowC32_25_valid certRowC32_26_valid

theorem certRowC32_23_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC32_23 = true := by
  decide +kernel

theorem certRowC32_22_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC32_22 = true :=
  checkTree2_split_path (by decide) certRowC32_23_valid certRowC32_24_valid

theorem certRowC32_21_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC32_21 = true := by
  decide +kernel

theorem certRowC32_20_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC32_20 = true :=
  checkTree2_split_path (by decide) certRowC32_21_valid certRowC32_22_valid

theorem certRowC32_19_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC32_19 = true := by
  decide +kernel

theorem certRowC32_18_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC32_18 = true := by
  decide +kernel

theorem certRowC32_17_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC32_17 = true := by
  decide +kernel

theorem certRowC32_16_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC32_16 = true :=
  checkTree2_split_path (by decide) certRowC32_17_valid certRowC32_18_valid

theorem certRowC32_15_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC32_15 = true :=
  checkTree2_split_path (by decide) certRowC32_16_valid certRowC32_19_valid

theorem certRowC32_14_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC32_14 = true :=
  checkTree2_split_path (by decide) certRowC32_15_valid certRowC32_20_valid

theorem certRowC32_13_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC32_13 = true := by
  decide +kernel

theorem certRowC32_12_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC32_12 = true :=
  checkTree2_split_path (by decide) certRowC32_13_valid certRowC32_14_valid

theorem certRowC32_11_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC32_11 = true := by
  decide +kernel

theorem certRowC32_10_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC32_10 = true :=
  checkTree2_split_path (by decide) certRowC32_11_valid certRowC32_12_valid

theorem certRowC32_9_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC32_9 = true := by
  decide +kernel

theorem certRowC32_8_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC32_8 = true := by
  decide +kernel

theorem certRowC32_7_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC32_7 = true :=
  checkTree2_split_path (by decide) certRowC32_8_valid certRowC32_9_valid

theorem certRowC32_6_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC32_6 = true := by
  decide +kernel

theorem certRowC32_5_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC32_5 = true :=
  checkTree2_split_path (by decide) certRowC32_6_valid certRowC32_7_valid

theorem certRowC32_4_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC32_4 = true :=
  checkTree2_split_path (by decide) certRowC32_5_valid certRowC32_10_valid

theorem certRowC32_3_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC32_3 = true :=
  checkTree2_split_path (by decide) certRowC32_4_valid certRowC32_41_valid

theorem certRowC32_2_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC32_2 = true :=
  checkTree2_split_path (by decide) certRowC32_3_valid certRowC32_42_valid

theorem certRowC32_1_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC32_1 = true := by
  decide +kernel

theorem certRowC32_0_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 8 10 2)
      []) certRowC32_0 = true :=
  checkTree2_split_path (by decide) certRowC32_1_valid certRowC32_2_valid

/-- (D, 8, 10). -/
theorem certRowC32_valid : rowC certRowC32 = true :=
  rowC_intro (by decide) (by decide) certRowC32_0_valid

theorem certRowC33_26_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC33_26 = true := by
  decide +kernel

theorem certRowC33_25_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC33_25 = true := by
  decide +kernel

theorem certRowC33_24_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC33_24 = true := by
  decide +kernel

theorem certRowC33_23_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC33_23 = true := by
  decide +kernel

theorem certRowC33_22_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC33_22 = true :=
  checkTree2_split_path (by decide) certRowC33_23_valid certRowC33_24_valid

theorem certRowC33_21_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC33_21 = true := by
  decide +kernel

theorem certRowC33_20_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC33_20 = true :=
  checkTree2_split_path (by decide) certRowC33_21_valid certRowC33_22_valid

theorem certRowC33_19_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC33_19 = true :=
  checkTree2_split_path (by decide) certRowC33_20_valid certRowC33_25_valid

theorem certRowC33_18_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC33_18 = true := by
  decide +kernel

theorem certRowC33_17_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC33_17 = true :=
  checkTree2_split_path (by decide) certRowC33_18_valid certRowC33_19_valid

theorem certRowC33_16_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC33_16 = true := by
  decide +kernel

theorem certRowC33_15_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC33_15 = true :=
  checkTree2_split_path (by decide) certRowC33_16_valid certRowC33_17_valid

theorem certRowC33_14_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC33_14 = true :=
  checkTree2_split_path (by decide) certRowC33_15_valid certRowC33_26_valid

theorem certRowC33_13_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC33_13 = true := by
  decide +kernel

theorem certRowC33_12_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC33_12 = true :=
  checkTree2_split_path (by decide) certRowC33_13_valid certRowC33_14_valid

theorem certRowC33_11_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC33_11 = true := by
  decide +kernel

theorem certRowC33_10_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC33_10 = true := by
  decide +kernel

theorem certRowC33_9_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC33_9 = true := by
  decide +kernel

theorem certRowC33_8_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC33_8 = true :=
  checkTree2_split_path (by decide) certRowC33_9_valid certRowC33_10_valid

theorem certRowC33_7_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC33_7 = true := by
  decide +kernel

theorem certRowC33_6_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC33_6 = true :=
  checkTree2_split_path (by decide) certRowC33_7_valid certRowC33_8_valid

theorem certRowC33_5_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC33_5 = true :=
  checkTree2_split_path (by decide) certRowC33_6_valid certRowC33_11_valid

theorem certRowC33_4_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC33_4 = true :=
  checkTree2_split_path (by decide) certRowC33_5_valid certRowC33_12_valid

theorem certRowC33_3_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC33_3 = true := by
  decide +kernel

theorem certRowC33_2_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC33_2 = true :=
  checkTree2_split_path (by decide) certRowC33_3_valid certRowC33_4_valid

theorem certRowC33_1_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC33_1 = true := by
  decide +kernel

theorem certRowC33_0_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 8 11 2)
      []) certRowC33_0 = true :=
  checkTree2_split_path (by decide) certRowC33_1_valid certRowC33_2_valid

/-- (D, 8, 11). -/
theorem certRowC33_valid : rowC certRowC33 = true :=
  rowC_intro (by decide) (by decide) certRowC33_0_valid

theorem certRowC34_60_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_60 = true := by
  decide +kernel

theorem certRowC34_59_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_59 = true := by
  decide +kernel

theorem certRowC34_58_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_58 = true := by
  decide +kernel

theorem certRowC34_57_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_57 = true := by
  decide +kernel

theorem certRowC34_56_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_56 = true :=
  checkTree2_split_path (by decide) certRowC34_57_valid certRowC34_58_valid

theorem certRowC34_55_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC34_55 = true :=
  checkTree2_split_path (by decide) certRowC34_56_valid certRowC34_59_valid

theorem certRowC34_54_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC34_54 = true := by
  decide +kernel

theorem certRowC34_53_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_53 = true :=
  checkTree2_split_path (by decide) certRowC34_54_valid certRowC34_55_valid

theorem certRowC34_52_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_52 = true := by
  decide +kernel

theorem certRowC34_51_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC34_51 = true :=
  checkTree2_split_path (by decide) certRowC34_52_valid certRowC34_53_valid

theorem certRowC34_50_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC34_50 = true := by
  decide +kernel

theorem certRowC34_49_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC34_49 = true :=
  checkTree2_split_path (by decide) certRowC34_50_valid certRowC34_51_valid

theorem certRowC34_48_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC34_48 = true := by
  decide +kernel

theorem certRowC34_47_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC34_47 = true := by
  decide +kernel

theorem certRowC34_46_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC34_46 = true :=
  checkTree2_split_path (by decide) certRowC34_47_valid certRowC34_48_valid

theorem certRowC34_45_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC34_45 = true := by
  decide +kernel

theorem certRowC34_44_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC34_44 = true :=
  checkTree2_split_path (by decide) certRowC34_45_valid certRowC34_46_valid

theorem certRowC34_43_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_43 = true := by
  decide +kernel

theorem certRowC34_42_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_42 = true := by
  decide +kernel

theorem certRowC34_41_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_41 = true := by
  decide +kernel

theorem certRowC34_40_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_40 = true :=
  checkTree2_split_path (by decide) certRowC34_41_valid certRowC34_42_valid

theorem certRowC34_39_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC34_39 = true :=
  checkTree2_split_path (by decide) certRowC34_40_valid certRowC34_43_valid

theorem certRowC34_38_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC34_38 = true := by
  decide +kernel

theorem certRowC34_37_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC34_37 = true :=
  checkTree2_split_path (by decide) certRowC34_38_valid certRowC34_39_valid

theorem certRowC34_36_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC34_36 = true :=
  checkTree2_split_path (by decide) certRowC34_37_valid certRowC34_44_valid

theorem certRowC34_35_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC34_35 = true := by
  decide +kernel

theorem certRowC34_34_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC34_34 = true := by
  decide +kernel

theorem certRowC34_33_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC34_33 = true := by
  decide +kernel

theorem certRowC34_32_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC34_32 = true := by
  decide +kernel

theorem certRowC34_31_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC34_31 = true := by
  decide +kernel

theorem certRowC34_30_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC34_30 = true :=
  checkTree2_split_path (by decide) certRowC34_31_valid certRowC34_32_valid

theorem certRowC34_29_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC34_29 = true := by
  decide +kernel

theorem certRowC34_28_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC34_28 = true :=
  checkTree2_split_path (by decide) certRowC34_29_valid certRowC34_30_valid

theorem certRowC34_27_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC34_27 = true :=
  checkTree2_split_path (by decide) certRowC34_28_valid certRowC34_33_valid

theorem certRowC34_26_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC34_26 = true := by
  decide +kernel

theorem certRowC34_25_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC34_25 = true :=
  checkTree2_split_path (by decide) certRowC34_26_valid certRowC34_27_valid

theorem certRowC34_24_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC34_24 = true :=
  checkTree2_split_path (by decide) certRowC34_25_valid certRowC34_34_valid

theorem certRowC34_23_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC34_23 = true := by
  decide +kernel

theorem certRowC34_22_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC34_22 = true :=
  checkTree2_split_path (by decide) certRowC34_23_valid certRowC34_24_valid

theorem certRowC34_21_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC34_21 = true := by
  decide +kernel

theorem certRowC34_20_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC34_20 = true :=
  checkTree2_split_path (by decide) certRowC34_21_valid certRowC34_22_valid

theorem certRowC34_19_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC34_19 = true :=
  checkTree2_split_path (by decide) certRowC34_20_valid certRowC34_35_valid

theorem certRowC34_18_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC34_18 = true := by
  decide +kernel

theorem certRowC34_17_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC34_17 = true :=
  checkTree2_split_path (by decide) certRowC34_18_valid certRowC34_19_valid

theorem certRowC34_16_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC34_16 = true :=
  checkTree2_split_path (by decide) certRowC34_17_valid certRowC34_36_valid

theorem certRowC34_15_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_15 = true := by
  decide +kernel

theorem certRowC34_14_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_14 = true := by
  decide +kernel

theorem certRowC34_13_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC34_13 = true := by
  decide +kernel

theorem certRowC34_12_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC34_12 = true := by
  decide +kernel

theorem certRowC34_11_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_11 = true :=
  checkTree2_split_path (by decide) certRowC34_12_valid certRowC34_13_valid

theorem certRowC34_10_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC34_10 = true :=
  checkTree2_split_path (by decide) certRowC34_11_valid certRowC34_14_valid

theorem certRowC34_9_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC34_9 = true := by
  decide +kernel

theorem certRowC34_8_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_8 = true :=
  checkTree2_split_path (by decide) certRowC34_9_valid certRowC34_10_valid

theorem certRowC34_7_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC34_7 = true :=
  checkTree2_split_path (by decide) certRowC34_8_valid certRowC34_15_valid

theorem certRowC34_6_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC34_6 = true := by
  decide +kernel

theorem certRowC34_5_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC34_5 = true :=
  checkTree2_split_path (by decide) certRowC34_6_valid certRowC34_7_valid

theorem certRowC34_4_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC34_4 = true :=
  checkTree2_split_path (by decide) certRowC34_5_valid certRowC34_16_valid

theorem certRowC34_3_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_3 = true :=
  checkTree2_split_path (by decide) certRowC34_4_valid certRowC34_49_valid

theorem certRowC34_2_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC34_2 = true :=
  checkTree2_split_path (by decide) certRowC34_3_valid certRowC34_60_valid

theorem certRowC34_1_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC34_1 = true := by
  decide +kernel

theorem certRowC34_0_valid :
    checkTree2 18 20 cdD (pathCell (baseCell 9 9 2)
      []) certRowC34_0 = true :=
  checkTree2_split_path (by decide) certRowC34_1_valid certRowC34_2_valid

/-- (D, 9, 9). -/
theorem certRowC34_valid : rowC certRowC34 = true :=
  rowC_intro (by decide) (by decide) certRowC34_0_valid

theorem certRowC35_46_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC35_46 = true := by
  decide +kernel

theorem certRowC35_45_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC35_45 = true := by
  decide +kernel

theorem certRowC35_44_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC35_44 = true :=
  checkTree2_split_path (by decide) certRowC35_45_valid certRowC35_46_valid

theorem certRowC35_43_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC35_43 = true := by
  decide +kernel

theorem certRowC35_42_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC35_42 = true :=
  checkTree2_split_path (by decide) certRowC35_43_valid certRowC35_44_valid

theorem certRowC35_41_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC35_41 = true := by
  decide +kernel

theorem certRowC35_40_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC35_40 = true := by
  decide +kernel

theorem certRowC35_39_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC35_39 = true := by
  decide +kernel

theorem certRowC35_38_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC35_38 = true := by
  decide +kernel

theorem certRowC35_37_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC35_37 = true := by
  decide +kernel

theorem certRowC35_36_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC35_36 = true := by
  decide +kernel

theorem certRowC35_35_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC35_35 = true := by
  decide +kernel

theorem certRowC35_34_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC35_34 = true :=
  checkTree2_split_path (by decide) certRowC35_35_valid certRowC35_36_valid

theorem certRowC35_33_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC35_33 = true :=
  checkTree2_split_path (by decide) certRowC35_34_valid certRowC35_37_valid

theorem certRowC35_32_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC35_32 = true :=
  checkTree2_split_path (by decide) certRowC35_33_valid certRowC35_38_valid

theorem certRowC35_31_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC35_31 = true :=
  checkTree2_split_path (by decide) certRowC35_32_valid certRowC35_39_valid

theorem certRowC35_30_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC35_30 = true := by
  decide +kernel

theorem certRowC35_29_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC35_29 = true := by
  decide +kernel

theorem certRowC35_28_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC35_28 = true := by
  decide +kernel

theorem certRowC35_27_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC35_27 = true := by
  decide +kernel

theorem certRowC35_26_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC35_26 = true := by
  decide +kernel

theorem certRowC35_25_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC35_25 = true := by
  decide +kernel

theorem certRowC35_24_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC35_24 = true :=
  checkTree2_split_path (by decide) certRowC35_25_valid certRowC35_26_valid

theorem certRowC35_23_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC35_23 = true := by
  decide +kernel

theorem certRowC35_22_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC35_22 = true :=
  checkTree2_split_path (by decide) certRowC35_23_valid certRowC35_24_valid

theorem certRowC35_21_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC35_21 = true :=
  checkTree2_split_path (by decide) certRowC35_22_valid certRowC35_27_valid

theorem certRowC35_20_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC35_20 = true := by
  decide +kernel

theorem certRowC35_19_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC35_19 = true :=
  checkTree2_split_path (by decide) certRowC35_20_valid certRowC35_21_valid

theorem certRowC35_18_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC35_18 = true :=
  checkTree2_split_path (by decide) certRowC35_19_valid certRowC35_28_valid

theorem certRowC35_17_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC35_17 = true :=
  checkTree2_split_path (by decide) certRowC35_18_valid certRowC35_29_valid

theorem certRowC35_16_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC35_16 = true := by
  decide +kernel

theorem certRowC35_15_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC35_15 = true :=
  checkTree2_split_path (by decide) certRowC35_16_valid certRowC35_17_valid

theorem certRowC35_14_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC35_14 = true := by
  decide +kernel

theorem certRowC35_13_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC35_13 = true :=
  checkTree2_split_path (by decide) certRowC35_14_valid certRowC35_15_valid

theorem certRowC35_12_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC35_12 = true :=
  checkTree2_split_path (by decide) certRowC35_13_valid certRowC35_30_valid

theorem certRowC35_11_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC35_11 = true :=
  checkTree2_split_path (by decide) certRowC35_12_valid certRowC35_31_valid

theorem certRowC35_10_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC35_10 = true :=
  checkTree2_split_path (by decide) certRowC35_11_valid certRowC35_40_valid

theorem certRowC35_9_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC35_9 = true :=
  checkTree2_split_path (by decide) certRowC35_10_valid certRowC35_41_valid

theorem certRowC35_8_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC35_8 = true := by
  decide +kernel

theorem certRowC35_7_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC35_7 = true :=
  checkTree2_split_path (by decide) certRowC35_8_valid certRowC35_9_valid

theorem certRowC35_6_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC35_6 = true := by
  decide +kernel

theorem certRowC35_5_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC35_5 = true := by
  decide +kernel

theorem certRowC35_4_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC35_4 = true :=
  checkTree2_split_path (by decide) certRowC35_5_valid certRowC35_6_valid

theorem certRowC35_3_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC35_3 = true :=
  checkTree2_split_path (by decide) certRowC35_4_valid certRowC35_7_valid

theorem certRowC35_2_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC35_2 = true :=
  checkTree2_split_path (by decide) certRowC35_3_valid certRowC35_42_valid

theorem certRowC35_1_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC35_1 = true := by
  decide +kernel

theorem certRowC35_0_valid :
    checkTree2 19 21 cdD (pathCell (baseCell 9 10 2)
      []) certRowC35_0 = true :=
  checkTree2_split_path (by decide) certRowC35_1_valid certRowC35_2_valid

/-- (D, 9, 10). -/
theorem certRowC35_valid : rowC certRowC35 = true :=
  rowC_intro (by decide) (by decide) certRowC35_0_valid

theorem certRowC36_28_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC36_28 = true := by
  decide +kernel

theorem certRowC36_27_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC36_27 = true := by
  decide +kernel

theorem certRowC36_26_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC36_26 = true := by
  decide +kernel

theorem certRowC36_25_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC36_25 = true :=
  checkTree2_split_path (by decide) certRowC36_26_valid certRowC36_27_valid

theorem certRowC36_24_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC36_24 = true := by
  decide +kernel

theorem certRowC36_23_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC36_23 = true :=
  checkTree2_split_path (by decide) certRowC36_24_valid certRowC36_25_valid

theorem certRowC36_22_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC36_22 = true := by
  decide +kernel

theorem certRowC36_21_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC36_21 = true := by
  decide +kernel

theorem certRowC36_20_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC36_20 = true :=
  checkTree2_split_path (by decide) certRowC36_21_valid certRowC36_22_valid

theorem certRowC36_19_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC36_19 = true := by
  decide +kernel

theorem certRowC36_18_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC36_18 = true :=
  checkTree2_split_path (by decide) certRowC36_19_valid certRowC36_20_valid

theorem certRowC36_17_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC36_17 = true := by
  decide +kernel

theorem certRowC36_16_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC36_16 = true := by
  decide +kernel

theorem certRowC36_15_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC36_15 = true := by
  decide +kernel

theorem certRowC36_14_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC36_14 = true :=
  checkTree2_split_path (by decide) certRowC36_15_valid certRowC36_16_valid

theorem certRowC36_13_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC36_13 = true :=
  checkTree2_split_path (by decide) certRowC36_14_valid certRowC36_17_valid

theorem certRowC36_12_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC36_12 = true := by
  decide +kernel

theorem certRowC36_11_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC36_11 = true :=
  checkTree2_split_path (by decide) certRowC36_12_valid certRowC36_13_valid

theorem certRowC36_10_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC36_10 = true := by
  decide +kernel

theorem certRowC36_9_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC36_9 = true := by
  decide +kernel

theorem certRowC36_8_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC36_8 = true :=
  checkTree2_split_path (by decide) certRowC36_9_valid certRowC36_10_valid

theorem certRowC36_7_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC36_7 = true :=
  checkTree2_split_path (by decide) certRowC36_8_valid certRowC36_11_valid

theorem certRowC36_6_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC36_6 = true :=
  checkTree2_split_path (by decide) certRowC36_7_valid certRowC36_18_valid

theorem certRowC36_5_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC36_5 = true :=
  checkTree2_split_path (by decide) certRowC36_6_valid certRowC36_23_valid

theorem certRowC36_4_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC36_4 = true := by
  decide +kernel

theorem certRowC36_3_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC36_3 = true :=
  checkTree2_split_path (by decide) certRowC36_4_valid certRowC36_5_valid

theorem certRowC36_2_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC36_2 = true :=
  checkTree2_split_path (by decide) certRowC36_3_valid certRowC36_28_valid

theorem certRowC36_1_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC36_1 = true := by
  decide +kernel

theorem certRowC36_0_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 9 11 2)
      []) certRowC36_0 = true :=
  checkTree2_split_path (by decide) certRowC36_1_valid certRowC36_2_valid

/-- (D, 9, 11). -/
theorem certRowC36_valid : rowC certRowC36 = true :=
  rowC_intro (by decide) (by decide) certRowC36_0_valid

theorem certRowC37_110_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC37_110 = true := by
  decide +kernel

theorem certRowC37_109_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC37_109 = true := by
  decide +kernel

theorem certRowC37_108_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_108 = true := by
  decide +kernel

theorem certRowC37_107_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC37_107 = true := by
  decide +kernel

theorem certRowC37_106_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC37_106 = true := by
  decide +kernel

theorem certRowC37_105_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_105 = true := by
  decide +kernel

theorem certRowC37_104_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_104 = true := by
  decide +kernel

theorem certRowC37_103_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_103 = true := by
  decide +kernel

theorem certRowC37_102_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_102 = true := by
  decide +kernel

theorem certRowC37_101_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_101 = true := by
  decide +kernel

theorem certRowC37_100_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_100 = true := by
  decide +kernel

theorem certRowC37_99_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC37_99 = true := by
  decide +kernel

theorem certRowC37_98_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC37_98 = true := by
  decide +kernel

theorem certRowC37_97_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -8], (0), 1, false)]) certRowC37_97 = true :=
  checkTree2_split_path (by decide) certRowC37_98_valid certRowC37_99_valid

theorem certRowC37_96_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -8], (0), 1, true)]) certRowC37_96 = true := by
  decide +kernel

theorem certRowC37_95_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_95 = true :=
  checkTree2_split_path (by decide) certRowC37_96_valid certRowC37_97_valid

theorem certRowC37_94_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_94 = true :=
  checkTree2_split_path (by decide) certRowC37_95_valid certRowC37_100_valid

theorem certRowC37_93_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_93 = true := by
  decide +kernel

theorem certRowC37_92_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_92 = true :=
  checkTree2_split_path (by decide) certRowC37_93_valid certRowC37_94_valid

theorem certRowC37_91_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_91 = true :=
  checkTree2_split_path (by decide) certRowC37_92_valid certRowC37_101_valid

theorem certRowC37_90_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_90 = true :=
  checkTree2_split_path (by decide) certRowC37_91_valid certRowC37_102_valid

theorem certRowC37_89_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_89 = true := by
  decide +kernel

theorem certRowC37_88_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_88 = true :=
  checkTree2_split_path (by decide) certRowC37_89_valid certRowC37_90_valid

theorem certRowC37_87_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_87 = true :=
  checkTree2_split_path (by decide) certRowC37_88_valid certRowC37_103_valid

theorem certRowC37_86_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC37_86 = true :=
  checkTree2_split_path (by decide) certRowC37_87_valid certRowC37_104_valid

theorem certRowC37_85_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC37_85 = true := by
  decide +kernel

theorem certRowC37_84_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_84 = true :=
  checkTree2_split_path (by decide) certRowC37_85_valid certRowC37_86_valid

theorem certRowC37_83_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC37_83 = true :=
  checkTree2_split_path (by decide) certRowC37_84_valid certRowC37_105_valid

theorem certRowC37_82_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC37_82 = true := by
  decide +kernel

theorem certRowC37_81_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC37_81 = true :=
  checkTree2_split_path (by decide) certRowC37_82_valid certRowC37_83_valid

theorem certRowC37_80_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC37_80 = true :=
  checkTree2_split_path (by decide) certRowC37_81_valid certRowC37_106_valid

theorem certRowC37_79_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC37_79 = true := by
  decide +kernel

theorem certRowC37_78_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC37_78 = true :=
  checkTree2_split_path (by decide) certRowC37_79_valid certRowC37_80_valid

theorem certRowC37_77_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_77 = true :=
  checkTree2_split_path (by decide) certRowC37_78_valid certRowC37_107_valid

theorem certRowC37_76_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_76 = true := by
  decide +kernel

theorem certRowC37_75_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_75 = true := by
  decide +kernel

theorem certRowC37_74_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_74 = true :=
  checkTree2_split_path (by decide) certRowC37_75_valid certRowC37_76_valid

theorem certRowC37_73_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_73 = true :=
  checkTree2_split_path (by decide) certRowC37_74_valid certRowC37_77_valid

theorem certRowC37_72_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_72 = true := by
  decide +kernel

theorem certRowC37_71_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_71 = true :=
  checkTree2_split_path (by decide) certRowC37_72_valid certRowC37_73_valid

theorem certRowC37_70_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC37_70 = true :=
  checkTree2_split_path (by decide) certRowC37_71_valid certRowC37_108_valid

theorem certRowC37_69_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC37_69 = true := by
  decide +kernel

theorem certRowC37_68_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_68 = true :=
  checkTree2_split_path (by decide) certRowC37_69_valid certRowC37_70_valid

theorem certRowC37_67_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_67 = true := by
  decide +kernel

theorem certRowC37_66_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_66 = true :=
  checkTree2_split_path (by decide) certRowC37_67_valid certRowC37_68_valid

theorem certRowC37_65_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_65 = true := by
  decide +kernel

theorem certRowC37_64_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC37_64 = true :=
  checkTree2_split_path (by decide) certRowC37_65_valid certRowC37_66_valid

theorem certRowC37_63_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC37_63 = true :=
  checkTree2_split_path (by decide) certRowC37_64_valid certRowC37_109_valid

theorem certRowC37_62_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_62 = true :=
  checkTree2_split_path (by decide) certRowC37_63_valid certRowC37_110_valid

theorem certRowC37_61_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_61 = true := by
  decide +kernel

theorem certRowC37_60_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_60 = true := by
  decide +kernel

theorem certRowC37_59_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_59 = true := by
  decide +kernel

theorem certRowC37_58_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_58 = true := by
  decide +kernel

theorem certRowC37_57_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_57 = true := by
  decide +kernel

theorem certRowC37_56_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_56 = true :=
  checkTree2_split_path (by decide) certRowC37_57_valid certRowC37_58_valid

theorem certRowC37_55_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_55 = true :=
  checkTree2_split_path (by decide) certRowC37_56_valid certRowC37_59_valid

theorem certRowC37_54_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_54 = true :=
  checkTree2_split_path (by decide) certRowC37_55_valid certRowC37_60_valid

theorem certRowC37_53_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_53 = true :=
  checkTree2_split_path (by decide) certRowC37_54_valid certRowC37_61_valid

theorem certRowC37_52_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_52 = true := by
  decide +kernel

theorem certRowC37_51_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_51 = true :=
  checkTree2_split_path (by decide) certRowC37_52_valid certRowC37_53_valid

theorem certRowC37_50_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_50 = true := by
  decide +kernel

theorem certRowC37_49_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_49 = true := by
  decide +kernel

theorem certRowC37_48_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_48 = true :=
  checkTree2_split_path (by decide) certRowC37_49_valid certRowC37_50_valid

theorem certRowC37_47_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_47 = true :=
  checkTree2_split_path (by decide) certRowC37_48_valid certRowC37_51_valid

theorem certRowC37_46_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC37_46 = true := by
  decide +kernel

theorem certRowC37_45_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC37_45 = true := by
  decide +kernel

theorem certRowC37_44_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_44 = true :=
  checkTree2_split_path (by decide) certRowC37_45_valid certRowC37_46_valid

theorem certRowC37_43_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_43 = true :=
  checkTree2_split_path (by decide) certRowC37_44_valid certRowC37_47_valid

theorem certRowC37_42_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_42 = true := by
  decide +kernel

theorem certRowC37_41_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC37_41 = true := by
  decide +kernel

theorem certRowC37_40_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_40 = true := by
  decide +kernel

theorem certRowC37_39_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_39 = true := by
  decide +kernel

theorem certRowC37_38_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_38 = true := by
  decide +kernel

theorem certRowC37_37_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC37_37 = true :=
  checkTree2_split_path (by decide) certRowC37_38_valid certRowC37_39_valid

theorem certRowC37_36_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC37_36 = true := by
  decide +kernel

theorem certRowC37_35_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_35 = true :=
  checkTree2_split_path (by decide) certRowC37_36_valid certRowC37_37_valid

theorem certRowC37_34_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false), ([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC37_34 = true :=
  checkTree2_split_path (by decide) certRowC37_35_valid certRowC37_40_valid

theorem certRowC37_33_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC37_33 = true :=
  checkTree2_split_path (by decide) certRowC37_34_valid certRowC37_41_valid

theorem certRowC37_32_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_32 = true := by
  decide +kernel

theorem certRowC37_31_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_31 = true := by
  decide +kernel

theorem certRowC37_30_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC37_30 = true :=
  checkTree2_split_path (by decide) certRowC37_31_valid certRowC37_32_valid

theorem certRowC37_29_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_29 = true :=
  checkTree2_split_path (by decide) certRowC37_30_valid certRowC37_33_valid

theorem certRowC37_28_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_28 = true := by
  decide +kernel

theorem certRowC37_27_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_27 = true := by
  decide +kernel

theorem certRowC37_26_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC37_26 = true :=
  checkTree2_split_path (by decide) certRowC37_27_valid certRowC37_28_valid

theorem certRowC37_25_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC37_25 = true := by
  decide +kernel

theorem certRowC37_24_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC37_24 = true :=
  checkTree2_split_path (by decide) certRowC37_25_valid certRowC37_26_valid

theorem certRowC37_23_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC37_23 = true := by
  decide +kernel

theorem certRowC37_22_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_22 = true :=
  checkTree2_split_path (by decide) certRowC37_23_valid certRowC37_24_valid

theorem certRowC37_21_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_21 = true :=
  checkTree2_split_path (by decide) certRowC37_22_valid certRowC37_29_valid

theorem certRowC37_20_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_20 = true :=
  checkTree2_split_path (by decide) certRowC37_21_valid certRowC37_42_valid

theorem certRowC37_19_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_19 = true :=
  checkTree2_split_path (by decide) certRowC37_20_valid certRowC37_43_valid

theorem certRowC37_18_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_18 = true := by
  decide +kernel

theorem certRowC37_17_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC37_17 = true := by
  decide +kernel

theorem certRowC37_16_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_16 = true := by
  decide +kernel

theorem certRowC37_15_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_15 = true := by
  decide +kernel

theorem certRowC37_14_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC37_14 = true := by
  decide +kernel

theorem certRowC37_13_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_13 = true := by
  decide +kernel

theorem certRowC37_12_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_12 = true :=
  checkTree2_split_path (by decide) certRowC37_13_valid certRowC37_14_valid

theorem certRowC37_11_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_11 = true :=
  checkTree2_split_path (by decide) certRowC37_12_valid certRowC37_15_valid

theorem certRowC37_10_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC37_10 = true :=
  checkTree2_split_path (by decide) certRowC37_11_valid certRowC37_16_valid

theorem certRowC37_9_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC37_9 = true :=
  checkTree2_split_path (by decide) certRowC37_10_valid certRowC37_17_valid

theorem certRowC37_8_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_8 = true := by
  decide +kernel

theorem certRowC37_7_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false), ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_7 = true :=
  checkTree2_split_path (by decide) certRowC37_8_valid certRowC37_9_valid

theorem certRowC37_6_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, false)]) certRowC37_6 = true :=
  checkTree2_split_path (by decide) certRowC37_7_valid certRowC37_18_valid

theorem certRowC37_5_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -8], (0), 1, true)]) certRowC37_5 = true := by
  decide +kernel

theorem certRowC37_4_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC37_4 = true :=
  checkTree2_split_path (by decide) certRowC37_5_valid certRowC37_6_valid

theorem certRowC37_3_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC37_3 = true :=
  checkTree2_split_path (by decide) certRowC37_4_valid certRowC37_19_valid

theorem certRowC37_2_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC37_2 = true :=
  checkTree2_split_path (by decide) certRowC37_3_valid certRowC37_62_valid

theorem certRowC37_1_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC37_1 = true := by
  decide +kernel

theorem certRowC37_0_valid :
    checkTree2 20 22 cdD (pathCell (baseCell 10 10 2)
      []) certRowC37_0 = true :=
  checkTree2_split_path (by decide) certRowC37_1_valid certRowC37_2_valid

/-- (D, 10, 10). -/
theorem certRowC37_valid : rowC certRowC37 = true :=
  rowC_intro (by decide) (by decide) certRowC37_0_valid

theorem certRowC38_28_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC38_28 = true := by
  decide +kernel

theorem certRowC38_27_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC38_27 = true := by
  decide +kernel

theorem certRowC38_26_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC38_26 = true := by
  decide +kernel

theorem certRowC38_25_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC38_25 = true := by
  decide +kernel

theorem certRowC38_24_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC38_24 = true :=
  checkTree2_split_path (by decide) certRowC38_25_valid certRowC38_26_valid

theorem certRowC38_23_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC38_23 = true := by
  decide +kernel

theorem certRowC38_22_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC38_22 = true :=
  checkTree2_split_path (by decide) certRowC38_23_valid certRowC38_24_valid

theorem certRowC38_21_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC38_21 = true := by
  decide +kernel

theorem certRowC38_20_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC38_20 = true :=
  checkTree2_split_path (by decide) certRowC38_21_valid certRowC38_22_valid

theorem certRowC38_19_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC38_19 = true :=
  checkTree2_split_path (by decide) certRowC38_20_valid certRowC38_27_valid

theorem certRowC38_18_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC38_18 = true := by
  decide +kernel

theorem certRowC38_17_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC38_17 = true :=
  checkTree2_split_path (by decide) certRowC38_18_valid certRowC38_19_valid

theorem certRowC38_16_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC38_16 = true := by
  decide +kernel

theorem certRowC38_15_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC38_15 = true := by
  decide +kernel

theorem certRowC38_14_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC38_14 = true := by
  decide +kernel

theorem certRowC38_13_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, false)]) certRowC38_13 = true :=
  checkTree2_split_path (by decide) certRowC38_14_valid certRowC38_15_valid

theorem certRowC38_12_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, -4], (163999999), 10000000000, true)]) certRowC38_12 = true := by
  decide +kernel

theorem certRowC38_11_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC38_11 = true :=
  checkTree2_split_path (by decide) certRowC38_12_valid certRowC38_13_valid

theorem certRowC38_10_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC38_10 = true := by
  decide +kernel

theorem certRowC38_9_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC38_9 = true := by
  decide +kernel

theorem certRowC38_8_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC38_8 = true :=
  checkTree2_split_path (by decide) certRowC38_9_valid certRowC38_10_valid

theorem certRowC38_7_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC38_7 = true :=
  checkTree2_split_path (by decide) certRowC38_8_valid certRowC38_11_valid

theorem certRowC38_6_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, false)]) certRowC38_6 = true :=
  checkTree2_split_path (by decide) certRowC38_7_valid certRowC38_16_valid

theorem certRowC38_5_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -8], (0), 1, true)]) certRowC38_5 = true := by
  decide +kernel

theorem certRowC38_4_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC38_4 = true :=
  checkTree2_split_path (by decide) certRowC38_5_valid certRowC38_6_valid

theorem certRowC38_3_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC38_3 = true :=
  checkTree2_split_path (by decide) certRowC38_4_valid certRowC38_17_valid

theorem certRowC38_2_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC38_2 = true :=
  checkTree2_split_path (by decide) certRowC38_3_valid certRowC38_28_valid

theorem certRowC38_1_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC38_1 = true := by
  decide +kernel

theorem certRowC38_0_valid :
    checkTree2 21 23 cdD (pathCell (baseCell 10 11 2)
      []) certRowC38_0 = true :=
  checkTree2_split_path (by decide) certRowC38_1_valid certRowC38_2_valid

/-- (D, 10, 11). -/
theorem certRowC38_valid : rowC certRowC38 = true :=
  rowC_intro (by decide) (by decide) certRowC38_0_valid

theorem certRowC39_36_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC39_36 = true := by
  decide +kernel

theorem certRowC39_35_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC39_35 = true := by
  decide +kernel

theorem certRowC39_34_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC39_34 = true := by
  decide +kernel

theorem certRowC39_33_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC39_33 = true := by
  decide +kernel

theorem certRowC39_32_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC39_32 = true :=
  checkTree2_split_path (by decide) certRowC39_33_valid certRowC39_34_valid

theorem certRowC39_31_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC39_31 = true := by
  decide +kernel

theorem certRowC39_30_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC39_30 = true :=
  checkTree2_split_path (by decide) certRowC39_31_valid certRowC39_32_valid

theorem certRowC39_29_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC39_29 = true := by
  decide +kernel

theorem certRowC39_28_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC39_28 = true :=
  checkTree2_split_path (by decide) certRowC39_29_valid certRowC39_30_valid

theorem certRowC39_27_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC39_27 = true := by
  decide +kernel

theorem certRowC39_26_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC39_26 = true :=
  checkTree2_split_path (by decide) certRowC39_27_valid certRowC39_28_valid

theorem certRowC39_25_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC39_25 = true := by
  decide +kernel

theorem certRowC39_24_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC39_24 = true :=
  checkTree2_split_path (by decide) certRowC39_25_valid certRowC39_26_valid

theorem certRowC39_23_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC39_23 = true :=
  checkTree2_split_path (by decide) certRowC39_24_valid certRowC39_35_valid

theorem certRowC39_22_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC39_22 = true := by
  decide +kernel

theorem certRowC39_21_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC39_21 = true :=
  checkTree2_split_path (by decide) certRowC39_22_valid certRowC39_23_valid

theorem certRowC39_20_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC39_20 = true :=
  checkTree2_split_path (by decide) certRowC39_21_valid certRowC39_36_valid

theorem certRowC39_19_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC39_19 = true := by
  decide +kernel

theorem certRowC39_18_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC39_18 = true :=
  checkTree2_split_path (by decide) certRowC39_19_valid certRowC39_20_valid

theorem certRowC39_17_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC39_17 = true := by
  decide +kernel

theorem certRowC39_16_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC39_16 = true :=
  checkTree2_split_path (by decide) certRowC39_17_valid certRowC39_18_valid

theorem certRowC39_15_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC39_15 = true := by
  decide +kernel

theorem certRowC39_14_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC39_14 = true :=
  checkTree2_split_path (by decide) certRowC39_15_valid certRowC39_16_valid

theorem certRowC39_13_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC39_13 = true := by
  decide +kernel

theorem certRowC39_12_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC39_12 = true := by
  decide +kernel

theorem certRowC39_11_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC39_11 = true :=
  checkTree2_split_path (by decide) certRowC39_12_valid certRowC39_13_valid

theorem certRowC39_10_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC39_10 = true := by
  decide +kernel

theorem certRowC39_9_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC39_9 = true := by
  decide +kernel

theorem certRowC39_8_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC39_8 = true := by
  decide +kernel

theorem certRowC39_7_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false), ([0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC39_7 = true :=
  checkTree2_split_path (by decide) certRowC39_8_valid certRowC39_9_valid

theorem certRowC39_6_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, false)]) certRowC39_6 = true :=
  checkTree2_split_path (by decide) certRowC39_7_valid certRowC39_10_valid

theorem certRowC39_5_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -8], (0), 1, true)]) certRowC39_5 = true := by
  decide +kernel

theorem certRowC39_4_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC39_4 = true :=
  checkTree2_split_path (by decide) certRowC39_5_valid certRowC39_6_valid

theorem certRowC39_3_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC39_3 = true :=
  checkTree2_split_path (by decide) certRowC39_4_valid certRowC39_11_valid

theorem certRowC39_2_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC39_2 = true :=
  checkTree2_split_path (by decide) certRowC39_3_valid certRowC39_14_valid

theorem certRowC39_1_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC39_1 = true := by
  decide +kernel

theorem certRowC39_0_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 10 12 2)
      []) certRowC39_0 = true :=
  checkTree2_split_path (by decide) certRowC39_1_valid certRowC39_2_valid

/-- (D, 10, 12). -/
theorem certRowC39_valid : rowC certRowC39 = true :=
  rowC_intro (by decide) (by decide) certRowC39_0_valid

theorem certRowC40_36_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC40_36 = true := by
  decide +kernel

theorem certRowC40_35_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC40_35 = true := by
  decide +kernel

theorem certRowC40_34_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC40_34 = true := by
  decide +kernel

theorem certRowC40_33_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC40_33 = true := by
  decide +kernel

theorem certRowC40_32_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC40_32 = true := by
  decide +kernel

theorem certRowC40_31_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC40_31 = true := by
  decide +kernel

theorem certRowC40_30_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC40_30 = true := by
  decide +kernel

theorem certRowC40_29_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC40_29 = true :=
  checkTree2_split_path (by decide) certRowC40_30_valid certRowC40_31_valid

theorem certRowC40_28_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC40_28 = true := by
  decide +kernel

theorem certRowC40_27_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC40_27 = true :=
  checkTree2_split_path (by decide) certRowC40_28_valid certRowC40_29_valid

theorem certRowC40_26_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC40_26 = true :=
  checkTree2_split_path (by decide) certRowC40_27_valid certRowC40_32_valid

theorem certRowC40_25_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC40_25 = true :=
  checkTree2_split_path (by decide) certRowC40_26_valid certRowC40_33_valid

theorem certRowC40_24_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC40_24 = true :=
  checkTree2_split_path (by decide) certRowC40_25_valid certRowC40_34_valid

theorem certRowC40_23_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC40_23 = true := by
  decide +kernel

theorem certRowC40_22_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC40_22 = true := by
  decide +kernel

theorem certRowC40_21_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC40_21 = true := by
  decide +kernel

theorem certRowC40_20_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC40_20 = true :=
  checkTree2_split_path (by decide) certRowC40_21_valid certRowC40_22_valid

theorem certRowC40_19_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC40_19 = true := by
  decide +kernel

theorem certRowC40_18_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC40_18 = true :=
  checkTree2_split_path (by decide) certRowC40_19_valid certRowC40_20_valid

theorem certRowC40_17_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC40_17 = true :=
  checkTree2_split_path (by decide) certRowC40_18_valid certRowC40_23_valid

theorem certRowC40_16_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC40_16 = true := by
  decide +kernel

theorem certRowC40_15_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC40_15 = true :=
  checkTree2_split_path (by decide) certRowC40_16_valid certRowC40_17_valid

theorem certRowC40_14_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC40_14 = true := by
  decide +kernel

theorem certRowC40_13_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC40_13 = true :=
  checkTree2_split_path (by decide) certRowC40_14_valid certRowC40_15_valid

theorem certRowC40_12_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC40_12 = true :=
  checkTree2_split_path (by decide) certRowC40_13_valid certRowC40_24_valid

theorem certRowC40_11_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC40_11 = true := by
  decide +kernel

theorem certRowC40_10_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC40_10 = true :=
  checkTree2_split_path (by decide) certRowC40_11_valid certRowC40_12_valid

theorem certRowC40_9_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC40_9 = true := by
  decide +kernel

theorem certRowC40_8_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC40_8 = true :=
  checkTree2_split_path (by decide) certRowC40_9_valid certRowC40_10_valid

theorem certRowC40_7_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC40_7 = true := by
  decide +kernel

theorem certRowC40_6_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC40_6 = true :=
  checkTree2_split_path (by decide) certRowC40_7_valid certRowC40_8_valid

theorem certRowC40_5_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC40_5 = true :=
  checkTree2_split_path (by decide) certRowC40_6_valid certRowC40_35_valid

theorem certRowC40_4_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC40_4 = true := by
  decide +kernel

theorem certRowC40_3_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC40_3 = true :=
  checkTree2_split_path (by decide) certRowC40_4_valid certRowC40_5_valid

theorem certRowC40_2_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC40_2 = true :=
  checkTree2_split_path (by decide) certRowC40_3_valid certRowC40_36_valid

theorem certRowC40_1_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC40_1 = true := by
  decide +kernel

theorem certRowC40_0_valid :
    checkTree2 22 24 cdD (pathCell (baseCell 11 11 2)
      []) certRowC40_0 = true :=
  checkTree2_split_path (by decide) certRowC40_1_valid certRowC40_2_valid

/-- (D, 11, 11). -/
theorem certRowC40_valid : rowC certRowC40 = true :=
  rowC_intro (by decide) (by decide) certRowC40_0_valid

theorem certRowC41_22_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC41_22 = true := by
  decide +kernel

theorem certRowC41_21_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC41_21 = true := by
  decide +kernel

theorem certRowC41_20_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC41_20 = true := by
  decide +kernel

theorem certRowC41_19_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC41_19 = true := by
  decide +kernel

theorem certRowC41_18_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC41_18 = true :=
  checkTree2_split_path (by decide) certRowC41_19_valid certRowC41_20_valid

theorem certRowC41_17_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC41_17 = true := by
  decide +kernel

theorem certRowC41_16_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC41_16 = true :=
  checkTree2_split_path (by decide) certRowC41_17_valid certRowC41_18_valid

theorem certRowC41_15_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC41_15 = true := by
  decide +kernel

theorem certRowC41_14_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC41_14 = true := by
  decide +kernel

theorem certRowC41_13_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC41_13 = true :=
  checkTree2_split_path (by decide) certRowC41_14_valid certRowC41_15_valid

theorem certRowC41_12_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC41_12 = true :=
  checkTree2_split_path (by decide) certRowC41_13_valid certRowC41_16_valid

theorem certRowC41_11_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC41_11 = true := by
  decide +kernel

theorem certRowC41_10_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC41_10 = true :=
  checkTree2_split_path (by decide) certRowC41_11_valid certRowC41_12_valid

theorem certRowC41_9_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC41_9 = true :=
  checkTree2_split_path (by decide) certRowC41_10_valid certRowC41_21_valid

theorem certRowC41_8_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC41_8 = true := by
  decide +kernel

theorem certRowC41_7_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC41_7 = true := by
  decide +kernel

theorem certRowC41_6_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC41_6 = true :=
  checkTree2_split_path (by decide) certRowC41_7_valid certRowC41_8_valid

theorem certRowC41_5_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC41_5 = true :=
  checkTree2_split_path (by decide) certRowC41_6_valid certRowC41_9_valid

theorem certRowC41_4_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC41_4 = true := by
  decide +kernel

theorem certRowC41_3_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC41_3 = true :=
  checkTree2_split_path (by decide) certRowC41_4_valid certRowC41_5_valid

theorem certRowC41_2_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true), ([1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC41_2 = true := by
  decide +kernel

theorem certRowC41_1_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      [([0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC41_1 = true :=
  checkTree2_split_path (by decide) certRowC41_2_valid certRowC41_3_valid

theorem certRowC41_0_valid :
    checkTree2 23 25 cdD (pathCell (baseCell 11 12 2)
      []) certRowC41_0 = true :=
  checkTree2_split_path (by decide) certRowC41_1_valid certRowC41_22_valid

/-- (D, 11, 12). -/
theorem certRowC41_valid : rowC certRowC41 = true :=
  rowC_intro (by decide) (by decide) certRowC41_0_valid

theorem certRowC42_22_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, false)]) certRowC42_22 = true := by
  decide +kernel

theorem certRowC42_21_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC42_21 = true := by
  decide +kernel

theorem certRowC42_20_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC42_20 = true := by
  decide +kernel

theorem certRowC42_19_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC42_19 = true := by
  decide +kernel

theorem certRowC42_18_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC42_18 = true :=
  checkTree2_split_path (by decide) certRowC42_19_valid certRowC42_20_valid

theorem certRowC42_17_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false), ([1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC42_17 = true := by
  decide +kernel

theorem certRowC42_16_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, false)]) certRowC42_16 = true :=
  checkTree2_split_path (by decide) certRowC42_17_valid certRowC42_18_valid

theorem certRowC42_15_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], (0), 1, true)]) certRowC42_15 = true := by
  decide +kernel

theorem certRowC42_14_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC42_14 = true :=
  checkTree2_split_path (by decide) certRowC42_15_valid certRowC42_16_valid

theorem certRowC42_13_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true), ([1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC42_13 = true := by
  decide +kernel

theorem certRowC42_12_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC42_12 = true :=
  checkTree2_split_path (by decide) certRowC42_13_valid certRowC42_14_valid

theorem certRowC42_11_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, false)]) certRowC42_11 = true :=
  checkTree2_split_path (by decide) certRowC42_12_valid certRowC42_21_valid

theorem certRowC42_10_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2], (4999999999), 10000000000, true)]) certRowC42_10 = true := by
  decide +kernel

theorem certRowC42_9_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, false)]) certRowC42_9 = true :=
  checkTree2_split_path (by decide) certRowC42_10_valid certRowC42_11_valid

theorem certRowC42_8_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -4], (163999999), 10000000000, true)]) certRowC42_8 = true := by
  decide +kernel

theorem certRowC42_7_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, false)]) certRowC42_7 = true :=
  checkTree2_split_path (by decide) certRowC42_8_valid certRowC42_9_valid

theorem certRowC42_6_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false), ([1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 8], (-328000001), 10000000000, true)]) certRowC42_6 = true := by
  decide +kernel

theorem certRowC42_5_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, false)]) certRowC42_5 = true :=
  checkTree2_split_path (by decide) certRowC42_6_valid certRowC42_7_valid

theorem certRowC42_4_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false), ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -4], (163999999), 10000000000, true)]) certRowC42_4 = true := by
  decide +kernel

theorem certRowC42_3_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, false)]) certRowC42_3 = true :=
  checkTree2_split_path (by decide) certRowC42_4_valid certRowC42_5_valid

theorem certRowC42_2_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true), ([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2], (4999999999), 10000000000, true)]) certRowC42_2 = true := by
  decide +kernel

theorem certRowC42_1_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      [([1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, -1, 8], (-328000001), 10000000000, true)]) certRowC42_1 = true :=
  checkTree2_split_path (by decide) certRowC42_2_valid certRowC42_3_valid

theorem certRowC42_0_valid :
    checkTree2 24 26 cdD (pathCell (baseCell 12 12 2)
      []) certRowC42_0 = true :=
  checkTree2_split_path (by decide) certRowC42_1_valid certRowC42_22_valid

/-- (D, 12, 12). -/
theorem certRowC42_valid : rowC certRowC42 = true :=
  rowC_intro (by decide) (by decide) certRowC42_0_valid

end BGP212.PackingCert
