#!/usr/bin/env python3
"""Positive and negative controls for V2d (Lemma 9.2, the J_T fibre theorem).

Writes Lean files into the given directory (default /tmp/v2d_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected.

  ok_endpoint / nc_endpoint_Cs   one coordinate (n = 0) at Table 3: U = min(L, max(g, C(1))) =
                                 777/1250, so u = 3/5 lies in the fibre; the nc file uses the
                                 endpoint with C(s) in place of C(s+1) (U = g), which excludes it.
  ok_endpoint_value / nc_endpoint_value
                                 U(∅) = 777/1250 at Table 3; the nc file claims g = 41/625.
  ok_capstep_needed / nc_capstep a cap function with C(1) = 1/10, C(2) = 1 (step 9/10 > g):
                                 x̂ = (1/5) violates its cap, yet (x̂, 1/2) ∈ T̃; the nc file
                                 claims the fibre is empty (empty_fibre_cap without CapStep).
  ok_cap0_needed / nc_cap0       C(0) = −1: the empty x̂ violates its cap, yet (∅, 1/2) ∈ T̃; the
                                 nc file claims the fibre is empty (without 0 ≤ C 0).

Usage: python3 -I specs/checks/fibre_v2d_controls.py [dir]
Check: for f in DIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
"""
import os
import sys

OUT = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v2d_ctl"
os.makedirs(OUT, exist_ok=True)

HEAD = """import Solution.Fibre

open BGP212.Gram BGP212.V2d

noncomputable def Ct : ℕ → ℝ := fun m => (BGP212.Params.C m : ℝ)

theorem hat0 : (Fin.elim0 : Fin 0 → ℝ) ∈ hatSupport 0 (41 / 625) (249 / 250) Ct := by
  refine ⟨fun i => Fin.elim0 i, by simp; norm_num, ?_⟩
  simp [roughMass_eq, roughCount_eq, Ct]
  decide +kernel

theorem endpoint0 : endpoint (41 / 625) (53 / 50) Ct (Fin.elim0 : Fin 0 → ℝ) = 777 / 1250 := by
  have h1 : (BGP212.Params.C 1 : ℝ) = 777 / 1250 := by
    have : BGP212.Params.C 1 = 777 / 1250 := by decide +kernel
    rw [this]; norm_num
  simp [endpoint, roughMass_eq, roughCount_eq, Ct, h1]
  norm_num

"""

FIBRE = """theorem ctl : {CLAIM} := by
  rw [fibre_equiv 0 (41 / 625) (53 / 50) (249 / 250) Ct (by norm_num) (by norm_num) _ hat0]
  {TAIL}
"""

VALUE = """theorem ctl : endpoint (41 / 625) (53 / 50) Ct (Fin.elim0 : Fin 0 → ℝ) = {V} := by
  rw [endpoint0]
  all_goals norm_num
"""

STEP = """noncomputable def Cbad : ℕ → ℝ := fun m => if m = 0 then 0 else if m = 1 then 1 / 10 else 1

theorem ctl : {CLAIM} := by
  rw [mem_supportT_snoc]
  simp [roughMass_eq, roughCount_eq, Cbad]
  all_goals norm_num
"""

ZERO = """noncomputable def Cneg : ℕ → ℝ := fun m => if m = 0 then -1 else 1

theorem ctl : {CLAIM} := by
  rw [mem_supportT_snoc]
  simp [roughMass_eq, roughCount_eq, Cneg]
  all_goals norm_num
"""

mem0 = "Fin.snoc (Fin.elim0 : Fin 0 → ℝ) (3 / 5) {R} supportT 1 (41 / 625) (53 / 50) Ct"
step = "Fin.snoc (![1 / 5] : Fin 1 → ℝ) (1 / 2) {R} supportT 2 (41 / 625) (53 / 50) Cbad"
zero = "Fin.snoc (Fin.elim0 : Fin 0 → ℝ) (1 / 2) {R} supportT 1 (41 / 625) (53 / 50) Cneg"

files = {
    "ok_endpoint": FIBRE.replace("{CLAIM}", mem0.replace("{R}", "∈"))
        .replace("{TAIL}", "rw [endpoint0]; norm_num"),
    # the endpoint with C(s) = C(0) in place of C(s+1) would be max g (C 0) = g < 3/5
    "nc_endpoint_Cs": FIBRE.replace("{CLAIM}", mem0.replace("{R}", "∉"))
        .replace("{TAIL}", "rw [endpoint0]; norm_num"),
    "ok_endpoint_value": VALUE.replace("{V}", "777 / 1250"),
    "nc_endpoint_value": VALUE.replace("{V}", "41 / 625"),
    "ok_capstep_needed": STEP.replace("{CLAIM}", step.replace("{R}", "∈")),
    "nc_capstep": STEP.replace("{CLAIM}", step.replace("{R}", "∉")),
    "ok_cap0_needed": ZERO.replace("{CLAIM}", zero.replace("{R}", "∈")),
    "nc_cap0": ZERO.replace("{CLAIM}", zero.replace("{R}", "∉")),
}
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
