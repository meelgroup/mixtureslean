/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The FPRAS parameter schedule for the mixture running time

This file performs the purely arithmetic substitution of the FPRAS calibration
`δ = ε/(3n)`, `η' = η/n`, `d = 2k` into the Cohen–Peng row count
`m = sampleSize (2k) C δ η'` and, in a second lemma, assembles the per-step
operation count of the domain-reduction dynamic program.  It mirrors
`approxbdd/nfa/tods/nfalean/ApproxNFA/Cost/Schedule.lean` (`thetaD_le`, …): a
`Nat.ceil → real` bound followed by the per-iteration cost bound, keeping
`Real.log` explicit throughout and collecting the polynomial with
`gcongr`/`nlinarith`/`positivity`.

The two headline results:

* `sampleSize_bound` — `m ≤ C·(2k)·log(2k)·(9n²/ε²)·log(n/η) + 1`, the schedule
  substitution of `δ⁻² = (3n/ε)² = 9n²/ε²` and `log(1/η') = log(n/η)`.
* `stepCost_le` — one step of Algorithm 1, given `card(Idx t) ≤ m` and
  `card(Ω t) ≤ maxΩ`, costs at most
  `m·maxΩ·2k + Clw·(m·maxΩ·2k + (2k)^ω)·log(m·maxΩ + 2k + 2)^plog`,
  i.e. the counted feature-build plus the imported `Õ(Nd + d^ω)` Lewis call.

No `sorry`.
-/
import DomainReduction.Cost.Model

namespace DomainReduction.Cost

open scoped BigOperators
open Finset Arlib Arlib.Approximation DomainReduction.Mixture

/-! ## The Cohen–Peng row count under the FPRAS calibration -/

/-- **The Cohen–Peng row count `m = sampleSize (2k) C (ε/(3n)) (η/n)` unfolded to a
real polynomial bound** (`main.tex:169–174`).  Substituting `δ = ε/(3n)` gives
`δ⁻² = (3n/ε)² = 9n²/ε²`, and `η' = η/n` gives `log(1/η') = log(n/η)`:

`m ≤ C·(2k)·log(2k)·(9n²/ε²)·log(n/η) + 1`.

The `log(2k)` and `log(n/η)` factors are kept **explicit** (not collapsed into the
`Õ`), exactly as nfalean keeps `Real.log(16|Q^u|)`.  The `+1` is the `Nat.ceil`
slack. -/
theorem sampleSize_bound {k n : ℕ} {ε η : ℝ} (C : ℝ)
    (hC : 0 ≤ C) (hk : 1 ≤ k) (hn : 0 < n) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1) :
    (sampleSize (2 * k) C (ε / (3 * n)) (η / n) : ℝ)
      ≤ C * (2 * k) * Real.log (2 * k) * (9 * (n : ℝ) ^ 2 / ε ^ 2) * Real.log (n / η) + 1 := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2k : (1 : ℝ) ≤ 2 * (k : ℝ) := by linarith
  have hnη : (1 : ℝ) ≤ (n : ℝ) / η := by
    rw [le_div_iff₀ hη]; nlinarith
  -- the nonnegativity hypothesis `sampleSize_le` demands, in its own variables
  have hnn : 0 ≤ C * ((2 * k : ℕ) : ℝ) * Real.log ((2 * k : ℕ) : ℝ)
      * (ε / (3 * (n : ℝ)))⁻¹ ^ 2 * Real.log (1 / (η / (n : ℝ))) := by
    have t1 : (0 : ℝ) ≤ Real.log ((2 * k : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * k))
    have t2 : (0 : ℝ) ≤ Real.log (1 / (η / (n : ℝ))) := by
      rw [one_div_div]; exact Real.log_nonneg hnη
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) t1)
      (sq_nonneg _)) t2
  have h := sampleSize_le (dim := 2 * k) (C := C) (δ := ε / (3 * (n : ℝ)))
    (η := η / (n : ℝ)) hnn
  have hδ : (ε / (3 * (n : ℝ)))⁻¹ ^ 2 = 9 * (n : ℝ) ^ 2 / ε ^ 2 := by
    rw [inv_div, div_pow]; ring
  refine h.trans_eq ?_
  rw [one_div_div, hδ]
  push_cast
  ring

section Mixture

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]
    {D : MixturePair k Ω}

/-! ## The per-step operation count -/

/-- **The operation count of one step `t` of Algorithm 1**, given the size bridge
`card(Idx t) ≤ m` and the uniform domain bound `card(Ω t) ≤ maxΩ`.

The counted feature-build costs `card(Idx t)·card(Ω t)·2k ≤ m·maxΩ·2k` (`buildCost`),
and the imported Lewis call on the `N = card(Idx t × Ω t) ≤ m·maxΩ` point candidate
costs at most `Clw·(N·2k + (2k)^ω)·log(N + 2k + 2)^plog` (`SparsifyCost.callCost_le`),
which the size bound lifts to the `m·maxΩ`-point worst case.  Hence

`stepCost t ≤ m·maxΩ·2k + Clw·(m·maxΩ·2k + (2k)^ω)·log(m·maxΩ + 2k + 2)^plog`.

This is the `Õ(|Ω_t|·n²k²/ε² · log(n/η) + k^ω)` per-step count of `main.tex:173`,
with the schedule `m`-bound of `sampleSize_bound` still to be substituted for `m`. -/
theorem stepCost_le (SC : SparsifyCost) (Rn : Run D) (t m maxΩ : ℕ)
    (hIdx : Fintype.card (Rn.Idx t) ≤ m) (hΩ : Fintype.card (Ω t) ≤ maxΩ) :
    (stepCost SC Rn t : ℝ)
      ≤ (m * maxΩ * (2 * k) : ℝ)
        + SC.Clw * ((m * maxΩ * (2 * k) : ℝ) + (2 * k) ^ SC.ω)
          * Real.log ((m * maxΩ : ℝ) + 2 * k + 2) ^ SC.plog := by
  -- feature-build bound
  have hb : (buildCost Rn t : ℝ) ≤ (m * maxΩ * (2 * k) : ℝ) := by
    rw [buildCost_eq]
    have : Fintype.card (Rn.Idx t) * Fintype.card (Ω t) * (2 * k) ≤ m * maxΩ * (2 * k) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hIdx hΩ)
    exact_mod_cast this
  -- the imported Lewis call bound, lifted to the m·maxΩ worst case
  have hNm : (Fintype.card (Rn.Idx t) : ℝ) * Fintype.card (Ω t) ≤ (m : ℝ) * maxΩ := by
    have : Fintype.card (Rn.Idx t) * Fintype.card (Ω t) ≤ m * maxΩ := Nat.mul_le_mul hIdx hΩ
    exact_mod_cast this
  have hk2 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  have harg1 : (1 : ℝ) ≤ (Fintype.card (Rn.Idx t) : ℝ) * Fintype.card (Ω t) + 2 * k + 2 := by
    have : (0 : ℝ) ≤ (Fintype.card (Rn.Idx t) : ℝ) * Fintype.card (Ω t) := by positivity
    linarith
  have hL1nn : (0 : ℝ)
      ≤ Real.log ((Fintype.card (Rn.Idx t) : ℝ) * Fintype.card (Ω t) + 2 * k + 2) :=
    Real.log_nonneg harg1
  have hL12 : Real.log ((Fintype.card (Rn.Idx t) : ℝ) * Fintype.card (Ω t) + 2 * k + 2)
      ≤ Real.log ((m * maxΩ : ℝ) + 2 * k + 2) := by
    apply Real.log_le_log (by linarith)
    have : (m * maxΩ : ℝ) = (m : ℝ) * maxΩ := by ring
    rw [this]; linarith
  have hc : (SC.callCost (Rn.cand t) : ℝ)
      ≤ SC.Clw * ((m * maxΩ * (2 * k) : ℝ) + (2 * k) ^ SC.ω)
        * Real.log ((m * maxΩ : ℝ) + 2 * k + 2) ^ SC.plog := by
    have hle := SC.callCost_le (Rn.cand t)
    rw [Fintype.card_prod, card_coord] at hle
    push_cast at hle
    refine le_trans hle ?_
    have hA12 : (Fintype.card (Rn.Idx t) : ℝ) * Fintype.card (Ω t) * (2 * k) + (2 * k) ^ SC.ω
        ≤ (m * maxΩ * (2 * k) : ℝ) + (2 * k) ^ SC.ω := by
      have := mul_le_mul_of_nonneg_right hNm hk2
      have he : (m * maxΩ * (2 * k) : ℝ) = (m : ℝ) * maxΩ * (2 * k) := by ring
      rw [he]; linarith
    have hpow : Real.log ((Fintype.card (Rn.Idx t) : ℝ) * Fintype.card (Ω t) + 2 * k + 2) ^ SC.plog
        ≤ Real.log ((m * maxΩ : ℝ) + 2 * k + 2) ^ SC.plog :=
      pow_le_pow_left₀ hL1nn hL12 _
    have hClw : (0 : ℝ) ≤ (SC.Clw : ℝ) := Nat.cast_nonneg _
    have hA2nn : (0 : ℝ) ≤ (m * maxΩ * (2 * k) : ℝ) + (2 * k) ^ SC.ω := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA12 hClw) hpow
      (pow_nonneg hL1nn _) (mul_nonneg hClw hA2nn)
  -- assemble
  have : (stepCost SC Rn t : ℝ) = (buildCost Rn t : ℝ) + (SC.callCost (Rn.cand t) : ℝ) := by
    unfold stepCost; push_cast; ring
  rw [this]
  exact add_le_add hb hc

end Mixture

end DomainReduction.Cost
