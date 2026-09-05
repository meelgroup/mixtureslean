/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# Theorem 2.1, running-time half: the total operation count of the mixture FPRAS

This is the capstone of the mixture running-time development.  Summing the
per-step operation count `stepCost_le` (`Cost/Schedule.lean`) over the `n` steps
of Algorithm 1 and substituting the Cohen–Peng row count
`m = sampleSize (2k) C (ε/(3n)) (η/n)` by its schedule bound `sampleSize_bound`,
we obtain a clean polynomial upper bound on `totalCost`, with the honest leading
dependence

`totalCost ≤ n · [ S·maxΩ·2k + Clw·(S·maxΩ·2k + (2k)^ω)·log(S·maxΩ + 2k + 2)^plog ]`,
where `S = Clw·2k·log(2k)·(9n²/ε²)·log(n/η) + 1 = O(k log k · n²/ε² · log(n/η))`.

Reading off the leading term (`S·maxΩ·2k = O(k²·maxΩ·n²/ε²·log(2k)·log(n/η))`,
times the outer `n` and the Lewis constant, plus the additive `n·(2k)^ω` from the
`(2k)^ω` matrix-multiplication term), this is

`O(n³ · k² · maxΩ · ε⁻² · log(n/η) · log(2k)) + n·(2k)^ω`,

polynomial in `n, k, 1/ε, log(1/η), maxΩ` — the FPRAS running-time claim
(`main.tex:175`).  The matrix-mult exponent `ω` stays abstract, the two `Real.log`
factors and the solver polylog `(log …)^plog` are kept explicit (never collapsed
into the `Õ`), exactly as nfalean keeps `Real.log(16|Q^u|)`.

This is the running-time conjunct that bundles next to `mixture_fpras` (accuracy)
in `Model/Theorem.lean`.

No `sorry`.
-/
import DomainReduction.Cost.Schedule
import DomainReduction.Mixture.Probability

namespace DomainReduction.Cost

open scoped BigOperators
open Finset Arlib Arlib.Approximation DomainReduction.Mixture

section Mixture

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]
    {D : MixturePair k Ω}

/-- **A size-and-cost-instrumented randomised run** (`thm:main_fptas`).  It bundles,
in one object, everything the two halves of Theorem 2.1 consume, so that neither
half floats as a side hypothesis:

* the accuracy structure `RandomRun` (the per-step `(1 ± δ)` behaviour of `Sparsify`);
* the imported per-call runtime interface `SC : SparsifyCost`;
* the **size half** `sized`: on *every* coin sequence the coresets stay within the
  Cohen–Peng row count `m = sampleSize (2k) SC.Clw δ η'`;
* the **non-degeneracy** `rowPos`: that row count is at least `1` (`Sparsify`
  keeps at least one row), a deterministic fact about the constant `m` that the
  cost bridge needs at step `0`.

This is the running-time analog of packaging accuracy in `RandomRun`: a
`SizedSparsifyGuarantee`-instrumented run inhabits it, its accuracy field giving the
`RandomRun`, its `outCard_le` field giving `sized`, and the schedule's positive
row count giving `rowPos`.  With it, `mixture_fpras` takes no floating per-outcome
or per-`m` hypothesis — the object supplies both halves. -/
structure SizedRandomRun (SC : SparsifyCost) (D : MixturePair k Ω) (n : ℕ) (δ η' : ℝ)
    extends RandomRun D n δ η' where
  /-- The size half: every run's coresets stay within `sampleSize (2k) SC.Clw δ η'`. -/
  sized : ∀ ω, SizedRun (toRandomRun.run ω) (sampleSize (2 * k) SC.Clw δ η') n
  /-- Non-degeneracy: the Cohen–Peng row count is at least one. -/
  rowPos : 1 ≤ sampleSize (2 * k) SC.Clw δ η'

/-! ## The per-step cost as a function of the (real) point budget

`perStep SC k maxΩ x` is the per-step operation count when the candidate has at most
`x` prefixes and `maxΩ` domain elements: the counted feature-build `x·maxΩ·2k` plus
the imported Lewis call `Clw·(x·maxΩ·2k + (2k)^ω)·log(x·maxΩ + 2k + 2)^plog`.  It is
monotone in `x`, which is all the capstone needs to substitute `x = m` by its
schedule bound. -/
noncomputable def perStep (SC : SparsifyCost) (k maxΩ : ℕ) (x : ℝ) : ℝ :=
  x * maxΩ * (2 * k)
    + SC.Clw * (x * maxΩ * (2 * k) + (2 * k) ^ SC.ω)
      * Real.log (x * maxΩ + 2 * k + 2) ^ SC.plog

/-- **`perStep` is monotone in the point budget `x`.**  Every occurrence of `x`
carries a nonnegative multiplier, and the `Real.log` argument is increasing, so a
larger budget never lowers the count. -/
theorem perStep_mono (SC : SparsifyCost) (k maxΩ : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : perStep SC k maxΩ x ≤ perStep SC k maxΩ y := by
  unfold perStep
  have hmax0 : (0 : ℝ) ≤ (maxΩ : ℝ) := Nat.cast_nonneg _
  have h2k : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  have hy : 0 ≤ y := le_trans hx hxy
  have hClw : (0 : ℝ) ≤ (SC.Clw : ℝ) := Nat.cast_nonneg _
  have hxmk : x * maxΩ * (2 * k) ≤ y * maxΩ * (2 * k) := by
    nlinarith [mul_le_mul_of_nonneg_right hxy hmax0]
  have harg1 : (1 : ℝ) ≤ x * maxΩ + 2 * k + 2 := by
    nlinarith [mul_nonneg hx hmax0]
  have hargle : x * maxΩ + 2 * k + 2 ≤ y * maxΩ + 2 * k + 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hxy hmax0]
  have hL1nn : 0 ≤ Real.log (x * maxΩ + 2 * k + 2) := Real.log_nonneg harg1
  have hpow : Real.log (x * maxΩ + 2 * k + 2) ^ SC.plog
      ≤ Real.log (y * maxΩ + 2 * k + 2) ^ SC.plog :=
    pow_le_pow_left₀ hL1nn (Real.log_le_log (by linarith) hargle) _
  have hA : x * maxΩ * (2 * k) + (2 * k) ^ SC.ω ≤ y * maxΩ * (2 * k) + (2 * k) ^ SC.ω := by
    linarith
  have hAynn : (0 : ℝ) ≤ y * maxΩ * (2 * k) + (2 * k) ^ SC.ω :=
    add_nonneg (mul_nonneg (mul_nonneg hy hmax0) h2k) (pow_nonneg h2k _)
  refine add_le_add hxmk ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left hA hClw) hpow (pow_nonneg hL1nn _)
    (mul_nonneg hClw hAynn)

/-! ## The capstone: the total mixture operation count -/

/-- **Theorem 2.1, running-time half** (`main.tex:175`).

Given the Lewis per-call runtime interface `SC`, a run whose coresets stay within
the Cohen–Peng row count `m = sampleSize (2k) Clw (ε/(3n)) (η/n)` (`SizedRun`), the
uniform domain bound `card(Ω t) ≤ maxΩ`, and the FPRAS calibration positivity, the
total arithmetic operation count of Algorithm 1 obeys

`totalCost ≤ n · perStep SC k maxΩ S`,  where
`S = Clw·2k·log(2k)·(9n²/ε²)·log(n/η) + 1`

is the schedule bound on `m` (`sampleSize_bound`).  Expanding `perStep` and reading
off the leading term, this is

`O(n³ · k² · maxΩ · ε⁻² · log(n/η) · log(2k)) + n·(2k)^ω`,

polynomial in `n, k, 1/ε, log(1/η), maxΩ`.  The exponent `ω` stays abstract; the
two `Real.log` factors and the solver polylog `(log …)^plog` are kept explicit.

The proof: cast `totalCost` to a `Finset.sum`, bound each summand by
`perStep SC k maxΩ m` via `stepCost_le` and the size bridge `SizedRun`, collapse the
constant sum to `n · perStep SC k maxΩ m`, and finally substitute `m ≤ S` through the
monotonicity `perStep_mono` and the schedule bound `sampleSize_bound`. -/
theorem mixture_totalCost_le (SC : SparsifyCost) (Rn : Run D)
    {ε η : ℝ} {n maxΩ : ℕ}
    (hk : 1 ≤ k) (hn : 0 < n) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1)
    (hm1 : 1 ≤ sampleSize (2 * k) SC.Clw (ε / (3 * n)) (η / n))
    (hsz : SizedRun Rn (sampleSize (2 * k) SC.Clw (ε / (3 * n)) (η / n)) n)
    (hmax : ∀ t, t < n → Fintype.card (Ω t) ≤ maxΩ) :
    (totalCost SC Rn n : ℝ)
      ≤ (n : ℝ) * perStep SC k maxΩ
          ((SC.Clw : ℝ) * (2 * k) * Real.log (2 * k) * (9 * (n : ℝ) ^ 2 / ε ^ 2)
            * Real.log (n / η) + 1) := by
  set m := sampleSize (2 * k) SC.Clw (ε / (3 * n)) (η / n) with hmdef
  set S := (SC.Clw : ℝ) * (2 * k) * Real.log (2 * k) * (9 * (n : ℝ) ^ 2 / ε ^ 2)
    * Real.log (n / η) + 1 with hSdef
  -- size bridge: every step's prefix count is at most `m`
  have hIdxAll : ∀ t, t < n → Fintype.card (Rn.Idx t) ≤ m := by
    intro t ht
    cases t with
    | zero => exact le_trans hsz.1 hm1
    | succ s => exact hsz.2 s (by omega)
  -- schedule bound: `m ≤ S`
  have hmS : (m : ℝ) ≤ S :=
    sampleSize_bound (k := k) (n := n) (ε := ε) (η := η) (SC.Clw : ℝ)
      (Nat.cast_nonneg _) hk hn hε hη hη1
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  calc (totalCost SC Rn n : ℝ)
      = ∑ t ∈ Finset.range n, (stepCost SC Rn t : ℝ) := by
        simp only [totalCost, Nat.cast_sum]
    _ ≤ ∑ _t ∈ Finset.range n, perStep SC k maxΩ (m : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        have ht' : t < n := Finset.mem_range.mp ht
        have hstep := stepCost_le SC Rn t m maxΩ (hIdxAll t ht') (hmax t ht')
        simpa [perStep] using hstep
    _ = (n : ℝ) * perStep SC k maxΩ (m : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * perStep SC k maxΩ S :=
        mul_le_mul_of_nonneg_left (perStep_mono SC k maxΩ hmnn hmS) (Nat.cast_nonneg _)

end Mixture

end DomainReduction.Cost
