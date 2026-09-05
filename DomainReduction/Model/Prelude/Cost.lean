/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# Prelude: the cost vocabulary

Part of the `Model/` audit surface (imports only arlib + Mathlib).  It owns the two
cost-model names the audit surface refers to:

* `sampleSize` — the Cohen–Peng ℓ₁ row count `⌈C·d log d·δ⁻²·log(1/η)⌉₊`, a closed
  form the pseudocode's `line:sample_size` names.
* `SparsifyCost` — the imported `Õ(N d + d^ω)` per-call runtime of Lewis-weight row
  sampling, packaged as a hypothesis structure (never an axiom), exactly parallel to
  `SparsifyGuarantee`.  A downstream theorem takes a `SparsifyCost` term as a
  parameter, so `#print axioms` stays clean.

Both are analogous to the reference development's Model-owned `Params` block: the
heavy cost machinery in `DomainReduction.Cost` and `DomainReduction.SizeGuarantee`
*imports* these, rather than defining them, so every cost name the `Model/` layer
mentions is itself defined under `Model/`.
-/
import Arlib.Approximation.Coresets.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor

namespace DomainReduction

open Arlib Arlib.Approximation

/-- **The Cohen–Peng ℓ₁ row count** `m = ⌈C·dim·log dim·δ⁻²·log(1/η)⌉₊`
(`thm:ellpsample`'s `p = 1` line: Lewis weights sum to `dim`, with the standard
`log(1/η)` high-probability boosting). -/
noncomputable def sampleSize (dim : ℕ) (C δ η : ℝ) : ℕ :=
  ⌈C * (dim : ℝ) * Real.log (dim : ℝ) * δ⁻¹ ^ 2 * Real.log (1 / η)⌉₊

namespace Cost

/-- **The `Õ(N d + d^ω)` per-call runtime of Lewis-weight row sampling**
(`thm:lewis_weights`, `main.tex:64–71`), as a bundle of data and hypotheses rather
than an axiom — exactly parallel to `SparsifyGuarantee`.

`callCost` is the opaque monotone op-count of one `Sparsify` call at *any* feature
dimension `d` (one solver, every dimension), with the abstract matrix-mult exponent
`ω` (`hω : 2 ≤ ω`) carrying the true `d^ω` dependence, and the soft-`Õ` polylog made
explicit as the `(log (N + d + 2))^plog` factor of `callCost_le`. -/
structure SparsifyCost where
  /-- Matrix-mult exponent (paper: `ω ≤ 2.4`).  Abstract `ℕ` so the theorem states
  the true dependence; bound `ω ≤ 3` only when a concrete polynomial is wanted. -/
  ω : ℕ
  /-- The matrix-mult exponent is at least `2` (a matrix has at least `N·d`
  entries to read). -/
  hω : 2 ≤ ω
  /-- The `Õ`-constant the solver's soft-`O` hides. -/
  Clw : ℕ
  /-- The polylog degree the `Õ` absorbs: `Õ` swallows `(log (N + d + 2))^plog`. -/
  plog : ℕ
  /-- **Arithmetic op-count of ONE `Sparsify` call** on input `U` of `N = card ι`
  points, at *any* feature dimension `d` (the same solver at every dimension). -/
  callCost : ∀ {d ι : Type} [Fintype d] [Fintype ι], WPS ι d → ℕ
  /-- **Monotone in the number of input points**: more rows never makes the call
  cheaper.  (Used to bound each step's actual candidate by the `m`-point worst
  case.) -/
  callCost_mono : ∀ {d ι κ : Type} [Fintype d] [Fintype ι] [Fintype κ]
      (U : WPS ι d) (V : WPS κ d),
      Fintype.card ι ≤ Fintype.card κ → callCost U ≤ callCost V
  /-- **The imported `Õ(N d + d^ω)` bound** (`thm:lewis_weights`, `main.tex:70`),
  with the tilde made explicit as the `(log (N + d + 2))^plog` factor. -/
  callCost_le : ∀ {d ι : Type} [Fintype d] [Fintype ι] (U : WPS ι d),
      (callCost U : ℝ)
        ≤ (Clw : ℝ)
            * ((Fintype.card ι : ℝ) * Fintype.card d + (Fintype.card d : ℝ) ^ ω)
            * Real.log ((Fintype.card ι : ℝ) + Fintype.card d + 2) ^ plog

end Cost

end DomainReduction
