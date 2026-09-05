/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The *size-carrying* sparsification guarantee, as a hypothesis

`DomainReduction.Sparsify` records only the **accuracy** half of Cohen–Peng's
Theorem 1.1: a `SparsifyGuarantee` promises that, off a small failure event, the
reduced set is a `(1 ± δ)` subspace embedding of the input, uniformly in the
query — but it says *nothing* about how many points the reduced set has. Its
`outIdx` is an arbitrary finite type.

This file adds the missing **size** half, still as a hypothesis rather than an
axiom, following the same convention (imported results are `structure`s a
downstream theorem takes as a parameter, never `axiom`s; `#print axioms` stays
`[propext, Classical.choice, Quot.sound]`).

A term of `SizedSparsifyGuarantee d δ η` is a `SparsifyGuarantee d δ η` (its full
accuracy content, reachable through the forgetful projection
`toSparsifyGuarantee`) *together with* a universal constant `C` and the promise
`outCard_le` that on every input and every outcome the number of surviving points
is at most

`m = ⌈ C · dim · log dim · δ⁻² · log(1/η) ⌉₊`,   `dim = Fintype.card d`,

which is the `p = 1`, `δ = 1/C` row count `O(d log d · ε⁻² · log(1/η))` of
Cohen–Peng's `thm:ellpsample` (their sufficient-row-count table). The bound is
stated **uniformly over the coin tosses**: `outCard_le` quantifies over every
`ω`, so a sampler whose output size fluctuates must meet the bound on *every*
run, not merely in expectation — the honest reading of a worst-case size
guarantee.

## What discharging this hypothesis would require (the honest gap)

Nothing in this file constructs an inhabitant; supplying one is exactly the
content of the size half of Theorem 1.1. The arlib development
`Arlib.Approximation.LewisWeights` has proved the *finite-moment* core of the
accuracy argument — Khintchine (`avg_pow_le`), the Lewis moment identity
(`sum_sq_lev`), the per-row / summed moment bounds (`avg_row_pow_le`,
`avg_sum_row_pow_le`) and the Markov/moment-method bridge (`avg_pow_tail`) — but
the following remain research-grade and unproven, and *all* of them gate an
inhabitant of `SizedSparsifyGuarantee`:

* the **comparison / contraction** lemma (Ledoux–Talagrand) passing from the
  Rademacher process `𝔼_σ max |∑ σᵢ|aᵢᵀx|` to the Gaussian one;
* the **`lewlinf` sup-bridge**, from the finite summed moment
  `𝔼_σ ∑ᵢ (row i)^{2k}` to the *supremum* `(max_{‖Ax‖₁=1} …)^{2k}` via
  projection + ℓ₁/ℓ∞ duality;
* **`momentreduct`** (`papers/peng/ellp-reduction.tex`): the symmetrization
  reduction from the uniform-half-sampling bound to importance sampling by Lewis
  weights, which invokes **matrix Chernoff** and an **Auerbach / well-conditioned
  `O(d²)`-row basis** (`lem:weakbound`);
* **Lewis-weight existence** with the *summation* `∑ wᵢ = d` (only the defining
  identity `IsLewis` is in arlib so far), which is what turns "weights sum to `d`"
  into the `d`-factor in `m`.

The size field here does not depend on any of that machinery: it is pure
interface. It exists so that a downstream complexity statement can *quantify over*
the size, exactly as the accuracy theorems quantify over `succeeds`.

No `sorry`.
-/
import DomainReduction.Sparsify
import DomainReduction.Model.Prelude.Cost
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor

namespace DomainReduction

open Arlib Arlib.Approximation

/-! ## The interface

The Cohen–Peng ℓ₁ row count `sampleSize` — the `m` a `(1 ± δ)` embedding needs — now
lives in the audit vocabulary `DomainReduction.Model.Prelude.Cost`; this file builds
the *size guarantee* around it. -/

/-- **The size-carrying ℓ₁ subspace-embedding guarantee of Lewis-weight row
sampling.**

Extends the accuracy-only `SparsifyGuarantee d δ η` with the two ingredients its
docstring lists as deliberately absent: a universal constant `C` and a *uniform
over the coin tosses* bound `outCard_le` on the number of surviving points,

`Fintype.card (outIdx U ω) ≤ sampleSize (Fintype.card d) C δ η`
                          `= ⌈ C · dim · log dim · δ⁻² · log(1/η) ⌉₊`.

The forgetful projection `toSparsifyGuarantee` recovers the pure accuracy
guarantee, so any theorem written against `SparsifyGuarantee` applies verbatim to
the `toSparsifyGuarantee` of a `SizedSparsifyGuarantee`; the size field is
strictly additional information. Like its parent this is a `structure`, possibly
empty — inhabiting it is the size half of Theorem 1.1 and is out of scope (see
the module docstring for the exact research-grade gap). -/
structure SizedSparsifyGuarantee (d : Type*) [Fintype d] (δ η : ℝ)
    extends SparsifyGuarantee d δ η where
  /-- The universal constant hidden in the `O(·)` of the row count. -/
  C : ℝ
  /-- **The output-size bound.** On every input `U` and every outcome `ω` the
  reduced point set has at most `sampleSize (Fintype.card d) C δ η` points — the
  Cohen–Peng ℓ₁ row count `⌈C · dim · log dim · δ⁻² · log(1/η)⌉₊`. -/
  outCard_le : ∀ {ι : Type} [Fintype ι] (U : WPS ι d) (ω : (space U).Ω),
      Fintype.card (outIdx U ω) ≤ sampleSize (Fintype.card d) C δ η

namespace SizedSparsifyGuarantee

variable {d : Type*} [Fintype d] {δ η : ℝ}

/-- **Forgetting the size.** The accuracy content of a size-carrying guarantee is
its underlying `SparsifyGuarantee` — the structure-projection generated by
`extends`, named here for reference. Every downstream accuracy theorem consumes
this. -/
abbrev toSparsify (S : SizedSparsifyGuarantee d δ η) : SparsifyGuarantee d δ η :=
  S.toSparsifyGuarantee

/-- The size-carrying guarantee inherits the success-probability bound of its
accuracy part: the sparsifier succeeds with probability at least `1 - η`. -/
theorem one_sub_le_Pr_good (S : SizedSparsifyGuarantee d δ η) {ι : Type} [Fintype ι]
    (U : WPS ι d) : 1 - η ≤ (S.space U).Pr (S.toSparsifyGuarantee.good U) :=
  S.toSparsifyGuarantee.one_sub_le_Pr_good U

end SizedSparsifyGuarantee

end DomainReduction
