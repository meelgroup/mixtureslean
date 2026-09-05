/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The bottom-up coreset construction on a circuit, and Theorem 3.1

§3.2 and §3.3 of the paper.  Once a circuit is seen as a region tree (the
`CircuitPair` of `Arlib.KnowledgeCompilation.Probabilistic`, whose total-variation
reading is `Model/Prelude/Circuit`), the whole analysis is the abstract propagation invariant of
`Arlib.Approximation.Coresets.RegionTree` evaluated at one particular query.

* `Circuit.Reduction C` — a bottom-up construction: the exact domain at each leaf
  region, and at each product region a chosen reduced weighted point set for the
  Cartesian product of the children's.
* `Circuit.sum_layer_free` — the paper's **"Sum Gates"** paragraph: a layer of sum
  gates applies a fixed linear map to the region's feature vector, so a reduction
  of the old features is already a reduction of the new ones, with the same
  window and no domain expansion.  This is why only *product* regions are ever
  sparsified.
* `Circuit.invariant` — the paper's **Lemma 3.2**, the coreset propagation
  invariant, instantiated at a circuit.
* `Circuit.estimate_mem_relErr` — **Theorem 3.1, deterministic half**.
* `RandomReduction.main` — **Theorem 3.1**, with the union bound over the `L`
  product-region sparsifications.

## Which hypotheses are actually used

Smoothness, decomposability and structured decomposability are all consumed, and
they are consumed exactly once, in the shape of `Circuit.valP_node`: the region
feature map of an internal node is *bilinear* in its children's.  **Determinism
is never used** — it appears in the paper's hypotheses and in none of its steps.
Removing it from the theorem statement would not change a line of this proof.

## What is not modelled

As in the mixture case, only the **accuracy** guarantee is formalized.  Nothing
here bounds the size of a reduced set, the number of arithmetic operations, or
the running time, so the complexity half of the paper's Theorem 3.1 is not
checked anywhere in this development.  See `DomainReduction.Sparsify`.

One deliberate relaxation, which makes the theorem *stronger* rather than weaker:
a reduced set here is an arbitrary weighted point set with the embedding
property, not necessarily a reweighted **subset** of the candidate domain.  For
an output that is a subset — which is what Lewis-weight row sampling returns —
the surviving feature vectors really are `Φ_root(z_j)` for actual assignments
`z_j`, and `estimate` is literally the paper's
`D̃ = ½ ∑ⱼ μⱼ |P_r(z_j) − Q_r(z_j)|`.

No `sorry`.
-/
import DomainReduction.Model.Prelude.Circuit
import DomainReduction.Sparsify
import Arlib.MarkovChains.Techniques.TotalVariation

namespace DomainReduction

open scoped BigOperators
open Finset Arlib Arlib.MarkovChains
open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic (Vtree CircuitPair Coord)

namespace Circuit

/-! ## The bottom-up construction -/

/-- The algorithm's **estimator** `D̃`: half the weighted sum of absolute values
of `P_r − Q_r` over the surviving root assignments. -/
noncomputable def estimate {V : Vtree} (C : CircuitPair V 1 1) (R : C.Reduction) : ℝ :=
  (1 / 2) * R.core.E aTV

/-! ## Sum gates cost nothing

The paper's §3.2 "Sum Gates" paragraph: a sum layer replaces `Φ_S` by `L_S Φ_S`
for a fixed matrix `L_S`, and `⟨a, L_S Φ⟩ = ⟨L_Sᵀ a, Φ⟩`, so a set that preserves
all linear tests on the old features preserves all linear tests on the new ones
— *identically*, and without enlarging the domain. -/

/-- **A sum layer is free.**  If `C` reduces `U` then it still does after the
features are transformed by any fixed linear map, with the same window and the
same points.  Hence no sparsification is needed at a sum gate, and the error
exponent counts product regions only. -/
theorem sum_layer_free {d d' ι κ : Type*} [Fintype d] [Fintype d'] [Fintype ι] [Fintype κ]
    {lo hi : ℝ} {U : WPS κ d} {Cs : WPS ι d} (L : d' → d → ℝ) (h : Embeds lo hi U Cs) :
    Embeds lo hi (WPS.linMap L U) (WPS.linMap L Cs) :=
  Embeds.linMap L h

/-! ## Lemma 3.2 and Theorem 3.1 -/

/-- **Lemma 3.2 (Coreset Propagation Invariant).**  If every product region was
sparsified to within `(1 ± δ)`, then the reduced set at the root reproduces
*every* linear test on the entire exact assignment space, to within
`(1 ± δ)^{L}` where `L` is the number of product regions.

This is `Arlib.Approximation.Reduction.embeds_exact` read at a circuit; the induction
lives there, and the only circuit-specific input is that a product region's
feature map is bilinear in its children's. -/
theorem invariant {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (R : C.Reduction) (hR : R.Sparsifies δ) :
    Embeds ((1 - δ) ^ C.steps) ((1 + δ) ^ C.steps) (C.toRegion).exactWPS R.core :=
  Arlib.Approximation.Reduction.embeds_exact hδ0 hδ1 R hR

/-- **Theorem 3.1, deterministic half.**  With per-step tolerance `δ = ε/(3L)`,
the estimator lies in `(1 ± ε) · d_TV(P, Q)`. -/
theorem estimate_mem_relErr {V : Vtree} (C : CircuitPair V 1 1) {ε : ℝ} (hL : 0 < C.steps)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (R : C.Reduction)
    (hR : R.Sparsifies (ε / (3 * C.steps))) :
    estimate C R ∈ relErr ε (dTV C) := by
  have h := Arlib.Approximation.Reduction.relErr_of_calibrated R hL hε hε1 hR aTV
  rw [dTV_eq_half_E C, estimate]
  exact Between.const_mul (by norm_num) h


/-! ## Line 1: the per-region calibration

The circuit algorithm's parameter-setting step, the analog of Algorithm 1's
`line:parameters` (`Model/Pseudocode.stepTolerance`/`stepFailure`).  A circuit of
`L = C.steps` product regions must compound `L` per-region `(1 ± δ)` guarantees
to `(1 ± ε)` and union-bound `L` failures to `η`, so it *derives*
`δ = ε/(3L)` and `η' = η/L` from its inputs `(ε, η)`.  These are named here — and
marked `@[reducible]` (definitionally `ε/(3L)`, `η/L`) — so the statement layer
refers to the derivation rather than restating the arithmetic, and no per-region
budget leaks into a headline theorem's hypotheses. -/

/-- **`δ = ε/(3L)`** — the per-region tolerance, derived from `(ε, C.steps)`. -/
@[reducible] noncomputable def stepTolerance (ε : ℝ) {V : Vtree} (C : CircuitPair V 1 1) : ℝ :=
  ε / (3 * C.steps)

/-- **`η' = η/L`** — the per-region failure probability, derived from
`(η, C.steps)`. -/
@[reducible] noncomputable def stepFailure (η : ℝ) {V : Vtree} (C : CircuitPair V 1 1) : ℝ :=
  η / C.steps

/-! ## The union bound over the `L` product regions -/

/-- A **randomised bottom-up construction**: a finite probability space, the
construction produced on each outcome, and for each of the `L` product-region
sparsifications a failure event of probability at most `η'`, off all of which the
whole construction meets its `(1 ± δ)` guarantee. -/
structure RandomReduction {V : Vtree} (C : CircuitPair V 1 1) (δ η' : ℝ) where
  /-- The probability space of all the sparsifiers' coin tosses. -/
  space : Arlib.FinProb
  /-- The construction produced on a given coin sequence. -/
  red : space.Ω → C.Reduction
  /-- `bad i` is the event that the `i`-th product-region sparsification failed. -/
  bad : ℕ → space.Ω → Prop
  /-- The failure events are events, i.e. decidable. -/
  [badDec : ∀ i, DecidablePred (bad i)]
  /-- Each of the `L` sparsifications fails with probability at most `η'`. -/
  bad_prob : ∀ i ∈ Finset.range C.steps, space.Pr (Finset.univ.filter (bad i)) ≤ η'
  /-- Off every failure event, the construction is a `(1 ± δ)` sparsification at
  every product region. -/
  good : ∀ ω, (∀ i ∈ Finset.range C.steps, ¬ bad i ω) → (red ω).Sparsifies δ

attribute [instance] RandomReduction.badDec

namespace RandomReduction

variable {V : Vtree} {C : CircuitPair V 1 1} {δ η' : ℝ}

/-- **Theorem 3.1.**  With per-region tolerance `δ = ε/(3L)` and per-region
failure probability `η' = η/L`, the estimator lies in `(1 ± ε)·d_TV(P,Q)` with
probability at least `1 - η`.

The union bound is over the `L` product regions, and `L` is `Circuit.steps` —
which counts internal nodes of the region *tree*.  That the two counts agree is
exactly the content of structured decomposability; see the discussion in
`Arlib.Approximation.Coresets.RegionTree`. -/
theorem main {ε η : ℝ} (hL : 0 < C.steps) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (RR : RandomReduction C (ε / (3 * C.steps)) (η / C.steps)) :
    1 - η ≤ RR.space.Pr (Finset.univ.filter
      (fun ω => estimate C (RR.red ω) ∈ relErr ε (dTV C))) := by
  have hub := RR.space.one_sub_card_mul_le_Pr_forall_not
    (Finset.range C.steps) RR.bad RR.bad_prob
  refine le_trans ?_ (le_trans hub (RR.space.Pr_mono ?_))
  · have hL0 : ((C.steps : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
    have hcard : ((Finset.range C.steps).card : ℝ) * (η / C.steps) = η := by
      rw [Finset.card_range]; field_simp
    rw [hcard]
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact estimate_mem_relErr C hL hε hε1 _ (RR.good ω hω)

end RandomReduction

end Circuit

end DomainReduction
