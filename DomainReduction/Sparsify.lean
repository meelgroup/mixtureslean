/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The imported sparsification guarantee, as a hypothesis

Theorem 1.1 of the paper is not proved here.  It is Cohen–Peng's `ℓ_p` row
sampling by Lewis weights, specialised to `p = 1`, and it says:

> **Theorem 1.1 (imported).**  There is a randomised algorithm which, given a
> weighted point set `U` of `N` points with feature vectors in `ℝ^d`, and
> parameters `δ, η ∈ (0,1)`, outputs a weighted point set `C` supported on
> `m = O(d log d · δ⁻² · log(1/η))` of the points of `U`, such that with
> probability at least `1 - η`,
> `(1 - δ) · E(U, y) ≤ E(C, y) ≤ (1 + δ) · E(U, y)` **for every** query
> `y ∈ ℝ^d` simultaneously.  The running time is `Õ(N d^ω)` (or nearly linear in
> the number of nonzeros, with the standard refinements).

Here `E(C, y) = ∑ᵢ μᵢ |⟨y, vᵢ⟩|` is the `ℓ₁` evaluation functional of
`Arlib.Approximation.WPS.E`, and the two-sided conclusion is
`Arlib.Approximation.Embeds (1 - δ) (1 + δ) U C`.

## Why this is a `structure` and not an `axiom`

The convention of this development, inherited from `Arlib.KnowledgeCompilation`,
is that **imported results are hypotheses, never axioms**.  A theorem that relies
on Lewis-weight sampling takes a `SparsifyGuarantee` as an explicit parameter, so
that the dependency is visible in the *statement* of the theorem and is checked
by `#print axioms` (which will report only `propext`, `Classical.choice`,
`Quot.sound`).  Nothing below is asserted to be true: `SparsifyGuarantee d δ η`
is a type, possibly empty, and every downstream theorem is of the form "given a
term of this type, …".

What this file formalises is therefore the *interface* to Lewis-weight sampling,
not Lewis weights.  There is no construction of a Lewis-weight distribution, no
sampling argument, no matrix concentration, and no proof that the interface is
inhabited.  Supplying an inhabitant is exactly the content of Theorem 1.1, and it
is out of scope.

## What is deliberately *not* modelled

Theorem 1.1 has two halves — an **accuracy** half and a **size / running-time**
half.  Only the accuracy half appears here.  Concretely:

* `SparsifyGuarantee` records **no bound whatsoever on the size of the output**.
  The field `outIdx` is an arbitrary finite index type; nothing forces it to be
  small, nothing forces it to be a *subset* of the input, and there is no
  occurrence of `d log d / δ² · log(1/η)` anywhere in this file.
* There is likewise no model of running time, of arithmetic cost, or of the
  number of oracle calls.

Consequently the size and running-time halves of the paper's Theorems 2.1 and
3.1 — the statements that the dynamic program keeps
`O(k log k · n² ε⁻² log(n/η))` points per step and runs in the stated time — are
**not formalised anywhere in this development**.  What is formalised is the
accuracy half: *if* every sparsification step meets its `(1 ± δ)` guarantee, the
output is a `(1 ± ε)` approximation of `d_TV(P, Q)`, and that happens with
probability at least `1 - η`.  A reader who wants the complexity claims must take
them from the paper; this repository does not check them.

No `sorry`.
-/
import Arlib.Approximation.Coresets.Embedding
import Arlib.Probability.UnionBound

namespace DomainReduction

open Arlib Arlib.Approximation

/-! ## The interface -/

/-- **The `ℓ₁` subspace-embedding guarantee of Lewis-weight row sampling**, as a
bundle of data and hypotheses rather than an axiom.

A term of `SparsifyGuarantee d δ η` is: a sparsification procedure on weighted
point sets with features in `ℝ^d`, presented by its internal randomness
(`space`), the reduced point set it returns on each outcome (`outIdx`, `out`), a
distinguished failure event (`bad`) of probability at most `η` (`bad_prob`), and
the promise that off the failure event the output is a `(1 ± δ)` subspace
embedding of the input, *uniformly in the query* (`succeeds`).

Three points about the shape of the definition, each of which matters
downstream.

* The guarantee is **uniform in the query**: `Embeds` quantifies over all
  `y : d → ℝ`.  This is the whole reason the domain-reduction argument works —
  at the moment step `t` is sparsified, the linear test that the resulting
  coreset will eventually be asked is not yet determined, because the later
  coordinates have not been chosen.  A per-query guarantee would be useless.
* The index type of the output is **allowed to depend on the outcome**: a
  sampling algorithm returns a different number of points on different coin
  tosses.  Hence `outIdx : ∀ U ω, Type` rather than a fixed type.
* The failure event is a `Finset` of outcomes rather than a predicate, matching
  `Arlib.FinProb.Event`, so that `bad_prob` is literally a `Pr`-inequality that
  a union bound can consume.

Nothing here bounds `outIdx` in size; see the module docstring — the size and
running-time half of Theorem 1.1 is out of scope. -/
structure SparsifyGuarantee (d : Type*) [Fintype d] (δ : ℝ) (η : ℝ) where
  /-- The probability space of the sparsifier's internal randomness, for a given
  input. -/
  space : ∀ {ι : Type} [Fintype ι], WPS ι d → Arlib.FinProb
  /-- The index type of the reduced weighted point set the sparsifier returns on
  a given input and outcome.  It may depend on the coin tosses: a sampling
  algorithm returns a different number of points on different runs. -/
  outIdx : ∀ {ι : Type} [Fintype ι] (U : WPS ι d), (space U).Ω → Type
  /-- The output is finite. -/
  [outFin : ∀ {ι : Type} [Fintype ι] (U : WPS ι d) (ω : (space U).Ω),
      Fintype (outIdx U ω)]
  /-- The reduced weighted point set the sparsifier returns on a given input and
  outcome. -/
  out : ∀ {ι : Type} [Fintype ι] (U : WPS ι d) (ω : (space U).Ω),
      WPS (outIdx U ω) d
  /-- The failure event: the outcomes on which no guarantee is claimed. -/
  bad : ∀ {ι : Type} [Fintype ι] (U : WPS ι d), Finset (space U).Ω
  /-- The guarantee fails with probability at most `η`. -/
  bad_prob : ∀ {ι : Type} [Fintype ι] (U : WPS ι d), (space U).Pr (bad U) ≤ η
  /-- Off the failure event the output is a `(1 ± δ)` subspace embedding of the
  input: it reproduces `E(U, ·)` to within a factor `1 ± δ`, simultaneously for
  every query. -/
  succeeds : ∀ {ι : Type} [Fintype ι] (U : WPS ι d) (ω : (space U).Ω),
      ω ∉ bad U → Embeds (1 - δ) (1 + δ) U (out U ω)

attribute [instance] SparsifyGuarantee.outFin

namespace SparsifyGuarantee

variable {d : Type*} [Fintype d] {δ η : ℝ}

/-- **The success event** of the sparsifier on input `U`: the complement of the
failure event.  Stated as a `Finset`, so that it is an `Arlib.FinProb.Event`. -/
def good (S : SparsifyGuarantee d δ η) {ι : Type} [Fintype ι] (U : WPS ι d) :
    Finset (S.space U).Ω :=
  Finset.univ \ S.bad U

/-- **The sparsifier succeeds with probability at least `1 - η`.**

This is `bad_prob` read through the complement rule `Arlib.FinProb.Pr_compl`.  It
is the form in which the paper states Theorem 1.1; the union bound of
`DomainReduction.Mixture.Probability` consumes the `bad_prob` form directly,
because that is the form the union bound is stated in. -/
theorem one_sub_le_Pr_good (S : SparsifyGuarantee d δ η) {ι : Type} [Fintype ι]
    (U : WPS ι d) : 1 - η ≤ (S.space U).Pr (S.good U) := by
  have h := S.bad_prob U
  rw [good, FinProb.Pr_compl]
  linarith

/-- **Membership in the success event is exactly what `succeeds` consumes.**  A
convenience restatement of `succeeds` for an outcome presented as an element of
`good` rather than as a non-element of `bad`. -/
theorem embeds_of_mem_good (S : SparsifyGuarantee d δ η) {ι : Type} [Fintype ι]
    (U : WPS ι d) {ω : (S.space U).Ω} (hω : ω ∈ S.good U) :
    Embeds (1 - δ) (1 + δ) U (S.out U ω) := by
  rw [good, Finset.mem_sdiff] at hω
  exact S.succeeds U ω hω.2

end SparsifyGuarantee

end DomainReduction
