/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The estimated quantity really is the total variation distance

`Model/Prelude/Mixture` defines `D.tv n` as `½ ∑ₓ |P(x) − Q(x)|` for the two mixtures.
That is the standard formula, but a formalization that *defines* the target and
then proves an algorithm computes it has proved nothing about total variation.
This file closes that gap from both ends:

* `IsProb D` — the hypotheses under which a `MixturePair` really is a pair of
  probability distributions: the mixture weights and every marginal are
  nonnegative and sum to one.
* `sum_compP` / `sum_prob` — under those hypotheses `P` is a probability mass
  function on the assignment space (`∑ₓ P(x) = 1`), and likewise `Q`.  Note what
  this proves along the way: a mixture of *products of marginals* is normalised,
  which is where the product structure is actually used.
* `MixturePair.dist` — hence a bona-fide `Arlib.MarkovChains.FinDist`.
* `tv_eq_tvDist` — **`D.tv n` is `Arlib.MarkovChains.tvDist` of those two
  distributions**, an independently defined notion (it comes with `tvDist_comm`,
  `tvDist_triangle`, the event characterisation, and the data-processing
  inequality, none of which know anything about this paper).

So the capstone of `Mixture.Algorithm` is a statement about the total variation
distance between two probability distributions, not about a convenient surrogate.

No `sorry`.
-/
import DomainReduction.Model.Prelude.Mixture
import Arlib.MarkovChains.Techniques.TotalVariation

namespace DomainReduction.Mixture

open scoped BigOperators
open Finset Arlib Arlib.Approximation Arlib.MarkovChains

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)]

/-- The hypotheses under which a `MixturePair` is a genuine pair of mixtures of
product *probability* distributions: nonnegative weights and marginals, each
summing to one. -/
structure IsProb (D : MixturePair k Ω) : Prop where
  /-- The mixture weights of `P` are nonnegative. -/
  α_nonneg : ∀ i, 0 ≤ D.α i
  /-- The mixture weights of `P` sum to one. -/
  α_sum : ∑ i, D.α i = 1
  /-- The mixture weights of `Q` are nonnegative. -/
  β_nonneg : ∀ i, 0 ≤ D.β i
  /-- The mixture weights of `Q` sum to one. -/
  β_sum : ∑ i, D.β i = 1
  /-- Every marginal of every component of `P` is nonnegative. -/
  Pm_nonneg : ∀ i t a, 0 ≤ D.Pm i t a
  /-- Every marginal of every component of `P` sums to one. -/
  Pm_sum : ∀ i t, ∑ a, D.Pm i t a = 1
  /-- Every marginal of every component of `Q` is nonnegative. -/
  Qm_nonneg : ∀ i t a, 0 ≤ D.Qm i t a
  /-- Every marginal of every component of `Q` sums to one. -/
  Qm_sum : ∀ i t, ∑ a, D.Qm i t a = 1

namespace MixturePair

variable {D : MixturePair k Ω} (h : IsProb D)

/-! ## The components are product probability distributions -/

omit [∀ t, Fintype (Ω t)] in
theorem compP_succ (i : Fin k) (t : ℕ) (x : Pre Ω (t + 1)) :
    D.compP i (t + 1) x = D.compP i t x.1 * D.Pm i t x.2 := rfl

omit [∀ t, Fintype (Ω t)] in
theorem compQ_succ (i : Fin k) (t : ℕ) (x : Pre Ω (t + 1)) :
    D.compQ i (t + 1) x = D.compQ i t x.1 * D.Qm i t x.2 := rfl

include h

/-- Each component of `P` is nonnegative: a product of nonnegative marginals. -/
theorem compP_nonneg (i : Fin k) : ∀ (t : ℕ) (x : Pre Ω t), 0 ≤ D.compP i t x := by
  intro t
  induction t with
  | zero => intro x; exact zero_le_one
  | succ t ih =>
      intro x
      rw [compP_succ]
      exact mul_nonneg (ih x.1) (h.Pm_nonneg i t x.2)

theorem compQ_nonneg (i : Fin k) : ∀ (t : ℕ) (x : Pre Ω t), 0 ≤ D.compQ i t x := by
  intro t
  induction t with
  | zero => intro x; exact zero_le_one
  | succ t ih =>
      intro x
      rw [compQ_succ]
      exact mul_nonneg (ih x.1) (h.Qm_nonneg i t x.2)

/-- **Each component of `P` is a probability distribution.**  The sum over the
assignment space factorises coordinate by coordinate — this is the one place the
*product* structure of the components is used. -/
theorem sum_compP (i : Fin k) : ∀ t : ℕ, ∑ x : Pre Ω t, D.compP i t x = 1 := by
  intro t
  induction t with
  | zero =>
      have hc : Fintype.card (Pre Ω 0) = 1 := rfl
      simp [compP, R, hc]
  | succ t ih =>
      have : ∑ x : Pre Ω (t + 1), D.compP i (t + 1) x
          = ∑ y : Pre Ω t, ∑ a : Ω t, D.compP i t y * D.Pm i t a := by
        rw [show (∑ x : Pre Ω (t + 1), D.compP i (t + 1) x)
              = ∑ x : Pre Ω t × Ω t, D.compP i t x.1 * D.Pm i t x.2 from rfl]
        exact Fintype.sum_prod_type _
      rw [this]
      calc ∑ y : Pre Ω t, ∑ a : Ω t, D.compP i t y * D.Pm i t a
          = ∑ y : Pre Ω t, D.compP i t y * ∑ a : Ω t, D.Pm i t a := by
            exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
        _ = ∑ y : Pre Ω t, D.compP i t y := by simp [h.Pm_sum i t]
        _ = 1 := ih

theorem sum_compQ (i : Fin k) : ∀ t : ℕ, ∑ x : Pre Ω t, D.compQ i t x = 1 := by
  intro t
  induction t with
  | zero =>
      have hc : Fintype.card (Pre Ω 0) = 1 := rfl
      simp [compQ, R, hc]
  | succ t ih =>
      have : ∑ x : Pre Ω (t + 1), D.compQ i (t + 1) x
          = ∑ y : Pre Ω t, ∑ a : Ω t, D.compQ i t y * D.Qm i t a := by
        rw [show (∑ x : Pre Ω (t + 1), D.compQ i (t + 1) x)
              = ∑ x : Pre Ω t × Ω t, D.compQ i t x.1 * D.Qm i t x.2 from rfl]
        exact Fintype.sum_prod_type _
      rw [this]
      calc ∑ y : Pre Ω t, ∑ a : Ω t, D.compQ i t y * D.Qm i t a
          = ∑ y : Pre Ω t, D.compQ i t y * ∑ a : Ω t, D.Qm i t a := by
            exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
        _ = ∑ y : Pre Ω t, D.compQ i t y := by simp [h.Qm_sum i t]
        _ = 1 := ih

/-! ## The mixtures are probability distributions -/

theorem prob_nonneg (t : ℕ) (x : Pre Ω t) : 0 ≤ D.prob t x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (h.α_nonneg i) (compP_nonneg h i t x)

theorem probQ_nonneg (t : ℕ) (x : Pre Ω t) : 0 ≤ D.probQ t x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (h.β_nonneg i) (compQ_nonneg h i t x)

theorem sum_prob (t : ℕ) : ∑ x : Pre Ω t, D.prob t x = 1 := by
  simp only [prob]
  rw [Finset.sum_comm]
  calc ∑ i : Fin k, ∑ x : Pre Ω t, D.α i * D.compP i t x
      = ∑ i : Fin k, D.α i * ∑ x : Pre Ω t, D.compP i t x := by
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ i : Fin k, D.α i := by simp [sum_compP h]
    _ = 1 := h.α_sum

theorem sum_probQ (t : ℕ) : ∑ x : Pre Ω t, D.probQ t x = 1 := by
  simp only [probQ]
  rw [Finset.sum_comm]
  calc ∑ i : Fin k, ∑ x : Pre Ω t, D.β i * D.compQ i t x
      = ∑ i : Fin k, D.β i * ∑ x : Pre Ω t, D.compQ i t x := by
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ i : Fin k, D.β i := by simp [sum_compQ h]
    _ = 1 := h.β_sum

/-! ## The bridge to `Arlib.MarkovChains.tvDist` -/

/-- The mixture `P`, as a genuine finite probability distribution on the space of
assignments to the first `n` coordinates. -/
def dist (n : ℕ) : FinDist (Pre Ω n) where
  p := D.prob n
  p_nonneg := prob_nonneg h n
  p_sum := sum_prob h n

/-- The mixture `Q`, as a genuine finite probability distribution. -/
def distQ (n : ℕ) : FinDist (Pre Ω n) where
  p := D.probQ n
  p_nonneg := probQ_nonneg h n
  p_sum := sum_probQ h n

/-- **The estimated quantity is the total variation distance.**  `D.tv n`
coincides with `Arlib.MarkovChains.tvDist` — defined elsewhere, for arbitrary
finite distributions, and equipped there with symmetry, the triangle inequality,
the event characterisation and the data-processing inequality.

This is what makes the capstone of `Mixture.Algorithm` a theorem about total
variation rather than about a definition chosen to suit the algorithm. -/
theorem tv_eq_tvDist (n : ℕ) : D.tv n = tvDist (dist h n) (distQ h n) := rfl

end MixturePair

end DomainReduction.Mixture
