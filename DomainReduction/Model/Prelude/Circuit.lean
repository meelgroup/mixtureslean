/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The circuit target really is the total variation distance

§3.1 of the paper.  The structured circuit pair itself — a pair of circuits over a
shared v-tree, its block-diagonal joint feature vector, and its region-tree
semantics — is reusable machinery and lives in
`Arlib.KnowledgeCompilation.Probabilistic` (`CircuitPair`).  What is specific to
*this* paper, and stays here, is the total-variation reading of a pair whose two
root gates compute probability distributions:

* `aTV` / `dot_aTV` — the linear test `a_TV` that reads off `P_r − Q_r`.
* `Circuit.dTV` / `dTV_eq_half_E` — the target `d_TV`, and its identification with
  half the evaluation functional of the exact domain at `a_TV`.
* `IsProb` — the hypothesis that the root gate computes a distribution (for a
  circuit this is a genuine assumption on the parameters, not a consequence of the
  architecture), and `dTV_eq_tvDist` — under it, `d_TV` is
  `Arlib.MarkovChains.tvDist`, an independently defined notion.

No `sorry`.
-/
import Arlib.KnowledgeCompilation.Probabilistic
import Arlib.MarkovChains.Techniques.TotalVariation

namespace DomainReduction

open scoped BigOperators
open Finset Arlib
open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic (Vtree CircuitPair Coord)
open Arlib.MarkovChains

namespace Circuit

/-! ## Total variation as the linear test at the root

At the root each side has a single gate, and the total variation distance is the
absolute value of one fixed linear test on the root region's feature vector. -/

/-- The paper's `a_TV`: the selector that reads off `P_r − Q_r`. -/
def aTV : Coord 1 1 → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

/-- **The `a_TV` linear test computes the difference of the two circuits.** -/
theorem dot_aTV {V : Vtree} (C : CircuitPair V 1 1) (x : C.Assign) :
    dot aTV (C.Phi x) = C.valP x 0 - C.valQ x 0 := by
  simp [dot, aTV, Fintype.sum_sum_type, CircuitPair.valP, CircuitPair.valQ, sub_eq_add_neg]

/-- The total variation distance between the two circuits' root distributions. -/
noncomputable def dTV {V : Vtree} (C : CircuitPair V 1 1) : ℝ :=
  (1 / 2) * ∑ x : C.Assign, |C.valP x 0 - C.valQ x 0|

/-- **`d_TV` is half the evaluation functional of the exact domain at `a_TV`.** -/
theorem dTV_eq_half_E {V : Vtree} (C : CircuitPair V 1 1) :
    dTV C = (1 / 2) * (C.toRegion).exactWPS.E aTV := by
  rw [dTV, Region.exactWPS, WPS.E_exact]
  exact congrArg _ (Finset.sum_congr rfl fun x _ => by rw [dot_aTV])

/-! ## The estimated quantity really is the total variation distance

A formalization that *defines* its target proves nothing about total variation.
Unlike the mixture case, normalisation cannot be derived from the parameters:
"probabilistic circuit" means a circuit whose root value happens to be a
distribution, and that is a hypothesis about the parameters, not a consequence of
the architecture.  So it is assumed — and then the target is identified with
`Arlib.MarkovChains.tvDist`, which is defined elsewhere for arbitrary finite
distributions and knows nothing about this paper. -/

/-- The hypothesis that a circuit's root gate computes a probability
distribution over the assignments in its scope. -/
structure IsProb {V : Vtree} (C : CircuitPair V 1 1) : Prop where
  /-- The `P`-parameterization is nonnegative. -/
  valP_nonneg : ∀ x, 0 ≤ C.valP x 0
  /-- The `P`-parameterization sums to one. -/
  valP_sum : ∑ x, C.valP x 0 = 1
  /-- The `Q`-parameterization is nonnegative. -/
  valQ_nonneg : ∀ x, 0 ≤ C.valQ x 0
  /-- The `Q`-parameterization sums to one. -/
  valQ_sum : ∑ x, C.valQ x 0 = 1

/-- The root distribution of the `P`-parameterization. -/
def distP {V : Vtree} {C : CircuitPair V 1 1} (h : IsProb C) : FinDist C.Assign where
  p := fun x => C.valP x 0
  p_nonneg := h.valP_nonneg
  p_sum := h.valP_sum

/-- The root distribution of the `Q`-parameterization. -/
def distQ {V : Vtree} {C : CircuitPair V 1 1} (h : IsProb C) : FinDist C.Assign where
  p := fun x => C.valQ x 0
  p_nonneg := h.valQ_nonneg
  p_sum := h.valQ_sum

/-- **`Circuit.dTV` is the total variation distance** between the two circuits'
root distributions, in the independent sense of `Arlib.MarkovChains.tvDist`. -/
theorem dTV_eq_tvDist {V : Vtree} {C : CircuitPair V 1 1} (h : IsProb C) :
    dTV C = tvDist (distP h) (distQ h) := rfl

end Circuit

end DomainReduction
