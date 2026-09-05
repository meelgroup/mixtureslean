/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# Mixtures of product distributions, and total variation as a linear test

The setting of §1.1 of the paper.  Two mixtures

  `P(x) = ∑ᵢ αᵢ ∏ₜ P_{i,t}(xₜ)`,  `Q(x) = ∑ᵢ βᵢ ∏ₜ Q_{i,t}(xₜ)`

over a product domain `∏ₜ Ωₜ`.  The paper's whole idea rests on one observation:
with the `2k`-dimensional local feature vector

  `r_t(xₜ) = (P_{1,t}(xₜ), …, P_{k,t}(xₜ), Q_{1,t}(xₜ), …, Q_{k,t}(xₜ))`

and the constant weight vector `w = (α₁, …, α_k, −β₁, …, −β_k)`, the accumulated
Hadamard product `R(x) = ⨂ₜ r_t(xₜ)` satisfies `⟨w, R(x)⟩ = P(x) − Q(x)`, so that

  `d_TV(P, Q) = ½ ∑ₓ |⟨w, R(x)⟩|`

is a *single* absolute linear test summed over the domain — exactly the quantity
an ℓ¹ subspace embedding preserves.

## Modelling decisions

* **Coordinates are indexed by `ℕ`, and assignments to the first `t` of them are
  built by a recursion that grows on the right**: `Pre 0 = PUnit`,
  `Pre (t+1) = Pre t × Ω t`.  Consequently `Pre (t+1)` is *definitionally* a
  product of `Pre t` and `Ω t`, which is what makes the extension step of the
  dynamic program a `WPS.hadamard` on the nose, with no transport of assignments
  along an equivalence.  Using `Fin n` and `∀ j : Fin n, j.val ≤ t → Ω j` would
  buy nothing and cost a great deal.
* **The feature index type is `Fin k ⊕ Fin k`** rather than `Fin (2*k)`: the two
  halves are the `P`-block and the `Q`-block, and `Sum.elim` names a vector by
  what it does on each block, so no arithmetic on indices ever appears.
* **The marginals are arbitrary real-valued functions.**  Nothing below needs
  them to be nonnegative or to sum to one; those hypotheses are added exactly
  where the *interpretation* as a total variation distance requires them
  (`Mixture.Main`).  Stating the algebra without them is not sloppiness — it is
  what makes the same lemmas available for the unnormalised circuit features of
  §2.

No `sorry`.
-/
import Arlib.Approximation.Coresets.Tensor
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Fin

namespace DomainReduction.Mixture

open scoped BigOperators
open Finset Arlib Arlib.Approximation

/-! ## The data of a mixture pair -/

/-- The `2k` feature coordinates: the `P`-block and the `Q`-block. -/
abbrev Coord (k : ℕ) : Type := Fin k ⊕ Fin k

/-- **A pair of mixtures of product distributions** over the coordinate domains
`Ω 0, Ω 1, …`, with `k` components each.

`Pm i t a` is `P_{i,t}(a)`, the mass the `i`-th component of `P` gives to the
value `a` at coordinate `t`; likewise `Qm`.  `α`, `β` are the mixture weights.
The fields are unconstrained reals; positivity and normalisation are hypotheses
of the theorems that need them, not of the model. -/
structure MixturePair (k : ℕ) (Ω : ℕ → Type) where
  /-- The mixture weights of `P`. -/
  α : Fin k → ℝ
  /-- The mixture weights of `Q`. -/
  β : Fin k → ℝ
  /-- `Pm i t a = P_{i,t}(a)`, the `i`-th component's marginal at coordinate `t`. -/
  Pm : Fin k → (t : ℕ) → Ω t → ℝ
  /-- `Qm i t a = Q_{i,t}(a)`. -/
  Qm : Fin k → (t : ℕ) → Ω t → ℝ

namespace MixturePair

variable {k : ℕ} {Ω : ℕ → Type} (D : MixturePair k Ω)

/-- The **local feature vector** `r_t(a) = (P_{1,t}(a), …, Q_{k,t}(a))`. -/
def r (t : ℕ) (a : Ω t) : Coord k → ℝ :=
  Sum.elim (fun i => D.Pm i t a) (fun i => D.Qm i t a)

/-- The **weight vector** `w = (α₁, …, α_k, −β₁, …, −β_k)`, so that
`⟨w, R(x)⟩ = P(x) − Q(x)`. -/
def w : Coord k → ℝ := Sum.elim D.α (fun i => -D.β i)

@[simp] theorem r_inl (t : ℕ) (a : Ω t) (i : Fin k) :
    D.r t a (Sum.inl i) = D.Pm i t a := rfl

@[simp] theorem r_inr (t : ℕ) (a : Ω t) (i : Fin k) :
    D.r t a (Sum.inr i) = D.Qm i t a := rfl

@[simp] theorem w_inl (i : Fin k) : D.w (Sum.inl i) = D.α i := rfl

@[simp] theorem w_inr (i : Fin k) : D.w (Sum.inr i) = -D.β i := rfl

end MixturePair

/-! ## Prefix assignments and the accumulated feature vector -/

/-- **Assignments to the first `t` coordinates**, built so that `Pre Ω (t+1)` is
*definitionally* `Pre Ω t × Ω t`.  This is the one design decision the whole
development rests on: the extension step of the dynamic program is then literally
a Hadamard product of weighted point sets. -/
def Pre (Ω : ℕ → Type) : ℕ → Type
  | 0 => PUnit
  | t + 1 => Pre Ω t × Ω t

instance instFintypePre (Ω : ℕ → Type) [∀ t, Fintype (Ω t)] : ∀ t, Fintype (Pre Ω t)
  | 0 => inferInstanceAs (Fintype PUnit)
  | t + 1 => @instFintypeProd _ _ (instFintypePre Ω t) _

instance instDecidableEqPre (Ω : ℕ → Type) [∀ t, DecidableEq (Ω t)] :
    ∀ t, DecidableEq (Pre Ω t)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | t + 1 => @instDecidableEqProd _ _ (instDecidableEqPre Ω t) _

namespace MixturePair

variable {k : ℕ} {Ω : ℕ → Type} (D : MixturePair k Ω)

/-- The **accumulated feature vector** `R_{≤t}(x_{≤t}) = ⨂_{j<t} r_j(x_j)`,
the Hadamard product of the local feature vectors along a prefix.  The empty
product is the all-ones vector, which is the paper's root coreset feature. -/
def R : (t : ℕ) → Pre Ω t → Coord k → ℝ
  | 0, _ => fun _ => 1
  | t + 1, x => fun c => R t x.1 c * D.r t x.2 c

@[simp] theorem R_zero (x : Pre Ω 0) : D.R 0 x = fun _ => 1 := rfl

@[simp] theorem R_succ (t : ℕ) (x : Pre Ω (t + 1)) (c : Coord k) :
    D.R (t + 1) x c = D.R t x.1 c * D.r t x.2 c := rfl

/-! ## The distributions, and total variation as a linear test -/

/-- The unnormalised value of the `i`-th component of `P` on a prefix:
`∏_{j<t} P_{i,j}(x_j)`.  It is the `P`-block of the accumulated feature. -/
def compP (i : Fin k) (t : ℕ) (x : Pre Ω t) : ℝ := D.R t x (Sum.inl i)

/-- The `i`-th component of `Q` on a prefix. -/
def compQ (i : Fin k) (t : ℕ) (x : Pre Ω t) : ℝ := D.R t x (Sum.inr i)

/-- The mixture `P` evaluated on a prefix assignment. -/
def prob (t : ℕ) (x : Pre Ω t) : ℝ := ∑ i, D.α i * D.compP i t x

/-- The mixture `Q` evaluated on a prefix assignment. -/
def probQ (t : ℕ) (x : Pre Ω t) : ℝ := ∑ i, D.β i * D.compQ i t x

/-- **The linear test computes the difference of the two mixtures.**
`⟨w, R(x)⟩ = P(x) − Q(x)`.  This is the identity that turns total variation into
a single absolute linear projection, and it is nothing but the definition of `w`
read through `Fintype.sum_sum_type`. -/
theorem dot_w_R (t : ℕ) (x : Pre Ω t) :
    dot D.w (D.R t x) = D.prob t x - D.probQ t x := by
  simp only [dot, prob, probQ, compP, compQ, Fintype.sum_sum_type, w_inl, w_inr,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- **Total variation as an ℓ¹ quantity.**  `d_TV(P,Q) = ½ ∑ₓ |⟨w, R(x)⟩|`,
which is `½ · E(exact domain, w)` for the evaluation functional of
`Arlib.Approximation.Coresets`. -/
noncomputable def tv (n : ℕ) [∀ t, Fintype (Ω t)] : ℝ :=
  (1 / 2) * ∑ x : Pre Ω n, |D.prob n x - D.probQ n x|

theorem tv_eq_half_E (n : ℕ) [∀ t, Fintype (Ω t)] :
    D.tv n = (1 / 2) * (WPS.exact (Pre Ω n) (D.R n)).E D.w := by
  rw [tv, WPS.E_exact]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [dot_w_R]

end MixturePair

end DomainReduction.Mixture
