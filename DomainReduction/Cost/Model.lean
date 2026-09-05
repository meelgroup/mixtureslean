/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The operational running-time cost model of the domain-reduction FPRAS

This file gives a **step-counted** account of the arithmetic work the
domain-reduction dynamic program performs, following the running-time halves of
Theorem 2.1 (mixture) and Theorem 3.1 (circuit).  It mirrors
`approxbdd/nfa/tods/nfalean/ApproxNFA/Cost/Model.lean`: an abstract cost structure
for the imported subroutine, a genuinely *counted* feature-build component, and a
per-step / per-region aggregate whose bound the later modules discharge.

## Faithfulness stance: hypothesis vs. proven

The load-bearing subroutine — the Lewis-weight solver of `thm:lewis_weights` — is
**imported** (its `Õ(N d + d^ω)` runtime is cited, not proved).  So the model
splits each step's cost into:

* **counted** — the feature-vector construction of the candidate domain
  (lines 6–9 of `alg:fptas`: one Hadamard / tensor product, `N·d` multiplications).
  This is a genuine `card ι · card d` count, the analog of nfalean's real
  `Finset.sum` components, and is NOT the target bound in disguise.
* **imported** — the single `Sparsify` call, whose op-count is a field of the new
  hypothesis structure `SparsifyCost`, exactly parallel to how the `(1 ± δ)`
  embedding is a field of `SparsifyGuarantee`.  Nothing here asserts the solver's
  runtime; a downstream theorem takes a `SparsifyCost` term as a parameter, so
  `#print axioms` stays `[propext, Classical.choice, Quot.sound]`.

The matrix-multiplication exponent `ω` is carried **abstract** (`SparsifyCost.ω`,
`hω : 2 ≤ ω`) so the headline states the true dependence, and the solver's soft-`Õ`
polylog is carried as an **explicit** `Real.log`-factor (`plog`), exactly as
nfalean keeps `Real.log (16 |Q^u|)` explicit rather than hiding it.

The **total-cost target** this foundation builds toward (mixture, `main.tex:175`) is
`totalCost ≤ Ctot · n³·k²·maxΩ · ε⁻² · log(n/η) · log(2k) · polylog + n·(2k)^ω`,
i.e. `O(n³ k² maxΩ ε⁻² log(n/η)) + n·k^ω`.  See `Cost/DEVPLAN-COST.md`.

No `sorry`.
-/
import DomainReduction.Mixture.Algorithm
import DomainReduction.SizeGuarantee
import DomainReduction.Model.Prelude.Circuit
import DomainReduction.Model.Prelude.Cost

namespace DomainReduction.Cost

open scoped BigOperators
open Finset Arlib Arlib.Approximation DomainReduction.Mixture

/-! ## The Cohen–Peng row count, unfolded to a real bound

The size bridge `card (Idx t) ≤ m` turns the counted `N = card(Idx t)·card(Ω t)`
into the polynomial `m·|Ω_t|`, where `m = sampleSize (2k) C δ η'`.  The following
elementary ceiling → real bound is the first arithmetic step toward the schedule
substitution `δ = ε/(3n)`, `η' = η/n` performed in `Cost/Schedule.lean`. -/

/-- **`sampleSize` unfolded to a real upper bound** (`Nat.ceil` → real, the analog
of nfalean's `Cost/Schedule.lean` ceiling bounds):
`m = ⌈C·dim·log dim·δ⁻²·log(1/η)⌉₊ ≤ C·dim·log dim·δ⁻²·log(1/η) + 1`, given that the
argument of the ceiling is nonnegative (which the schedule's positivity hypotheses
supply). -/
theorem sampleSize_le {dim : ℕ} {C δ η : ℝ}
    (h : 0 ≤ C * (dim : ℝ) * Real.log dim * δ⁻¹ ^ 2 * Real.log (1 / η)) :
    (sampleSize dim C δ η : ℝ)
      ≤ C * (dim : ℝ) * Real.log dim * δ⁻¹ ^ 2 * Real.log (1 / η) + 1 := by
  unfold sampleSize
  exact le_of_lt (Nat.ceil_lt_add_one h)

section Mixture

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]
    {D : MixturePair k Ω}

/-! ## Mixture side: the counted feature-build, per step, and total -/

/-- `Fintype.card (Mixture.Coord k) = 2k`: the `2k` feature coordinates are the
`P`-block `Fin k` and the `Q`-block `Fin k`.  (Qualified as `Mixture.Coord` because
this file also imports the circuit's own bare-namespace `Coord`, which the enclosing
`DomainReduction` namespace would otherwise pick.) -/
theorem card_coord (k : ℕ) : Fintype.card (Mixture.Coord k) = 2 * k := by
  simp [Mixture.Coord, Fintype.card_sum, two_mul]

/-- **The feature-build cost of the candidate at step `t`**: one Hadamard product,
`N·d` multiplications (lines 6–9 of `alg:fptas`), with `N = card(Idx t × Ω t)` and
`d = card(Mixture.Coord k) = 2k`.  A genuine `card ι · card d` count. -/
noncomputable def buildCost (Rn : Run D) (t : ℕ) : ℕ :=
  Fintype.card (Rn.Idx t × Ω t) * Fintype.card (Mixture.Coord k)

/-- **The counted feature-build is exactly `N·d`.**  `buildCost = card(Idx t)·|Ω_t|·2k`. -/
theorem buildCost_eq (Rn : Run D) (t : ℕ) :
    buildCost Rn t = Fintype.card (Rn.Idx t) * Fintype.card (Ω t) * (2 * k) := by
  unfold buildCost
  rw [Fintype.card_prod, card_coord]

/-- **The cost of one step `t`**: build the candidate, then one `Sparsify` call on
it.  `Rn.cand t : WPS (Idx t × Ω t) (Mixture.Coord k)`. -/
noncomputable def stepCost (SC : SparsifyCost) (Rn : Run D) (t : ℕ) : ℕ :=
  buildCost Rn t + SC.callCost (Rn.cand t)

/-- **The total number of arithmetic operations the mixture run performs** — the
quantity the mixture-FPRAS theorem (`mixture_fpras`) bounds on every outcome: the
sum of the per-step costs (`stepCost`, a feature build plus one `Sparsify` call)
over the `n` steps. -/
noncomputable def totalCost (SC : SparsifyCost) (Rn : Run D) (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, stepCost SC Rn t

/-- **The run's coresets stay within the Lewis row count `m`** (the size bridge,
analog of nfalean's structural `hout`/`hQcard` hypotheses): the root coreset is a
singleton, and every step-`t` output has at most `m` points.  A
`SizedSparsifyGuarantee`-instrumented random run yields this with
`m = sampleSize (2k) C δ η'` on every outcome. -/
def SizedRun (Rn : Run D) (m : ℕ) (n : ℕ) : Prop :=
  Fintype.card (Rn.Idx 0) ≤ 1 ∧ ∀ t, t < n → Fintype.card (Rn.Idx (t + 1)) ≤ m

/-- `totalCost` at `0` steps is `0`. -/
@[simp] theorem totalCost_zero (SC : SparsifyCost) (Rn : Run D) :
    totalCost SC Rn 0 = 0 := by
  simp [totalCost]

/-- The one-step unfolding of `totalCost` (the summand split the capstone consumes). -/
theorem totalCost_succ (SC : SparsifyCost) (Rn : Run D) (n : ℕ) :
    totalCost SC Rn (n + 1) = totalCost SC Rn n + stepCost SC Rn n := by
  simp [totalCost, Finset.sum_range_succ]

end Mixture

/-! ## Circuit side: the bottom-up construction cost over the region tree

The circuit's candidate at each product region is a `WPS.tensor` of the two
children's coresets, and the number of `Sparsify` calls is the number of product
nodes = `C.steps = L`.  The region tree combines children whose feature dimensions
differ (`Region dl`, `Region dr` glue into `Region d`), but it is one and the same
Lewis solver invoked at each — so the whole construction is charged against a
**single** `SC : SparsifyCost`, whose `callCost` applies at every dimension the
tree visits (the dimension is an implicit argument of `callCost`, inferred from the
candidate). -/

/-- **The total number of arithmetic operations a whole bottom-up construction `R`
performs** — the quantity the circuit-FPRAS theorem (`circuit_fpras`) bounds on
every outcome.  It is `0` at a leaf (nothing is reduced there), and at each product
node the two children's cost plus one `Sparsify` call on the tensor candidate
`WPS.tensor M Rl.core Rr.core`; so the number of `callCost` summands is the number
of product nodes = `Region.steps`. -/
noncomputable def regionCost (SC : SparsifyCost) :
    ∀ {d : Type} [Fintype d] {S : Region d}, Reduction S → ℕ
  | _, _, _, @Reduction.leaf _ _ _ _ _ => 0
  | _, _, _, @Reduction.node _ _ instl instr _ _ _ M Rl Rr _ _ C =>
      @regionCost SC _ instl _ Rl + @regionCost SC _ instr _ Rr
        + SC.callCost (WPS.tensor M Rl.core Rr.core)

/-- `regionCost` at a leaf is `0` — nothing is reduced there. -/
@[simp] theorem regionCost_leaf (SC : SparsifyCost)
    (X : Type) [Fintype X] [DecidableEq X] {d : Type} [Fintype d] (Φ : X → d → ℝ) :
    regionCost SC (Reduction.leaf X Φ) = 0 := rfl

/-- **`regionCost` at a product node** unfolds to the two children's costs plus one
`Sparsify` call on the tensor candidate (`main.tex:214, 237`). -/
@[simp] theorem regionCost_node (SC : SparsifyCost)
    {dl dr : Type} [Fintype dl] [Fintype dr] {d : Type} [Fintype d]
    {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
    (Rl : Reduction l) (Rr : Reduction r) (ι : Type) [Fintype ι] (C : WPS ι d) :
    regionCost SC (Reduction.node M Rl Rr ι C)
      = regionCost SC Rl + regionCost SC Rr
        + SC.callCost (WPS.tensor M Rl.core Rr.core) := rfl

end DomainReduction.Cost
