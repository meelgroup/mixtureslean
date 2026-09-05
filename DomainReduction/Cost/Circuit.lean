/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# Theorem 3.1, running-time half: the total operation count of the circuit FPRAS

This is the capstone of the circuit running-time development, the structured
counterpart of `Cost/Mixture.lean`.  The mixture side summed a per-step cost over
the `n` steps of Algorithm 1; here the work is a **bottom-up construction over the
region tree** of a structured circuit, so the aggregate is a recursion over the
`L = C.steps` product regions rather than a flat sum.

The per-region candidate at a product region `S = A ⊔ B` is the Cartesian product
`WPS.tensor` of the two children's coresets (`main.tex:214`).  With each child
coreset carrying at most `m = sampleSize W Clw (ε/(3L)) (η/L)` points, that
candidate has at most `m²` points, and one Lewis-weight call on it costs
`Õ(m²·W + W^ω)`.  Summing over the `L` product regions gives the honest headline

`regionCost ≤ L · Clw·(m²·W + W^ω)·log(m² + W + 2)^plog`,

and, substituting the schedule bound `m ≤ Clw·W·log W·(9L²/ε²)·log(L/η) + 1`
(`sampleSize_bound_circuit`), the leading dependence

`O(W³ · L⁵ · ε⁻⁴ · log²(L/η) · log²W) + L·W^ω`,

polynomial in `W, L, 1/ε, log(1/η)` — the paper states only "scales
polynomially" (`main.tex:237`); the exponent is made explicit here.  The
matrix-mult exponent `ω` stays abstract; the two `Real.log` factors and the
solver polylog `(log …)^plog` are kept explicit (never collapsed into the `Õ`),
exactly as the mixture side does.

## The tree recursion

The new work relative to the mixture side is the aggregation.  Rather than
decompose `regionCost` into a sum over product nodes, the clean route is a direct
induction

`regionCost SC R ≤ S.steps · Q`

on the `Reduction` tree `R` over `S` (`regionCost_le_steps`), where `Q` is the
region-uniform per-region bound `perRegion Clw ω plog W m`: a leaf costs `0 =
0·Q` (and `steps = 0`); a product node costs the two children's costs (`≤
l.steps·Q`, `≤ r.steps·Q` by the inductive hypotheses) plus one call (`≤ Q`),
which is `(l.steps + r.steps + 1)·Q = node.steps·Q`.  Instantiating at `S =
C.toRegion` gives `S.steps = C.steps = L`.

## Added hypotheses

* `W` — a uniform bound on every visited region's feature width `card d`,
  carried per node by the structural predicate `SizedReduction`.
* `m` — the per-child coreset size bound `card (child.Idx) ≤ m`, likewise carried
  by `SizedReduction` (the running-time analog of the mixture `SizedRun`, and of
  the size half's `SizedSparsifyGuarantee.outCard_le`).
* The region tree glues children of *different* feature dimensions, but it is one
  and the same Lewis solver invoked at each, so the cost is charged against a
  **single** `SC : SparsifyCost` whose `callCost` and constants `SC.Clw`, `SC.ω`,
  `SC.plog` apply at every dimension (the dimension is an implicit argument of
  `callCost`, inferred from each region's candidate).  No per-dimension family and
  no uniformity side-conditions are needed.

This is the running-time conjunct that bundles next to `circuit_fpras`
(accuracy) — `estimate_mem_relErr` / `RandomReduction.main` — as the second half
of Theorem 3.1.

No `sorry`.
-/
import DomainReduction.Cost.Schedule
import DomainReduction.Circuit.Main

namespace DomainReduction.Cost

open scoped BigOperators
open Finset Arlib
open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic (Vtree CircuitPair Coord)

/-! ## The Cohen–Peng row count under the circuit calibration -/

/-- **The circuit-side schedule substitution** of the Cohen–Peng row count
`m = sampleSize W Cst (ε/(3L)) (η/L)`, the exact analog of the mixture
`sampleSize_bound` with `n → L` (the number of product regions) and the feature
dimension taken directly as `W` (in place of `2k`).  Substituting `δ = ε/(3L)`
gives `δ⁻² = 9L²/ε²`, and `η' = η/L` gives `log(1/η') = log(L/η)`:

`m ≤ Cst·W·log W·(9L²/ε²)·log(L/η) + 1`.

The `log W` and `log(L/η)` factors are kept explicit; the `+1` is the `Nat.ceil`
slack. -/
theorem sampleSize_bound_circuit {W L : ℕ} {ε η : ℝ} (Cst : ℝ)
    (hC : 0 ≤ Cst) (hW : 1 ≤ W) (hL : 0 < L) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1) :
    (sampleSize W Cst (ε / (3 * L)) (η / L) : ℝ)
      ≤ Cst * (W : ℝ) * Real.log (W : ℝ) * (9 * (L : ℝ) ^ 2 / ε ^ 2) * Real.log (L / η) + 1 := by
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLη : (1 : ℝ) ≤ (L : ℝ) / η := by
    rw [le_div_iff₀ hη]; nlinarith
  have hnn : 0 ≤ Cst * ((W : ℕ) : ℝ) * Real.log ((W : ℕ) : ℝ)
      * (ε / (3 * (L : ℝ)))⁻¹ ^ 2 * Real.log (1 / (η / (L : ℝ))) := by
    have t1 : (0 : ℝ) ≤ Real.log ((W : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hW)
    have t2 : (0 : ℝ) ≤ Real.log (1 / (η / (L : ℝ))) := by
      rw [one_div_div]; exact Real.log_nonneg hLη
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) t1)
      (sq_nonneg _)) t2
  have h := sampleSize_le (dim := W) (C := Cst) (δ := ε / (3 * (L : ℝ)))
    (η := η / (L : ℝ)) hnn
  have hδ : (ε / (3 * (L : ℝ)))⁻¹ ^ 2 = 9 * (L : ℝ) ^ 2 / ε ^ 2 := by
    rw [inv_div, div_pow]; ring
  refine h.trans_eq ?_
  rw [one_div_div, hδ]

/-! ## The per-region point-budget cost

`perRegion Clw ω plog W x` is the per-product-region operation count when the
candidate has at most `x` points per child (so at most `x²` in the Cartesian
product) and feature width `W`: the imported Lewis call
`Clw·(x²·W + W^ω)·log(x² + W + 2)^plog` on the `|U_S| = x² × d_S` matrix.  It is
monotone in `x`, which is all the capstone needs to substitute `x = m` by its
schedule bound. -/
noncomputable def perRegion (Clw ω plog W : ℕ) (x : ℝ) : ℝ :=
  (Clw : ℝ) * (x ^ 2 * (W : ℝ) + (W : ℝ) ^ ω)
    * Real.log (x ^ 2 + (W : ℝ) + 2) ^ plog

/-- **`perRegion` is monotone in the point budget `x`.**  Every occurrence of `x`
carries a nonnegative multiplier and the `Real.log` argument is increasing, so a
larger budget never lowers the count. -/
theorem perRegion_mono {Clw ω plog W : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    perRegion Clw ω plog W x ≤ perRegion Clw ω plog W y := by
  unfold perRegion
  have hy : 0 ≤ y := le_trans hx hxy
  have hx2 : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hWnn : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg _
  have hClwnn : (0 : ℝ) ≤ (Clw : ℝ) := Nat.cast_nonneg _
  have harg1 : (1 : ℝ) ≤ x ^ 2 + (W : ℝ) + 2 := by nlinarith [sq_nonneg x]
  have hargle : x ^ 2 + (W : ℝ) + 2 ≤ y ^ 2 + (W : ℝ) + 2 := by linarith
  have hLnn : 0 ≤ Real.log (x ^ 2 + (W : ℝ) + 2) := Real.log_nonneg harg1
  have hpow : Real.log (x ^ 2 + (W : ℝ) + 2) ^ plog
      ≤ Real.log (y ^ 2 + (W : ℝ) + 2) ^ plog :=
    pow_le_pow_left₀ hLnn (Real.log_le_log (by linarith) hargle) _
  have hmid : x ^ 2 * (W : ℝ) + (W : ℝ) ^ ω ≤ y ^ 2 * (W : ℝ) + (W : ℝ) ^ ω := by
    nlinarith [hx2, hWnn]
  have hmidynn : 0 ≤ y ^ 2 * (W : ℝ) + (W : ℝ) ^ ω := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmid hClwnn) hpow (pow_nonneg hLnn _)
    (mul_nonneg hClwnn hmidynn)

/-! ## The per-region call bound -/

/-- **The imported Lewis call on one product region, bounded by `perRegion`.**
The candidate is the tensor product `WPS.tensor M Rl.core Rr.core` of the two
children's coresets, with `card (Rl.Idx × Rr.Idx) = card Rl.Idx · card Rr.Idx ≤
m²` points and feature width `card d ≤ W`.  Feeding those into the imported
`Õ(N·d + d^ω)` bound `SparsifyCost.callCost_le` (the same solver at this
dimension) gives

`callCost (tensor) ≤ SC.Clw·(m²·W + W^SC.ω)·log(m² + W + 2)^SC.plog`,

the unfolding of `perRegion SC.Clw SC.ω SC.plog W m`. -/
theorem callCost_tensor_le (SC : SparsifyCost)
    {m W : ℕ}
    {dl dr d : Type} [Fintype dl] [Fintype dr] [Fintype d]
    {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
    (Rl : Reduction l) (Rr : Reduction r)
    (hcl : Fintype.card Rl.Idx ≤ m) (hcr : Fintype.card Rr.Idx ≤ m)
    (hcd : Fintype.card d ≤ W) :
    (SC.callCost (WPS.tensor M Rl.core Rr.core) : ℝ)
      ≤ (SC.Clw : ℝ) * ((m : ℝ) ^ 2 * (W : ℝ) + (W : ℝ) ^ SC.ω)
          * Real.log ((m : ℝ) ^ 2 + (W : ℝ) + 2) ^ SC.plog := by
  have hle := SC.callCost_le (WPS.tensor M Rl.core Rr.core)
  set Clw := SC.Clw with hClwSet
  set ω := SC.ω with hωSet
  set plog := SC.plog with hplogSet
  -- the candidate has at most `m²` points
  have hN : (Fintype.card (Rl.Idx × Rr.Idx) : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [Fintype.card_prod]
    have hmm : Fintype.card Rl.Idx * Fintype.card Rr.Idx ≤ m * m := Nat.mul_le_mul hcl hcr
    calc (↑(Fintype.card Rl.Idx * Fintype.card Rr.Idx) : ℝ)
        ≤ (↑(m * m) : ℝ) := by exact_mod_cast hmm
      _ = (m : ℝ) ^ 2 := by push_cast; ring
  have hdW : (Fintype.card d : ℝ) ≤ (W : ℝ) := by exact_mod_cast hcd
  -- bound the `N·d + d^ω` factor
  have hmid : (Fintype.card (Rl.Idx × Rr.Idx) : ℝ) * (Fintype.card d : ℝ)
        + (Fintype.card d : ℝ) ^ ω ≤ (m : ℝ) ^ 2 * (W : ℝ) + (W : ℝ) ^ ω := by
    have h1 : (Fintype.card (Rl.Idx × Rr.Idx) : ℝ) * (Fintype.card d : ℝ)
        ≤ (m : ℝ) ^ 2 * (W : ℝ) :=
      mul_le_mul hN hdW (Nat.cast_nonneg _) (by positivity)
    have h2 : (Fintype.card d : ℝ) ^ ω ≤ (W : ℝ) ^ ω :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hdW ω
    linarith
  -- bound the polylog factor
  have harg : (Fintype.card (Rl.Idx × Rr.Idx) : ℝ) + (Fintype.card d : ℝ) + 2
      ≤ (m : ℝ) ^ 2 + (W : ℝ) + 2 := by linarith [hN, hdW]
  have hargpos : (1 : ℝ) ≤ (Fintype.card (Rl.Idx × Rr.Idx) : ℝ) + (Fintype.card d : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (Fintype.card (Rl.Idx × Rr.Idx) : ℝ) + (Fintype.card d : ℝ) := by positivity
    linarith
  have hlognn : (0 : ℝ)
      ≤ Real.log ((Fintype.card (Rl.Idx × Rr.Idx) : ℝ) + (Fintype.card d : ℝ) + 2) :=
    Real.log_nonneg hargpos
  have hlogpow : Real.log ((Fintype.card (Rl.Idx × Rr.Idx) : ℝ) + (Fintype.card d : ℝ) + 2) ^ plog
      ≤ Real.log ((m : ℝ) ^ 2 + (W : ℝ) + 2) ^ plog :=
    pow_le_pow_left₀ hlognn (Real.log_le_log (by linarith) harg) _
  have hClwd : (Clw : ℝ) ≤ (Clw : ℝ) := le_refl _
  have hmidnn : (0 : ℝ) ≤ (Fintype.card (Rl.Idx × Rr.Idx) : ℝ) * (Fintype.card d : ℝ)
      + (Fintype.card d : ℝ) ^ ω := by positivity
  refine hle.trans ?_
  exact mul_le_mul (mul_le_mul hClwd hmid hmidnn (Nat.cast_nonneg _)) hlogpow
    (pow_nonneg hlognn _) (by positivity)

/-! ## The size bridge over the region tree -/

/-- **The construction's coresets stay within the Lewis row count `m` and every
region within the feature width `W`** (the circuit analog of the mixture
`SizedRun`).  At every product node, each child coreset has at most `m` points
and the node's own feature type has at most `W` coordinates; there is nothing to
require at a leaf.  A `SizedSparsifyGuarantee`-instrumented random construction
yields this with `m = sampleSize W Clw (ε/(3L)) (η/L)` on every outcome. -/
def SizedReduction (m W : ℕ) : ∀ {d : Type} [Fintype d] {S : Region d}, Reduction S → Prop
  | _, _, _, @Reduction.leaf _ _ _ _ _ => True
  | d, inst, _, @Reduction.node _ _ instl instr _ _ _ M Rl Rr _ _ C =>
      @SizedReduction m W _ instl _ Rl ∧ @SizedReduction m W _ instr _ Rr ∧
        Fintype.card Rl.Idx ≤ m ∧ Fintype.card Rr.Idx ≤ m ∧ @Fintype.card d inst ≤ W

@[simp] theorem sizedReduction_node {m W : ℕ} {dl dr : Type} [Fintype dl] [Fintype dr]
    {d : Type} [Fintype d] {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
    (Rl : Reduction l) (Rr : Reduction r) (ι : Type) [Fintype ι] (C : WPS ι d) :
    SizedReduction m W (Reduction.node M Rl Rr ι C) ↔
      (SizedReduction m W Rl ∧ SizedReduction m W Rr ∧
        Fintype.card Rl.Idx ≤ m ∧ Fintype.card Rr.Idx ≤ m ∧ Fintype.card d ≤ W) := Iff.rfl

/-- **A size-and-cost-instrumented randomised construction** (`thm:pc_fpras`).  The
circuit analog of `SizedRandomRun`: it bundles the accuracy structure
`RandomReduction`, the per-call runtime interface `SC : SparsifyCost`, and the
**size half** `sized` — on *every* coin sequence the coresets stay within the
Cohen–Peng row count `sampleSize W SC.Clw δ η'` and every region within feature
width `W`.  A `SizedSparsifyGuarantee`-instrumented construction inhabits it, so
`circuit_fpras` takes no floating per-outcome hypothesis. -/
structure SizedRandomReduction (SC : SparsifyCost) {V : Vtree} (C : CircuitPair V 1 1) (W : ℕ) (δ η' : ℝ)
    extends Circuit.RandomReduction C δ η' where
  /-- The size half: every construction's coresets/regions stay within
  `sampleSize W SC.Clw δ η'` / width `W`. -/
  sized : ∀ ω, SizedReduction (sampleSize W SC.Clw δ η') W (toRandomReduction.red ω)

/-! ## The tree recursion: `regionCost ≤ steps · perRegion` -/

/-- **The bottom-up construction costs at most `steps · perRegion`.**  A direct
induction on the `Reduction` tree: a leaf costs `0` and has `0` steps; a product
node costs its two children's costs (bounded by `l.steps · Q` and `r.steps · Q`
via the inductive hypotheses) plus one Lewis call (`≤ Q = perRegion Clw ω plog W
m`, by `callCost_tensor_le`), and `l.steps + r.steps + 1 = node.steps`.  Hence

`regionCost SC R ≤ S.steps · perRegion Clw ω plog W m`.

The coordinate type — and with it its `Fintype` instance and the size predicate —
changes along the recursion, so both are reverted into the motive, exactly as in
`Reduction.embeds_exact`. -/
theorem regionCost_le_steps (SC : SparsifyCost) {m W : ℕ}
    {d : Type} [instd : Fintype d] {S : Region d} (R : Reduction S)
    (hsz : SizedReduction m W R) :
    (regionCost SC R : ℝ) ≤ (S.steps : ℝ) * perRegion SC.Clw SC.ω SC.plog W (m : ℝ) := by
  set Clw := SC.Clw with hClwSet
  set ω := SC.ω with hωSet
  set plog := SC.plog with hplogSet
  revert instd hsz
  induction R with
  | leaf X Φ =>
      intro instd hsz
      simp [regionCost_leaf, Region.steps_leaf]
  | @node dl dr instl instr dd l r M Rl Rr ι instι C ihl ihr =>
      intro instd hsz
      rw [sizedReduction_node] at hsz
      obtain ⟨hl, hr, hcl, hcr, hcd⟩ := hsz
      have hIl := @ihl instl hl
      have hIr := @ihr instr hr
      have hq : (SC.callCost (WPS.tensor M Rl.core Rr.core) : ℝ)
          ≤ perRegion Clw ω plog W (m : ℝ) := by
        unfold perRegion
        exact callCost_tensor_le SC M Rl Rr hcl hcr hcd
      rw [regionCost_node, Region.steps_node]
      push_cast
      have hexp : ((l.steps : ℝ) + (r.steps : ℝ) + 1) * perRegion Clw ω plog W (m : ℝ)
          = (l.steps : ℝ) * perRegion Clw ω plog W (m : ℝ)
            + (r.steps : ℝ) * perRegion Clw ω plog W (m : ℝ)
            + perRegion Clw ω plog W (m : ℝ) := by ring
      rw [hexp]
      linarith [hIl, hIr, hq]

/-! ## The capstone: the total circuit operation count -/

/-- **Theorem 3.1, running-time half** (`main.tex:237`).

Given the single Lewis per-call runtime interface `SC` (applied at every region
dimension), a bottom-up construction `R` on a
circuit `C` whose coresets stay within the Cohen–Peng row count
`m = sampleSize W Clw (ε/(3L)) (η/L)` and whose regions have feature width at most
`W` (`SizedReduction`), and the FPRAS calibration positivity, the total
arithmetic operation count of the bottom-up construction obeys

`regionCost ≤ L · perRegion Clw ω plog W S`,  where `L = C.steps` and
`S = Clw·W·log W·(9L²/ε²)·log(L/η) + 1`

is the schedule bound on `m` (`sampleSize_bound_circuit`).  Expanding `perRegion`
and reading off the leading term (`S²·W = O(W³·L⁴/ε⁴·log²(L/η)·log²W)`, times the
outer `L`, plus the additive `L·W^ω`), this is

`O(W³ · L⁵ · ε⁻⁴ · log²(L/η) · log²W) + L·W^ω`,

polynomial in `W, L, 1/ε, log(1/η)`.  The exponent `ω` stays abstract; the two
`Real.log` factors and the solver polylog `(log …)^plog` are kept explicit.

The proof: bound `regionCost` by `L · perRegion Clw ω plog W m` via the tree
recursion `regionCost_le_steps`, then substitute `m ≤ S` through the monotonicity
`perRegion_mono` and the schedule bound `sampleSize_bound_circuit`.  This is the
running-time conjunct that bundles next to `circuit_fpras` (accuracy). -/
theorem circuit_totalCost_le (SC : SparsifyCost)
    {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) (R : C.Reduction) {ε η : ℝ} {W : ℕ}
    (hW : 1 ≤ W) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1) (hL : 0 < C.steps)
    (hsz : SizedReduction (sampleSize W SC.Clw (ε / (3 * C.steps)) (η / C.steps)) W R) :
    (regionCost SC R : ℝ)
      ≤ (C.steps : ℝ) * perRegion SC.Clw SC.ω SC.plog W
          ((SC.Clw : ℝ) * (W : ℝ) * Real.log (W : ℝ) * (9 * (C.steps : ℝ) ^ 2 / ε ^ 2)
            * Real.log (C.steps / η) + 1) := by
  set Clw := SC.Clw with hClwSet
  set ω := SC.ω with hωSet
  set plog := SC.plog with hplogSet
  set m := sampleSize W Clw (ε / (3 * C.steps)) (η / C.steps) with hmdef
  set Sb := (Clw : ℝ) * (W : ℝ) * Real.log (W : ℝ) * (9 * (C.steps : ℝ) ^ 2 / ε ^ 2)
    * Real.log (C.steps / η) + 1 with hSbdef
  -- the tree recursion, instantiated at the whole circuit (`C.steps = C.toRegion.steps`)
  have hind : (regionCost SC R : ℝ) ≤ (C.steps : ℝ) * perRegion Clw ω plog W (m : ℝ) :=
    regionCost_le_steps SC R hsz
  -- schedule bound: `m ≤ Sb`
  have hmS : (m : ℝ) ≤ Sb := by
    rw [hmdef, hSbdef]
    exact sampleSize_bound_circuit (W := W) (L := C.steps) (ε := ε) (η := η)
      (Clw : ℝ) (Nat.cast_nonneg _) hW hL hε hη hη1
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  refine hind.trans ?_
  exact mul_le_mul_of_nonneg_left (perRegion_mono hmnn hmS) (Nat.cast_nonneg _)

end DomainReduction.Cost
