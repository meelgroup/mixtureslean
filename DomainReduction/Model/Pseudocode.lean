/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The algorithms, transcribed

Second of the three `Model/` files: both paper algorithms in the paper's own
vocabulary, with **no proofs of correctness**.  Every definition names the
pseudocode line it transcribes and is tied to its analysis counterpart by `rfl`,
so `main.tex` and this file can be checked against each other line by line.

The analysis uses its own objects — a `Run` of per-step coresets for mixtures, an
`Arlib.Approximation.Reduction` over the region tree for circuits.  Neither is the
paper's vocabulary, which is why this layer exists: `Model/Theorem` states both
headlines over the *transcribed* names, making those analysis objects proof content
a referee never has to read.

```
Require: marginals for P, Q over ∏_{t=1}^n Ω_t, accuracy ε ∈ (0,1), failure η > 0
1  δ ← ε/(3n) ;  η' ← η/n                                        line:parameters
2  m ← Θ( k log k / δ² · log(1/η') )                             line:sample_size
3  C₀ ← {(∅, 1, 𝟙_{2k})}                                        line:root
4  for t = 1 to n:                                               line:outer
5      U_t ← ∅
6      for (z, μ, v) ∈ C_{t-1}:                                  line:extend_state
7          for x_t ∈ Ω_t:                                        line:extend_dom
8              u ← (z, x_t) ;  u_feat ← v ⊗ r_t(x_t)             line:feature
9              add (u, μ, u_feat) to U_t                         line:add
10     C_t ← Sparsify(U_t, m, η')                                line:sparsify
11 return  D̃ = ½ ∑_{(z,μ,v) ∈ C_n} μ |wᵀv|                       line:return
```


## Self-contained, and the bridges

This file imports **only** `Model/Prelude`, so every name it uses is `Model/`-local,
`arlib`, or Mathlib — it names no analysis object.  The transcription is stated over
the coreset data itself (arlib `WPS`, `Region`, `Reduction`) and the Model
vocabulary.

The `rfl`-bridges that identify the transcription with the analysis `Run` (`estimate
= Run.output`, `candidateExtension = Run.cand`, `IsExecution = Run.Faithful`) and with
`Circuit.estimate` name analysis types, so they live *outside* `Model/` in
`DomainReduction.PseudocodeBridge` — as the reference keeps faithfulness in
`Algorithm/`.  The circuit-side identities that touch only `arlib`
(`circuitLeafCoreset` is a `Reduction.leaf`'s `core`, `IsCircuitExecution =
Reduction.Sparsifies`) stay here.
-/
import DomainReduction.Model.Prelude

namespace DomainReduction.Model.Pseudocode

open scoped BigOperators
open Arlib
open Arlib.Approximation
-- `CircuitPair` is the *pair* of two structured circuits over a shared v-tree
-- (`Arlib.KnowledgeCompilation.Probabilistic`); `DomainReduction.Circuit` (below) is
-- this paper's total-variation reading of such a pair.
open Arlib.KnowledgeCompilation.Probabilistic (Vtree CircuitPair Coord)
open DomainReduction DomainReduction.Mixture

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]

/-! ## Line 1–2: the parameters -/

/-- **`δ = ε/(3n)`** (`line:parameters`) — the per-step tolerance, the telescoping
budget that compounds `n` charges of `(1 ± δ)` to `(1 ± ε)`.  *Derived* from the
inputs `(ε, n)`, so no headline theorem has to expose `ε/(3n)`. -/
@[reducible] noncomputable def stepTolerance (ε : ℝ) (n : ℕ) : ℝ := ε / (3 * n)

/-- **`η' = η/n`** (`line:parameters`) — the per-step failure probability, so the
union bound over `n` steps loses only `η`.  Derived, as `stepTolerance`. -/
@[reducible] noncomputable def stepFailure (η : ℝ) (n : ℕ) : ℝ := η / n

/-- **`m = Θ(k log k · δ⁻² · log(1/η'))`** (`line:sample_size`) — the Cohen–Peng ℓ₁
row count at feature dimension `d = 2k`.  Recorded for the audit only: no accuracy
statement depends on it. -/
noncomputable def sampleSize (k : ℕ) (C δ η' : ℝ) : ℕ :=
  DomainReduction.sampleSize (2 * k) C δ η'

/-! ## Line 3: the root coreset -/

/-- **`C₀ = {(∅, 1, 𝟙_{2k})}`** (`line:root`) — the single empty prefix with the
all-ones feature, i.e. the empty Hadamard product. -/
def rootCoreset (D : MixturePair k Ω) : WPS (Pre Ω 0) (Mixture.Coord k) :=
  WPS.exact (Pre Ω 0) (D.R 0)

/-! ## Lines 5–9: the candidate extension domain -/

/-- **The leaf `Ω_t`** (`line:extend_dom`) — all of coordinate `t`'s domain, each
element with weight `1` and feature `r_t` (the exact weighted point set on `Ω_t`). -/
def leaf (D : MixturePair k Ω) (t : ℕ) : WPS (Ω t) (Mixture.Coord k) :=
  WPS.exact (Ω t) (D.r t)

/-- **`U_t`, the candidate extension domain** (`line:extend_state`–`line:add`) —
every surviving prefix extended by every `x_t ∈ Ω_t`, inheriting the weight and
multiplying features coordinatewise.  The pseudocode's three nested loops are
exactly one Hadamard product. -/
def candidateExtension {ι : Type} [Fintype ι] (C : WPS ι (Mixture.Coord k))
    (D : MixturePair k Ω) (t : ℕ) : WPS (ι × Ω t) (Mixture.Coord k) :=
  WPS.hadamard C (leaf D t)

/-! ## Line 10: the `Sparsify` call

`Sparsify(U_t, m, η')` (`line:sparsify`; Cohen–Peng ℓ₁ Lewis-weight row sampling,
`thm:lewis_weights`) is the external, randomized subroutine.  Its *interface* — the
only thing the analysis uses — is that, off an event of probability `≤ η'`, the
returned `C_t` is a `(1 ± δ)` subspace embedding of `U_t`, uniformly over all
queries; `Embeds` (arlib) is exactly that predicate.  What it means for a whole run
to obey this per step is `Run.Faithful` — an *analysis* object — so, as in the
reference `#NFA` development, the faithfulness bridge to it lives outside `Model/`
(`DomainReduction.PseudocodeBridge`), not here. -/

/-! ## Line 11: the returned estimate -/

/-- **`D̃ = ½ ∑_{(z,μ,v) ∈ C} μ|wᵀv|`** (`line:return`) — the whole output of
Algorithm 1: half the final coreset `C`'s absolute linear test against `w`.  Stated
over the coreset itself (an arlib `WPS`), so no analysis object appears. -/
noncomputable def estimate {ι : Type} [Fintype ι] (D : MixturePair k Ω)
    (C : WPS ι (Mixture.Coord k)) : ℝ :=
  (1 / 2) * C.E D.w

/-! # Algorithms 2–3, transcribed: the circuit FPRAS

```
CircuitTV(P, Q, ε, η):                                          alg:circuit
Require: smooth, decomposable circuits P, Q over a common v-tree V
1  L ← number of product nodes of V
2  δ ← ε/(3L) ;  η' ← η/L                                        alg:circuit L2
3  m ← Θ( W log W / δ² · log(1/η') )                             alg:circuit L3
4  C_root ← ReduceNode(root(V))                                  alg:circuit L4
5  return  D̃ = ½ ∑_{(z,μ,Φ) ∈ C_root} μ |⟨a_TV, Φ⟩|              alg:circuit L5

ReduceNode(v with region S):                                    alg:reduce
1  if S = {X_i} is a leaf:  C ← {(a, 1, Φ_{i}(a)) : a ∈ Ω_i}     (no sparsification)
2  elif v is a sum node with child c:  C ← {(z, μ, L_S Φ)}       (free linear map)
3  else (product node, children h, ℓ):
4      U ← C_h × C_ℓ                                             (the candidate)
5      C ← Sparsify(U, m, η')                                    (the only sparsification)
6  return C
```

A whole run of `ReduceNode` is one `Arlib.Approximation.Reduction` over the region tree:
an inductive whose `leaf` constructor is line 1 and whose `node` constructor *stores* the
index type and coreset chosen at line 5.

**Line 2, the sum case, has no counterpart by construction.**  `Region` has only `leaf` and
product `node`: a sum layer is absorbed into the product node's structure tensor, sound
because a sum layer is a *free* change of features (`Circuit.sum_layer_free`).  So three
cases become two, and line 2 is discharged definitionally — residual risk 4 in
`Model/Theorem`. -/

variable {V : Vtree} {gP gQ : ℕ}

/-! ## `alg:circuit` lines 2–3: the per-region parameters -/

/-- **`δ = ε/(3L)`** (`alg:circuit` line 2) — the per-region tolerance, derived from `ε`
and the region count `L = C.steps`. -/
@[reducible] noncomputable def circuitStepTolerance (ε : ℝ) (C : CircuitPair V 1 1) : ℝ :=
  ε / (3 * C.steps)

/-- **`η' = η/L`** (`alg:circuit` line 2) — the per-region failure probability, so the
union bound over the `L` product regions loses only `η`. -/
@[reducible] noncomputable def circuitStepFailure (η : ℝ) (C : CircuitPair V 1 1) : ℝ :=
  η / C.steps

/-- **`m = Θ(W log W · δ⁻² · log(1/η'))`** (`alg:circuit` line 3) — the row count at
feature width `W`.  Recorded for the audit only. -/
noncomputable def circuitSampleSize (W : ℕ) (Cst δ η' : ℝ) : ℕ :=
  DomainReduction.sampleSize W Cst δ η'

/-! ## `alg:reduce` line 1: the leaf case -/

/-- **`C ← {(a, 1, Φ_i(a)) : a ∈ Ω_i}`** (`alg:reduce` line 1) — a leaf region's domain is
small enough to enumerate exactly, so nothing is sparsified and no error is incurred. -/
def circuitLeafCoreset {d : Type} (X : Type) [Fintype X] [DecidableEq X]
    (Φ : X → d → ℝ) : WPS X d :=
  WPS.exact X Φ

/-- The leaf case is what a `Reduction.leaf` stores (`rfl`). -/
theorem circuitLeafCoreset_eq_core {d : Type} (X : Type) [Fintype X] [DecidableEq X]
    (Φ : X → d → ℝ) :
    (Reduction.leaf X Φ).core = circuitLeafCoreset X Φ := rfl

/-! ## `alg:reduce` line 4: the candidate at a product region -/

/-- **`U ← C_h × C_ℓ`** (`alg:reduce` line 4) — the candidate handed to `Sparsify` at a
product region: the children's coresets paired, weights multiplying and features combining
through the structure tensor `M`.  The circuit analogue of `candidateExtension`. -/
def circuitCandidate {dl dr d : Type} [Fintype dl] [Fintype dr]
    {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
    (Rl : Reduction l) (Rr : Reduction r) : WPS (Rl.Idx × Rr.Idx) d :=
  WPS.tensor M Rl.core Rr.core

/-! ## `alg:reduce` line 5: the `Sparsify` call, and what an execution is -/

/-- **A valid execution of `ReduceNode` at per-region tolerance `δ`**: every product
region's returned coreset `(1 ± δ)`-embeds its candidate `U = C_h × C_ℓ`.  Leaf regions
carry no obligation — line 1 enumerates them exactly. -/
def IsCircuitExecution (C : CircuitPair V gP gQ) (R : C.Reduction) (δ : ℝ) : Prop :=
  R.Sparsifies δ

/-- `IsCircuitExecution` is `Reduction.Sparsifies` (`rfl`) — one predicate, two
vocabularies. -/
theorem isCircuitExecution_iff_sparsifies (C : CircuitPair V gP gQ) (R : C.Reduction) (δ : ℝ) :
    IsCircuitExecution C R δ ↔ R.Sparsifies δ := Iff.rfl

/-- **The line-5 `Sparsify` contract, spelled out** (`rfl`): both children are valid
executions and the chosen coreset `(1 ± δ)`-embeds line 4's candidate. -/
theorem sparsifies_node_candidate {δ : ℝ} {dl dr d : Type} [Fintype dl] [Fintype dr]
    [Fintype d] {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
    (Rl : Reduction l) (Rr : Reduction r) (ι : Type) [Fintype ι] (Cs : WPS ι d) :
    (Reduction.node M Rl Rr ι Cs).Sparsifies δ ↔
      (Rl.Sparsifies δ ∧ Rr.Sparsifies δ ∧
        Embeds (1 - δ) (1 + δ) (circuitCandidate M Rl Rr) Cs) := Iff.rfl

/-! ## `alg:circuit` line 5: the returned estimate -/

/-- **`D̃ = ½ ∑_{(z,μ,Φ) ∈ C_root} μ|⟨a_TV, Φ⟩|`** (`alg:circuit` line 5) — the whole output
of the circuit algorithm: the root coreset tested against `a_TV = (+1, −1)`. -/
noncomputable def circuitEstimate (C : CircuitPair V 1 1) (R : C.Reduction) : ℝ :=
  (1 / 2) * R.core.E Circuit.aTV

end DomainReduction.Model.Pseudocode
