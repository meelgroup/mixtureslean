/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The main theorems: the FPRAS guarantees

The **statement layer** of the development: in the vocabulary of the problem, what
has been proved.  It introduces no constructions and contains exactly **two
theorems** — one per FPRAS, `mixture_fpras` and `circuit_fpras` — each a one-line
`∧`-assembly of an accuracy capstone (`RandomRun.main` /
`Circuit.RandomReduction.main`) and a running-time capstone (`mixture_totalCost_le`
/ `circuit_totalCost_le`).  No accuracy-only or intermediate results litter this
layer.  Audit path: `Model/Prelude` (the vocabulary), `Model/ProblemSetting` (what
`d_TV(P, Q)` is), `Model/Pseudocode` (both algorithms, transcribed line by line),
then this file.

## Self-containment — the referee never leaves `Model/`

Every paper-specific name a `Model/` *signature* uses is defined **under `Model/`**;
the only outside names are `arlib` (the reusable coreset/probability library,
imported like Mathlib) and Mathlib.  This is enforced structurally, not by
inspection:

* `Model/Prelude` — the vocabulary (the datatypes `MixturePair`, `Circuit`, the
  targets `tv`/`dTV` and their `tvDist` certifications, the cost interface
  `SparsifyCost`, the row count `sampleSize`) — imports **only** `arlib` and Mathlib,
  and the analysis (`DomainReduction.Mixture`/`Circuit`/`Cost`) imports *it*.
* `Model/ProblemSetting` and `Model/Pseudocode` import **only** `Model/Prelude`, so
  by the import graph they cannot mention anything but `Model/` + arlib + Mathlib.
* This file's two *statements* name only `Model/`-local wrappers
  (`mixtureOutput`/`mixtureCost`/`circuitOutput`/`circuitCost`, `mixtureTV`,
  `circuitTV`, `AlgorithmRun`/`AlgorithmReduction`), `arlib` (`relErr`, the run's
  probability space `FinProb`), and Mathlib.  The analysis objects (`Run`,
  `Reduction`, `totalCost`, `regionCost`) appear only *inside the wrapper bodies*
  and *in the proof terms* — reached, not surfaced, exactly as the reference `#NFA`
  development reaches its `Execution`/`Cost` through `pseudocodeOutput`/`realizedCost`.

The faithfulness bridges from the transcription to the analysis (`estimate` is
`Run.output`, `circuitEstimate` is `Circuit.estimate`, `IsExecution` is
`Run.Faithful`) live in `DomainReduction.PseudocodeBridge`, outside `Model/`, since
each names an analysis type — again mirroring the reference, whose faithfulness
lemmas live in `Algorithm/`, not `Model/`.

Neither statement reaches `Sparsify.lean`, `Mixture/Hybrid`, `Arlib.MarkovChains`, or
`Arlib.Approximation.LewisWeights`: those are proof content or separate obligations,
discussed under *Residual risk* below.

## The two guarantees

Each bundles *accuracy ∧ running time* in one statement, over one run and one
outcome space — the shape of the paper's "correct and fast" theorems.

* `mixture_fpras` — **Theorem 2.1** (`thm:main_fptas`), Algorithm 1.
* `circuit_fpras` — **Theorem 3.1** (`thm:pc_fpras`), the bottom-up construction on
  a circuit pair sharing a v-tree.

Accuracy: the transcribed estimator lands in `(1 ± ε)·d_TV(P, Q)` with probability
`≥ 1 − η`.  Running time: on **every** outcome the arithmetic-operation count meets
the explicit polynomial written out in the statement — `O(n³k²·maxΩ·ε⁻²·log(n/η)) +
n·(2k)^ω`, resp. `O(W³L⁵ε⁻⁴log²(L/η)) + L·W^ω`.

Both take **only the algorithm's inputs** `(ε, η, …)`.  The calibration
`δ = ε/(3n)`, `η' = η/n` (circuit: `ε/(3L)`, `η/L`) is computed by the algorithm, so
it lives in `Model/Pseudocode` and inside what it means to be a run — `AlgorithmRun`
/ `AlgorithmReduction` — never as a hypothesis exposing `ε/(3n)`.

Proofs are one-line assemblies: accuracy from `RandomRun.main` /
`Circuit.RandomReduction.main` (a union bound over the sparsification steps composed
with the deterministic telescoping invariant), running time from
`mixture_totalCost_le` / `circuit_totalCost_le`.

## Scope

The `Sparsify` subroutine (Cohen–Peng ℓ₁ Lewis-weight row sampling,
`thm:lewis_weights`) enters as an explicit *hypothesis* — packaged per run by
`RandomRun` / `RandomReduction`, and its per-call cost by `SparsifyCost` — never as
an axiom, so `#print axioms` stays clean.  Its accuracy content is nonetheless
*proved* from first principles in `Arlib.Approximation.LewisWeights`: Route B
(`lewis_importance_embeds`) gives a genuine `(1 ± δ)` embedding uniform over all
queries at suboptimal size `O(d² log d · δ⁻²)`; Route A (`process_uniform_tail`)
gives the optimal-in-`d` count for the Rademacher process; and the `momentreduct`
reduction (symmetrization + Ledoux–Talagrand contraction + Khintchine) is proved for
the sampling moment.  The one remaining gap to a fully-optimal *uniform* inhabitant
is the supremum-level contraction, which needs suprema-of-stochastic-processes
infrastructure Mathlib lacks.

## Residual risk — real gaps that are not `sorry`s

1. **`d_TV` is identified beside the theorem, not inside it.**  The statements bound
   `mixtureTV`/`circuitTV`; that these *are* total variation in the independent sense
   of `tvDist` is `Model/ProblemSetting`'s two `_eq_tvDist` theorems, each under an
   `IsProb` hypothesis.  Read those too.
2. **No statement mentions a sampler.**  `SparsifyGuarantee` is not in either
   closure: the embedding promise is the `step`/`good` field of the run object, the
   size promise the `sized` field.  The theorems are conditional on such a sampler
   existing (Theorem 1.1, out of scope).
3. **The transcription bridges are certified but not all consumed.**  The headlines
   name the transcribed *outputs* and *budgets*; the loop and recursion structure
   enters through run-object fields phrased in analysis vocabulary.  So
   `rootCoreset`, `candidateExtension`, `circuitCandidate` and the two `IsExecution`
   predicates document the correspondence rather than carry it.
4. **Sum gates have no syntactic counterpart** — `alg:reduce`'s sum case is absorbed
   into the product node's structure tensor, sound because a sum layer is a free
   change of features (`Circuit.sum_layer_free`).  Three pseudocode cases, two
   constructors.
5. **`W` is bound to the feature width only through the run object.**
   `circuit_fpras`'s `hW : 1 ≤ W` is positivity; the real constraint is a field of
   `SizedReduction`, reached via `RR.sized`.  The mixture's `hmax` is by contrast
   explicit.
6. **A reduced set is any weighted point set with the embedding property**, not
   necessarily a reweighted subset of the candidate domain.  This strengthens the
   theorems, but `estimate` is literally the paper's `½ ∑ⱼ μⱼ|P_r(zⱼ) − Q_r(zⱼ)|`
   only when the reduction is subset-shaped.
7. **Cost model** — arithmetic operations, fast matrix multiplication with exponent
   `ω`, `n` unary.  No bit-complexity or numerical-stability claim.

`sorry`-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import DomainReduction.Model.ProblemSetting
import DomainReduction.Model.Pseudocode
import DomainReduction.PseudocodeBridge
import DomainReduction.Mixture.Probability
import DomainReduction.Circuit.Main
import DomainReduction.Cost.Mixture
import DomainReduction.Cost.Circuit

namespace DomainReduction.Model

open scoped BigOperators
open Arlib
open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic (Vtree CircuitPair Coord)
open DomainReduction DomainReduction.Mixture DomainReduction.Cost

/-! ## Theorem 2.1 — the mixture FPRAS -/

section Mixture

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]

/-- **A run of Algorithm 1 on inputs `(ε, η)`** — a size-and-cost-instrumented
randomised run whose per-step budgets are the algorithm's own `ε/(3n)`, `η/n`.
Sealing them here is what lets `mixture_fpras` take `(ε, η)` as its only inputs. -/
abbrev AlgorithmRun (SC : SparsifyCost) (D : MixturePair k Ω) (n : ℕ) (ε η : ℝ) :=
  SizedRandomRun SC D n (Pseudocode.stepTolerance ε n) (Pseudocode.stepFailure η n)

/-- The **output** of Algorithm 1 on outcome `ω` of the run `RR`: the transcribed
estimator `Pseudocode.estimate` at the run's final coreset.  A `Model/`-local
wrapper — its body reaches the run object, the headline surface names only this. -/
noncomputable def mixtureOutput {SC : SparsifyCost} {D : MixturePair k Ω} {n : ℕ} {ε η : ℝ}
    (RR : AlgorithmRun SC D n ε η) (ω : RR.space.Ω) : ℝ :=
  Pseudocode.estimate D ((RR.run ω).core n)

/-- The **operation count** of Algorithm 1 on outcome `ω`: `totalCost` at the run.
A `Model/`-local wrapper, as `mixtureOutput`. -/
noncomputable def mixtureCost {SC : SparsifyCost} {D : MixturePair k Ω} {n : ℕ} {ε η : ℝ}
    (RR : AlgorithmRun SC D n ε η) (ω : RR.space.Ω) : ℕ :=
  totalCost SC (RR.run ω) n

/-- **Theorem 2.1** (`thm:main_fptas`): Algorithm 1 is correct and fast, in one
statement — accuracy `∧` running time, over one run and one outcome space.

Everything the algorithm *derives* rides on the run object rather than appearing as
a hypothesis, so the only inputs are `(ε, η, n, k)`, constraints on them, and `hmax`
defining the complexity parameter `maxΩ` in which the bound is stated. -/
theorem mixture_fpras {D : MixturePair k Ω} (SC : SparsifyCost)
    {ε η : ℝ} {n maxΩ : ℕ}
    (hk : 1 ≤ k) (hn : 0 < n) (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hmax : ∀ t, t < n → Fintype.card (Ω t) ≤ maxΩ)
    (RR : AlgorithmRun SC D n ε η) :
    (1 - η ≤ RR.space.Pr (Finset.univ.filter
        (fun ω => mixtureOutput RR ω ∈ Arlib.relErr ε (mixtureTV D n))))
      -- running time: `mixtureCost` = total arithmetic-op count of the run on outcome `ω`
      ∧ (∀ ω, (mixtureCost RR ω : ℝ)
          ≤ (n : ℝ) *
              (let S := (SC.Clw : ℝ) * (2 * k) * Real.log (2 * k) * (9 * (n : ℝ) ^ 2 / ε ^ 2)
                          * Real.log (n / η) + 1;
               S * maxΩ * (2 * k)
                 + (SC.Clw : ℝ) * (S * maxΩ * (2 * k) + (2 * k) ^ SC.ω)
                     * Real.log (S * maxΩ + 2 * k + 2) ^ SC.plog)) :=
  ⟨RandomRun.main hn hε.le hε1 RR.toRandomRun,
   fun ω => mixture_totalCost_le SC (RR.run ω) hk hn hε hη hη1 RR.rowPos (RR.sized ω) hmax⟩

end Mixture

/-! ## Theorem 3.1 — the circuit FPRAS -/

/-- **A run of the circuit algorithm on inputs `(ε, η)`** — as `AlgorithmRun`, with
the per-region budgets `ε/(3L)`, `η/L` (`L = C.steps`) sealed in. -/
abbrev AlgorithmReduction (SC : SparsifyCost) {V : Vtree} (C : CircuitPair V 1 1) (W : ℕ) (ε η : ℝ) :=
  SizedRandomReduction SC C W
    (Pseudocode.circuitStepTolerance ε C) (Pseudocode.circuitStepFailure η C)

/-- The **output** of the circuit algorithm on outcome `ω`: the transcribed estimator
`Pseudocode.circuitEstimate` at the run's root coreset.  A `Model/`-local wrapper. -/
noncomputable def circuitOutput {SC : SparsifyCost} {V : Vtree} {C : CircuitPair V 1 1} {W : ℕ}
    {ε η : ℝ} (RR : AlgorithmReduction SC C W ε η) (ω : RR.space.Ω) : ℝ :=
  Pseudocode.circuitEstimate C (RR.red ω)

/-- The **operation count** of the circuit algorithm on outcome `ω`: `regionCost` at
the run.  A `Model/`-local wrapper. -/
noncomputable def circuitCost {SC : SparsifyCost} {V : Vtree} {C : CircuitPair V 1 1} {W : ℕ}
    {ε η : ℝ} (RR : AlgorithmReduction SC C W ε η) (ω : RR.space.Ω) : ℕ :=
  regionCost SC (RR.red ω)

/-- **Theorem 3.1** (`thm:pc_fpras`): the bottom-up circuit construction is correct
and fast, in one statement — accuracy `∧` running time, over one run and one outcome
space.  `P` and `Q` share only the v-tree `V`; their gate counts and wiring are free.

As on the mixture side the derived quantities ride on the run object, so the only
inputs are `(ε, η)` and constraints on them.  Note `hW : 1 ≤ W` is *positivity only*
— unlike the mixture's `hmax`, it does not bind `W` to the feature width.  That
binding (`Fintype.card d ≤ W` at every region) is a field of the run object, reached
through `RR.sized`; see the closure note in the file header. -/
theorem circuit_fpras {V : Vtree} {C : CircuitPair V 1 1} (SC : SparsifyCost)
    {ε η : ℝ} {W : ℕ}
    (hW : 1 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hL : 0 < C.steps)
    (RR : AlgorithmReduction SC C W ε η) :
    (1 - η ≤ RR.space.Pr (Finset.univ.filter
        (fun ω => circuitOutput RR ω ∈ Arlib.relErr ε (circuitTV C))))
      -- running time: `circuitCost` = total arithmetic-op count of the run on outcome `o`
      ∧ (∀ o, (circuitCost RR o : ℝ)
          ≤ (C.steps : ℝ) *
              (let S := (SC.Clw : ℝ) * (W : ℝ) * Real.log (W : ℝ) * (9 * (C.steps : ℝ) ^ 2 / ε ^ 2)
                          * Real.log (C.steps / η) + 1;
               (SC.Clw : ℝ) * (S ^ 2 * (W : ℝ) + (W : ℝ) ^ SC.ω)
                 * Real.log (S ^ 2 + (W : ℝ) + 2) ^ SC.plog)) :=
  ⟨Circuit.RandomReduction.main hL hε.le hε1 RR.toRandomReduction,
   fun o => circuit_totalCost_le SC C (RR.red o) hW hε hη hη1 hL (RR.sized o)⟩

end DomainReduction.Model
