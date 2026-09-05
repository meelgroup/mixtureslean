/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# Faithfulness bridges: the transcription IS the analysis object

The `rfl`-bridges from the paper-named transcription of `Model/Pseudocode` to the
analysis objects (`Mixture.Run`, `Circuit.estimate`).  They live **outside** `Model/`
on purpose: each mentions an analysis type (`Run`, `Circuit.Reduction`) in its
signature, and the audit surface stays self-contained precisely by keeping such
mentions here — exactly as the reference `#NFA` development keeps its faithfulness
lemmas in `Algorithm/`, not in `Model/`.

`Model/Theorem` imports this file and consumes these bridges inside its proof terms,
so the transcribed names remain the ones a referee reads while the correspondence to
the analysis is discharged here.
-/
import DomainReduction.Model.Pseudocode
import DomainReduction.Mixture.Algorithm
import DomainReduction.Circuit.Main

namespace DomainReduction.Model.Pseudocode

open scoped BigOperators
open Arlib
open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic (Vtree CircuitPair Coord)
open DomainReduction DomainReduction.Mixture

/-! ## Mixture: the transcription is the `Run` model -/

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]

/-- `candidateExtension` on a run's coreset is `Run.cand`, the object the analysis
sparsifies (`rfl`). -/
theorem candidateExtension_eq_cand (D : MixturePair k Ω) (Rn : Run D) (t : ℕ) :
    candidateExtension (Rn.core t) D t = Rn.cand t := rfl

/-- **A deterministic execution of Algorithm 1 at per-step tolerance `δ`**: the root
coreset is `C₀` (`line:root`), and each of the `n` `Sparsify` calls (`line:sparsify`)
returns a `(1 ± δ)` embedding of its candidate extension.  Phrased over the analysis
`Run`, so it lives here rather than in `Model/`. -/
def IsExecution (D : MixturePair k Ω) (Rn : Run D) (δ : ℝ) (n : ℕ) : Prop :=
  (∀ y, (Rn.core 0).E y = (rootCoreset D).E y) ∧
  (∀ t, t < n → Embeds (1 - δ) (1 + δ) (candidateExtension (Rn.core t) D t) (Rn.core (t + 1)))

/-- `IsExecution` is `Run.Faithful` (`rfl`) — one predicate, two vocabularies. -/
theorem isExecution_iff_faithful (D : MixturePair k Ω) (Rn : Run D) (δ : ℝ) (n : ℕ) :
    IsExecution D Rn δ n ↔ Rn.Faithful δ n := Iff.rfl

/-- `estimate` on a run's final coreset is `Run.output` (`rfl`) — the object the
capstone bounds. -/
theorem estimate_eq_output (D : MixturePair k Ω) (Rn : Run D) (n : ℕ) :
    estimate D (Rn.core n) = Rn.output n := rfl

/-! ## Circuit: the transcription is `Circuit.estimate` -/

/-- `circuitEstimate` is `Circuit.estimate` (`rfl`) — the object the capstone bounds. -/
theorem circuitEstimate_eq_estimate {V : Vtree} (C : CircuitPair V 1 1) (R : C.Reduction) :
    circuitEstimate C R = Circuit.estimate C R := rfl

end DomainReduction.Model.Pseudocode
