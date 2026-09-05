/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The problem: what `d_TV(P, Q)` is

First of the three `Model/` files.  No algorithm, no approximation: it fixes the
two quantities the FPRASes estimate and certifies that each really is total
variation distance.

* **Mixtures** (§1.1) — `mixtureTV D n`, for `D : MixturePair k Ω` a pair of
  mixtures of `k` product distributions over `∏_{t<n} Ω t`.
* **Circuits** (§3) — `circuitTV C`, for `C` a pair of structured circuits over a
  shared v-tree.

Both unfold to `½ ∑ₓ |P(x) − Q(x)|` in the form that drives the whole paper — a
**single absolute linear test** `½ ∑ₓ |⟨w, R(x)⟩|`, which is exactly what an ℓ¹
subspace embedding preserves, and so what turns a sum over an exponentially large
domain into a coreset problem.

Defining a target proves nothing about total variation, so `mixtureTV_eq_tvDist`
and `circuitTV_eq_tvDist` identify it with `Arlib.MarkovChains.tvDist` — defined
elsewhere for arbitrary finite distributions — under the normalisation hypotheses
`IsProb`.  Those two theorems are separate obligations, not corollaries of the
headlines.

Audit path: this file, then `Model/Pseudocode`, then `Model/Theorem`.
-/
import DomainReduction.Model.Prelude

namespace DomainReduction.Model

open scoped BigOperators
open Arlib Arlib.MarkovChains
open Arlib.KnowledgeCompilation.Probabilistic (Vtree CircuitPair)
open DomainReduction DomainReduction.Mixture

/-! ## The mixture problem -/

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]

/-- **The mixture target** `d_TV(P, Q) = ½ ∑ₓ |P(x) − Q(x)|`, over the first `n`
coordinates.  This is what `mixture_fpras` (`thm:main_fptas`) approximates. -/
noncomputable def mixtureTV (D : MixturePair k Ω) (n : ℕ) : ℝ := D.tv n

/-- `mixtureTV` is `MixturePair.tv` (`rfl`) — the half-ℓ¹ form the capstone is
phrased in. -/
theorem mixtureTV_eq_tv (D : MixturePair k Ω) (n : ℕ) : mixtureTV D n = D.tv n := rfl

/-- **The target really is total variation distance**, in the independent sense of
`Arlib.MarkovChains.tvDist`, once `IsProb` makes the parameters genuine
distributions.  Without this the development would be about a surrogate. -/
theorem mixtureTV_eq_tvDist {D : MixturePair k Ω} (h : Mixture.IsProb D) (n : ℕ) :
    mixtureTV D n = tvDist (D.dist h n) (D.distQ h n) :=
  D.tv_eq_tvDist h n

/-! ## The circuit problem -/

/-- **The circuit target** `d_TV(P, Q)` for a pair of circuits over a shared
v-tree.  This is what `circuit_fpras` (`thm:pc_fpras`) approximates. -/
noncomputable def circuitTV {V : Vtree} (C : CircuitPair V 1 1) : ℝ := Circuit.dTV C

/-- `circuitTV` is `Circuit.dTV` (`rfl`). -/
theorem circuitTV_eq_dTV {V : Vtree} (C : CircuitPair V 1 1) : circuitTV C = Circuit.dTV C := rfl

/-- **The circuit target really is total variation distance**, under `IsProb` (the
root gate computes a distribution).  For circuits this is a genuine assumption on
the parameters, not a consequence of the architecture. -/
theorem circuitTV_eq_tvDist {V : Vtree} {C : CircuitPair V 1 1} (h : Circuit.IsProb C) :
    circuitTV C = tvDist (Circuit.distP h) (Circuit.distQ h) :=
  Circuit.dTV_eq_tvDist h

end DomainReduction.Model
