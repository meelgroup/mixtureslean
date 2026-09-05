/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# DomainReduction

A machine-checked formalization of *Total Variation Distance Estimation through
Domain Reduction*: an FPRAS for the total variation distance between mixtures of
product distributions, and its extension to structured probabilistic circuits.

Importing `DomainReduction` pulls in the whole development, capstones included.
The reusable machinery — weighted point sets, the ℓ¹ evaluation functional,
subspace embeddings, tensor products of coresets, multiplicative-error algebra
and the abstract region-tree propagation invariant — lives in `Arlib.Approximation.Coresets`
and is imported from there.

## The two capstones

* `DomainReduction.Mixture.RandomRun.main` — **Theorem 2.1**.  Algorithm 1, run
  with per-step tolerance `ε/(3n)` and per-step failure probability `η/n`,
  outputs a value in `(1 ± ε)·d_TV(P,Q)` with probability at least `1 − η`.
* `DomainReduction.Circuit.RandomReduction.main` — **Theorem 3.1**.  The same for
  the bottom-up construction on a smooth, decomposable, structured circuit pair,
  with the union bound over the `L` product regions.

`DomainReduction.Mixture.MixturePair.tv_eq_tvDist` certifies that the quantity
estimated is the total variation distance between two genuine probability
distributions, in the independent sense of `Arlib.MarkovChains.tvDist`.

## Scope

Both the **accuracy** and **running-time** guarantees are formalized.  The
headline theorems `DomainReduction.Model.mixture_fpras` and
`DomainReduction.Model.circuit_fpras` each bundle *accuracy ∧ running time* into a
single statement (the shape of the paper's "correct and fast" theorems): accuracy
from `Model/Theorem`, and the explicit operation-count bounds from
`DomainReduction.Cost`.  See `DomainReduction.Sparsify` for a precise statement of
what is assumed of the `Sparsify` subroutine and what is out of scope.
-/

import DomainReduction.Sparsify
import DomainReduction.Model.Prelude
import DomainReduction.Mixture.Algorithm
import DomainReduction.Mixture.Hybrid
import DomainReduction.Mixture.Probability
import DomainReduction.Circuit.Main
import DomainReduction.Model.ProblemSetting
import DomainReduction.Model.Pseudocode
import DomainReduction.PseudocodeBridge
import DomainReduction.Model.Theorem
import DomainReduction.Cost.Model
import DomainReduction.Cost.Schedule
import DomainReduction.Cost.Mixture
import DomainReduction.Cost.Circuit
