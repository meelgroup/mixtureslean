/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# Prelude: the vocabulary of the audit surface

The bottom of the `Model/` layer — and the bottom of the whole import DAG.  Every
paper-specific name that appears in a *definition* or *statement* of the other three
`Model/` files, and that is not an `arlib` or Mathlib symbol, is defined here (or in
one of the files this re-exports).  So a referee reading `Model/` never has to leave
it to find out what a name means.

It owns:

* **Mixtures** (`Model/Prelude/Mixture`, `Model/Prelude/MixtureTV`) — `MixturePair`,
  the feature vocabulary (`Coord`, `Pre`, `r`, `w`, `R`), the target `tv`, and the
  certification that `tv` is `Arlib.MarkovChains.tvDist` (`IsProb`, `dist`, `distQ`,
  `tv_eq_tvDist`).
* **Circuits** (`Model/Prelude/Circuit`) — the total-variation reading of a circuit
  pair: the TV query `aTV`, the target `dTV`, and its `tvDist` certification (`IsProb`,
  `distP`, `distQ`, `dTV_eq_tvDist`).  The circuit pair itself (`CircuitPair`, its
  region map and `valP`/`valQ` semantics) is reusable machinery and lives in
  `Arlib.KnowledgeCompilation.Probabilistic`.
* **Cost** (`Model/Prelude/Cost`) — the row count `sampleSize` and the imported
  per-call runtime interface `SparsifyCost`.

Because this file sits at the bottom, the analysis (`DomainReduction.Mixture`,
`DomainReduction.Circuit`) and the cost model (`DomainReduction.Cost`) *import* these
datatypes rather than defining them: the heavy machinery is built on the Model
vocabulary, not the other way around.  This is what makes the audit surface
self-contained — exactly the role of `Model/Prelude` in the reference `#NFA`
development.
-/
import DomainReduction.Model.Prelude.Mixture
import DomainReduction.Model.Prelude.MixtureTV
import DomainReduction.Model.Prelude.Circuit
import DomainReduction.Model.Prelude.Cost
