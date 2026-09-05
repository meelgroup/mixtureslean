# Total Variation Distance Estimation through Domain Reduction — a formalization

A machine-checked, `sorry`-free, axiom-clean Lean 4 + Mathlib formalization of
*Total Variation Distance Estimation through Domain Reduction*: an FPRAS for the
total variation distance between mixtures of product distributions, and its
extension to structured probabilistic circuits. Both the **accuracy** and the
**running-time** guarantees are proved, and the two headline theorems bundle them
in a single statement (`accuracy ∧ running time`), the shape of the paper's
"correct **and** fast" theorems.

The reusable half of the development — weighted point sets, the `ℓ¹` evaluation
functional, subspace embeddings and their composition, tensor products of
coresets, multiplicative-error algebra, the abstract propagation invariant over a
tree of regions, and the from-scratch `ℓ₁` Lewis-weight sampling development —
lives in [`arlib`](https://github.com/meelgroup/arlib) as the area
`Arlib.Approximation` (`Coresets/`, `LewisWeights/`). The **structured
probabilistic circuits** it feeds — v-trees, single circuits, and pairs of circuits
over a shared v-tree (`Vtree`, `Circuit V g`, `CircuitPair V gP gQ`) — live in the
same library under `Arlib.KnowledgeCompilation.Probabilistic`. This repository holds
only what is specific to the paper: the models, and the capstones.

## What is proved

### Accuracy

| Paper | Lean |
| --- | --- |
| `wᵀR(x) = P(x) − Q(x)` (eq. 5) | `Mixture.MixturePair.dot_w_R` |
| `d_TV = ½ ∑ₓ \|wᵀR(x)\|` (eq. 5) | `Mixture.MixturePair.tv_eq_half_E` |
| Lemma 2.1, one-step coreset guarantee | `Arlib.Approximation.Embeds` (it *is* the definition) |
| Definition of the hybrid functional `F_t` | `Mixture.Run.F` |
| `F_0 = d_TV(P,Q)`, `F_n = D̃` | `Mixture.Run.F_init`, `Mixture.Run.F_zero` |
| First display of Lemma 2.2's proof | `Mixture.Run.F_cand` |
| Lemma 2.2, propagation of error | `Mixture.Run.embeds_prefix` (stronger; uniform in query) |
| Theorem 2.1, correctness (deterministic core) | `Mixture.Run.output_mem_relErr` |
| **Theorem 2.1, correctness** | **`Mixture.RandomRun.main`** |
| §3.1, `d_TV = ½∑\|⟨a_TV, Φ_root(x)⟩\|` | `Circuit.dot_aTV`, `Circuit.dTV_eq_half_E` |
| §3.2, sum gates introduce no error | `Circuit.sum_layer_free` (`Arlib.Approximation.Embeds.linMap`) |
| §3.2, product gates | `Arlib.Approximation.Embeds.tensor` |
| Lemma 3.2, coreset propagation invariant | `Circuit.invariant` (stronger; uniform in query) |
| Theorem 3.1 (deterministic core) | `Circuit.estimate_mem_relErr` |
| **Theorem 3.1, correctness** | **`Circuit.RandomReduction.main`** |

### Running time (`Cost/`)

The imported Lewis solver's per-call cost `Õ(Nd + d^ω)` enters as the
`SparsifyCost` interface (parallel to `SparsifyGuarantee`, never an axiom);
everything above it is proved.

| Paper | Lean |
| --- | --- |
| the imported solver's per-call cost `Õ(Nd + d^ω)` | `Cost.SparsifyCost` (interface) |
| per-step / total operation count | `Cost.stepCost`, `Cost.totalCost` |
| Theorem 2.1, running time `O(n³k²·maxΩ·ε⁻²·log(n/η)) + n·(2k)^ω` | `Cost.mixture_totalCost_le` |
| Theorem 3.1, running time `O(W³L⁵·ε⁻⁴·log²(L/η)) + L·W^ω` | `Cost.circuit_totalCost_le` |
| **Theorems 2.1 / 3.1, bundled (accuracy ∧ running time)** | **`Model.mixture_fpras`, `Model.circuit_fpras`** |

### The imported subroutine, proved from first principles

`Sparsify` (`thm:lewis_weights`) is Cohen–Peng `ℓ₁` Lewis-weight row sampling. It
enters this repository only as the interfaces above, but its accuracy content is
not merely asserted — it is developed from scratch in
`Arlib.Approximation.LewisWeights`:

| Route | Lean | What it gives |
| --- | --- | --- |
| **B** — importance sampling + ε-net + relative Chernoff | `Lewis.lewis_importance_embeds` | a genuine `(1 ± δ)` `ℓ₁` embedding, all queries at once, at suboptimal size |
| **A** — moment method on the supremum | `Lewis.process_uniform_tail` | the optimal-in-`d` concentration core |
| `momentreduct` (L4 contraction + L5 symmetrization + Khintchine) | `Symmetrize`/`Contraction`/`MomentReduct` | the sampling moment reduced to the empirical energy |

Beyond the paper:

* **The circuit result is proved under the weaker "shared v-tree" hypothesis.**
  The paper compares two circuits of a *common architecture*; the formalization
  requires only a *common v-tree*. `Arlib.KnowledgeCompilation.Probabilistic.CircuitPair V gP gQ`
  is a pair of `arlib` circuits (`…Probabilistic.Circuit`) indexed by the **same**
  `Vtree V`, with independent gate counts `gP`, `gQ` and independent wiring — so
  `P` and `Q` may have entirely different computational structure. The shared `V`
  is explicit in `circuit_fpras`'s signature and load-bearing: `pairRegion`
  recurses on both circuits at once and only typechecks because they share `V`.
* `Mixture.MixturePair.tv_eq_tvDist` and `Circuit.dTV_eq_tvDist` — the estimated
  quantity **is** the total variation distance between two genuine probability
  distributions, in the independent sense of `Arlib.MarkovChains.tvDist`. The
  normalisation hypotheses the paper leaves implicit are isolated as
  `Mixture.IsProb` / `Circuit.IsProb`; in the mixture case `∑ₓ P(x) = 1` is
  *proved* from them (this is the one place the product structure of the
  components is used), while for a circuit normalisation is genuinely an
  assumption about the parameters rather than a consequence of the architecture.
* `Mixture.Run.embeds_prefix` and `Arlib.Approximation.Reduction.embeds_exact` are
  **stronger** than the paper's Lemma 2.2 and Lemma 3.2: they are uniform over
  *all* queries, not only over the aggregate the paper tracks. The paper's own
  route is formalized separately in `Mixture/Hybrid.lean` and is not depended on.
* Both capstones are checked to be **non-vacuous**: `Arlib.Approximation.exactReduction`
  exhibits an inhabitant of the circuit hypothesis for every region tree, and the
  mixture hypothesis is likewise inhabited by the never-sparsify run.

## Reading the development — `Model/` is the audit surface

Read `Model/` and stop. It states the problem, the two algorithms, and the two
theorems, and it contains no proofs. Everything else in the repository proves those
two theorems.

The development has four layers:

| Layer | Where | What it holds |
| --- | --- | --- |
| statement | `Model/` | the problem, the algorithms, the two theorems |
| imported interfaces | `Sparsify.lean`, `SizeGuarantee.lean`, `Model/Prelude/Cost.lean` | the Lewis-weight subroutine, taken as explicit parameters rather than as axioms |
| accuracy proof | `Mixture/`, `Circuit/` | sections 2 and 3 of the paper |
| running-time proof | `Cost/` | section 7, as a step-counted operational model |

All four layers sit on [`arlib`](https://github.com/meelgroup/arlib), which is
imported the same way as Mathlib and holds everything that is not specific to this
paper. The parts used here are `Arlib.Approximation` and
`Arlib.KnowledgeCompilation.Probabilistic`.

The reading path is three files, in this order. `Model/ProblemSetting.lean` fixes the
two quantities the algorithms estimate and proves that each one is a total variation
distance. `Model/Pseudocode.lean` transcribes Algorithms 1 to 3, one definition per
pseudocode line, with no proofs. `Model/Theorem.lean` states the two theorems,
`mixture_fpras` and `circuit_fpras`; each one joins an accuracy bound and a
running-time bound with `∧`.

To check a single claim of the paper rather than read the files in order, use
[`PAPER-MAPPING.md`](PAPER-MAPPING.md). It gives a Lean declaration and a
`file:line` for every numbered object in the paper.

`Model/` is self-contained: every paper-specific name in a `Model/` signature is
defined under `Model/`, and the only outside names come from `arlib` and Mathlib. The
import graph enforces this. `Model/Prelude` imports only `arlib` and Mathlib, and
`ProblemSetting` and `Pseudocode` import only `Model/Prelude`. A reader goes through
the four files below in order and then stops.

0. **`Model/Prelude.lean`** (+ `Prelude/`) — *the vocabulary.* The datatypes
   (`MixturePair`, the circuit pair `Circuit`), the targets (`tv`, `dTV`) with their
   `tvDist` certifications, and the cost interface (`SparsifyCost`, `sampleSize`). The
   analysis and cost layers import *these*, so the audit surface never has to leave
   `Model/` to find what a name means.
1. **`Model/ProblemSetting.lean`** — *the problem.* Fixes the two targets
   `mixtureTV D n` and `circuitTV C` (`= ½ ∑ₓ |P(x) − Q(x)|`, one absolute linear
   test) and **certifies each is `Arlib.MarkovChains.tvDist`** of two genuine
   probability distributions (`mixtureTV_eq_tvDist`, `circuitTV_eq_tvDist`), so the
   headline is a theorem about total variation, not about a surrogate.
2. **`Model/Pseudocode.lean`** — *both algorithms, in the paper's own words.* A
   line-by-line transcription of Algorithm 1 (`alg:fptas`) — parameters, root
   coreset, the extend double-loop, the `Sparsify` call, the returned estimate —
   and of Algorithms 2–3 (`alg:circuit`, `alg:reduce`) — the per-region
   calibration, the leaf enumeration, the product-node candidate, the `Sparsify`
   obligation, the returned estimate. Every definition is tagged with the
   pseudocode line it transcribes, and there are **no proofs of correctness**.
   The extend step is literally one `WPS.hadamard` and the product candidate one
   `WPS.tensor`. This file **imports only `Model/Prelude`**, so it names no analysis
   object; the `rfl`-bridges that identify the transcription with the analysis `Run`
   / `Circuit.estimate` (`candidateExtension_eq_cand`, `isExecution_iff_faithful`,
   `estimate_eq_output`, `circuitEstimate_eq_estimate`) live *outside* `Model/` in
   [`PseudocodeBridge.lean`](DomainReduction/PseudocodeBridge.lean) — mirroring the
   reference `#NFA` development, whose faithfulness lemmas live in `Algorithm/`.
   Both headline theorems are stated over the *transcribed* names, so the analysis
   objects are proof content a referee never has to read.
3. **`Model/Theorem.lean`** — *the guarantees.* Exactly two theorems,
   `mixture_fpras` (`thm:main_fptas`) and `circuit_fpras` (`thm:pc_fpras`), each
   bundling **accuracy ∧ running time** in one `∧` — the accuracy capstone
   (`RandomRun.main` / `Circuit.RandomReduction.main`) and the running-time
   capstone (`Cost.mixture_totalCost_le` / `Cost.circuit_totalCost_le`), read
   through the `Model` names. Each takes only the algorithm's inputs `(ε, η, …)`:
   the per-step calibration `δ = ε/(3n)`, `η' = η/n` is derived by the algorithm
   and sealed inside the run object (`AlgorithmRun` / `AlgorithmReduction`), never
   surfaced as a hypothesis.

## Scope — read this before quoting the result

**Accuracy *and* running time are formalized.** Both headline theorems state, in
one `∧`, the `(ε, η)` accuracy guarantee — *the estimator lands in
`(1 ± ε)·d_TV(P, Q)` with probability at least `1 − η`* — **and** an explicit
polynomial operation-count bound holding on every outcome (`Cost/`).

**Entered as interfaces, never axioms** (so `#print axioms` stays clean):

* **the Lewis subroutine's accuracy** enters as the `SparsifyGuarantee` interface,
  but is *proved from scratch* in `Arlib.Approximation.LewisWeights` (Route B, a
  genuine all-query embedding; Route A, its optimal-in-`d` concentration core; and
  the `momentreduct` sampling-moment reduction);
* **its per-call cost** `Õ(Nd + d^ω)` enters as the `SparsifyCost` interface;
* **its output size** `m = O(d log d · δ⁻² · log(1/η))` enters as
  `SizedSparsifyGuarantee`.

Each is a type taken as an explicit parameter, so the dependency is visible in the
statement. The one piece still left at the hypothesis level is a fully-optimal
*uniform* Lewis-embedding inhabitant — the supremum-level contraction over all
queries — which needs suprema-of-stochastic-processes infrastructure Mathlib
lacks; it is documented, not forced.

One place where the formalization is more careful than the paper: the paper's
per-step failure bound is *conditional* on the (random) coreset handed to the
sparsifier, while the union bound consumes the *unconditional* bound. These agree
by the tower rule, and the obligation is pushed into the `RandomRun.bad_prob`
field a user must discharge. See the docstring of `Mixture/Probability.lean`.

## Verifying "done"

```bash
lake exe cache get   # prebuilt Mathlib oleans; do not compile Mathlib from source
lake build           # must emit zero `declaration uses 'sorry'` warnings
```

```lean
import DomainReduction
-- the two headline theorems (bundled accuracy ∧ running time)
#print axioms DomainReduction.Model.mixture_fpras   -- [propext, Classical.choice, Quot.sound]
#print axioms DomainReduction.Model.circuit_fpras   -- [propext, Classical.choice, Quot.sound]
```

Those three are Mathlib's foundational axioms. Anything else — a `sorryAx`, a
stray custom `axiom` — would mean a result is not actually proved. Every result
named on this page, together with the `Arlib.Approximation` machinery it rests on,
has been checked this way; a clean rebuild from source emits zero
`declaration uses 'sorry'` warnings.

## Layout

`Model/` holds definitions and statements, and no correctness proof. `Mixture/`,
`Circuit/` and `Cost/` hold the proofs, and each directory is named for the part of
the two theorems it establishes. `Sparsify.lean` and `SizeGuarantee.lean` state the
imported Cohen-Peng results as interfaces.

```
DomainReduction.lean          -- root. Imports the whole development, capstones included
DomainReduction/

  Model/                      -- the audit surface. Every paper-specific name in a
                              --   Model/ signature is defined under Model/
    Prelude.lean              -- the vocabulary. Imports only arlib and Mathlib. Re-exports:
    Prelude/
      Mixture.lean            -- section 1.1. MixturePair, the local feature vectors r_t, the
                              --   weight vector w, and d_TV as one absolute linear test
      MixtureTV.lean          -- IsProb D, and mixtureTV = Arlib.MarkovChains.tvDist. The
                              --   mixture target is a total variation distance
      Circuit.lean            -- section 3.1. The total-variation reading of a CircuitPair
                              --   over a shared v-tree: Phi_S, a_TV, dTV, and its tvDist proof
      Cost.lean               -- sampleSize, the Cohen-Peng row count, and SparsifyCost,
                              --   the per-call cost interface
    ProblemSetting.lean       -- (1) the problem. mixtureTV and circuitTV, each proved equal to
                              --   tvDist of two distributions. Imports only Prelude
    Pseudocode.lean           -- (2) the algorithms. Algorithms 1 to 3 transcribed line by line,
                              --   each definition tagged with its pseudocode line. No proofs.
                              --   Imports only Prelude
    Theorem.lean              -- (3) the guarantees. Two theorems, mixture_fpras and
                              --   circuit_fpras, each joining accuracy and running time

  Sparsify.lean               -- the imported accuracy result of Cohen-Peng, as a
                              --   SparsifyGuarantee parameter rather than an axiom
  SizeGuarantee.lean          -- the size-carrying variant. It also promises
                              --   m = O(d log d / delta^2 * log(1/eta)) output rows
  PseudocodeBridge.lean       -- the rfl-bridges proving the transcription equals Run and
                              --   Circuit.estimate. Kept outside Model/ because each one
                              --   names an analysis type

  Mixture/                    -- accuracy for mixtures, section 2
    Algorithm.lean            -- Algorithm 1 as a Run of coresets, the propagation invariant
                              --   embeds_prefix, and the deterministic half of Theorem 2.1
    Hybrid.lean               -- section 2.2 as the paper writes it: the hybrid functional F_t.
                              --   The capstone does not depend on this file
    Probability.lean          -- the union bound over the n steps, giving Theorem 2.1 as
                              --   RandomRun.main

  Circuit/                    -- accuracy for circuits, section 3
    Main.lean                 -- sections 3.2 and 3.3. The bottom-up region-tree construction,
                              --   the invariant of Lemma 3.2, and Theorem 3.1 as
                              --   Circuit.RandomReduction.main

  Cost/                       -- running time, section 7, as a step-counted model
    Model.lean                -- stepCost, totalCost and regionCost: the work that is counted
    Schedule.lean             -- substitutes the calibration delta = eps/(3n), eta' = eta/n and
                              --   d = 2k into sampleSize, then bounds the per-step cost
    Mixture.lean              -- the running-time half of Theorem 2.1: mixture_totalCost_le
    Circuit.lean              -- the running-time half of Theorem 3.1: circuit_totalCost_le.
                              --   This one recurses over the L product regions

papers/peng/                  -- Cohen and Peng, "Lp Row Sampling by Lewis Weights". The source
                              --   paper of the imported subroutine, thm:lewis_weights
PAPER-MAPPING.md              -- a Lean declaration and a file:line for every numbered object
                              --   of the paper
LICENSE                       -- Apache 2.0
lakefile.toml                 -- requires arlib by path as ../arlib. See Build
lean-toolchain                -- leanprover/lean4:v4.15.0
lake-manifest.json            -- the pinned Mathlib revision
```

## Build

The project pins Lean `v4.15.0` and Mathlib `v4.15.0`, matching
[`arlib`](https://github.com/meelgroup/arlib). `lakefile.toml` requires `arlib` by
path as `../arlib`, so place this repository and `arlib` in the same parent
directory.

```bash
# from the parent directory holding this repository
git clone https://github.com/meelgroup/arlib.git
cd <this repository>

lake exe cache get   # downloads prebuilt Mathlib oleans; do not compile Mathlib from source
lake build           # must emit zero `declaration uses 'sorry'` warnings
```

## License

Apache 2.0, following Mathlib. Copyright © 2026 Anonymous Author(s).

## Acknowledgements

Built with the assistance of **Claude** (Anthropic's Claude Code).
