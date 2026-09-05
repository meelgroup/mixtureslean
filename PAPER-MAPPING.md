# Paper → Lean: a statement-by-statement map

Every numbered object of *Total Variation Distance Estimation through Domain Reduction*
and the Lean declaration that formalizes it. The three `Model/` files are the
entry points; everything else is the machinery they assemble.

The table is meant to be **checked, not believed**. Each row gives a declaration name and a
`file:line`, so any entry can be confirmed with

```bash
grep -n "theorem mixture_fpras" DomainReduction/Model/Theorem.lean
```

and any claim of *provenness* with `#print axioms <name>` (it must print exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no project axiom).

Paper labels (`alg:fptas`, `thm:main_fptas`, …) are the LaTeX `\label`s of `main.tex`, so
each row can be located in the sources too.

**Read the "Scope" section at the end before quoting the result.** Both the **accuracy** and
the **running-time** halves of the two headline theorems are formalized (accuracy in `Model/`,
running time in `Cost/`, bundled in the `Model/Theorem` headline theorems). The imported Lewis-weight subroutine's
**accuracy** is proved from first principles in `Arlib.Approximation.LewisWeights` (Route B, a
genuine embedding; Route A, its optimal-in-`d` concentration core; and the `momentreduct`
sampling-moment reduction, `Symmetrize`/`Contraction`/`MomentReduct`); what stays a hypothesis
is only the *inhabitant*-level plumbing (the supremum-level contraction for a fully-optimal
uniform embedding, degeneracy). This map says exactly which is which.

---

## Legend

| | meaning |
|---|---|
| **exact** | the Lean statement says what the paper says (modulo Lean's admissibility side-conditions, which are discharged) |
| **stronger** | Lean proves something strictly stronger, and the paper's statement is an instance |
| **certification** | a statement the paper leaves implicit, made explicit here (e.g. "the target really is total variation distance") |
| **hypothesis** | an imported result entered as an explicit parameter, never an axiom |
| **not formalized** | no Lean counterpart. Stated honestly; do not read the table as claiming otherwise. |

---

## 1. The headline — the `Model/` audit surface

The three files a reader should read, in order, and stop.

| # | Paper | Lean | File | Status |
|---|---|---|---|---|
| Alg 1–3 | `alg:fptas`, `alg:circuit`, `alg:reduce` — both FPRASes, transcribed line by line | `Model.Pseudocode` (whole file) | `DomainReduction/Model/Pseudocode.lean` | **exact** (no proofs; see §4) |
| Thm 2.1 | `thm:main_fptas` — *`Pr[D̃ ∈ (1±ε)·d_TV(P,Q)] ≥ 1−η`* **∧** runtime | `mixture_fpras` | `DomainReduction/Model/Theorem.lean:167` | **exact** (accuracy ∧ running time) |
| Thm 3.1 | `thm:pc_fpras` — the same for structured probabilistic circuit **pairs over a shared v-tree**, **∧** runtime | `circuit_fpras` | `DomainReduction/Model/Theorem.lean:216` | **exact** (accuracy ∧ running time) |

The statement layer holds **exactly two theorems** — one per FPRAS — each **bundled**: it states, in
one `∧`, both the accuracy half (`Pr[D̃ ∈ (1±ε)·d_TV] ≥ 1−η`) and the running-time half (the explicit
operation-count bound on every outcome) — the shape of the paper's "correct **and** fast" theorems,
mirroring the reference's single `approxNFA_countNFA`. The accuracy conjunct is a capstone
(`RandomRun.main` / `Circuit.RandomReduction.main`) read directly through the `Model` names; the
running-time conjunct comes from `Cost/` (`mixture_totalCost_le` / `circuit_totalCost_le`). No
accuracy-only or intermediate results clutter the layer. The theorems take **only the algorithm's
inputs** `(ε, η, …)`: the per-step calibration `δ = ε/(3n)`, `η' = η/n` is derived by the algorithm
(`Pseudocode.stepTolerance` / `Pseudocode.circuitStepTolerance`) and sealed inside the run object
(`AlgorithmRun` / `AlgorithmReduction`), never surfaced as a hypothesis. See §7 and Scope.

---

## 2. The problem — what `d_TV(P, Q)` is (`Model/ProblemSetting`)

| # | Paper | Lean | File | Status |
|---|---|---|---|---|
| §1.1 | the mixture target `d_TV(P, Q) = ½ ∑ₓ \|P(x)−Q(x)\|` | `Model.mixtureTV` | `DomainReduction/Model/ProblemSetting.lean:46` | **exact** |
| §3 | the circuit target `d_TV(P, Q)` | `Model.circuitTV` | `DomainReduction/Model/ProblemSetting.lean:63` | **exact** |
| — | *…the mixture target **is** `Arlib.MarkovChains.tvDist`* | `Model.mixtureTV_eq_tvDist` | `DomainReduction/Model/ProblemSetting.lean:55` | **certification** |
| — | *…the circuit target **is** `tvDist`* | `Model.circuitTV_eq_tvDist` | `DomainReduction/Model/ProblemSetting.lean:71` | **certification** |
| — | *…`mixtureTV = MixturePair.tv` / `circuitTV = Circuit.dTV`* (`rfl` bridges) | `mixtureTV_eq_tv`, `circuitTV_eq_dTV` | `DomainReduction/Model/ProblemSetting.lean` | **exact** (`:= rfl`) |

The `_eq_tvDist` rows are what makes the whole development a theorem about *total variation*
rather than about a convenient surrogate: `tvDist` is defined elsewhere, for arbitrary finite
distributions, knowing nothing about this paper (it comes with `tvDist_comm`, the triangle
inequality, the event characterisation, the data-processing inequality). The normalisation
hypotheses the paper leaves implicit are isolated as `Mixture.IsProb` / `Circuit.IsProb`; in
the mixture case `∑ₓ P(x) = 1` is *proved* from them
(`Mixture.MixturePair.sum_prob`, `Model/Prelude/MixtureTV.lean:147` — the one place the product
structure is used).

---

## 3. The linear-test identity (`Model/Prelude`)

The single observation the whole paper rests on: total variation is one absolute linear test.

| # | Paper | Lean | File | Status |
|---|---|---|---|---|
| eq. 5 | `⟨w, R(x)⟩ = P(x) − Q(x)` | `Mixture.MixturePair.dot_w_R` | `DomainReduction/Model/Prelude/Mixture.lean:156` | **exact** |
| eq. 5 | `d_TV = ½ ∑ₓ \|⟨w, R(x)⟩\|` | `Mixture.MixturePair.tv_eq_half_E` | `DomainReduction/Model/Prelude/Mixture.lean:167` | **exact** |
| §3.1 | `d_TV = ½ ∑ \|⟨a_TV, Φ_root(x)⟩\|` | `Circuit.dot_aTV`, `Circuit.dTV_eq_half_E` | `DomainReduction/Model/Prelude/Circuit.lean:48, 57` | **exact** |

---

## 4. The algorithms, transcribed (`Model/Pseudocode`)

Each definition carries the pseudocode line of `alg:fptas` it transcribes. **No proofs of
correctness live here**, and `Model/Pseudocode` imports *only* `Model/Prelude` — so every
name it uses is `Model/`-local, `arlib`, or Mathlib. The `rfl` bridges that identify the
transcription with the analysis `Run` name an analysis type, so they live *outside* `Model/`
in `DomainReduction.PseudocodeBridge` (as the reference keeps faithfulness in `Algorithm/`).

| Line of `alg:fptas` | Paper | Lean | File:line |
|---|---|---|---|
| `line:parameters` | `δ = ε/(3n)`, `η' = η/n` | `stepTolerance`, `stepFailure` | `Pseudocode.lean:69, 73` |
| `line:sample_size` | `m = Θ(k log k · δ⁻² · log(1/η'))` | `sampleSize` | `Pseudocode.lean:78` |
| `line:root` | `C₀ = {(∅, 1, 𝟙_{2k})}` | `rootCoreset` | `Pseudocode.lean:85` |
| `line:extend_dom` | the leaf `Ω_t` with feature `r_t` | `leaf` | `Pseudocode.lean:92` |
| `line:extend_state`–`line:add` | `U_t = C_{t-1} ⊗ Ω_t` (one Hadamard product) | `candidateExtension` | `Pseudocode.lean:99` |
| `line:sparsify` | `C_t ← Sparsify(U_t, m, η')` — the interface is arlib `Embeds` | *(faithfulness `IsExecution` in `PseudocodeBridge`)* | `PseudocodeBridge.lean:44` |
| `line:return` | `D̃ = ½ ∑_{(z,μ,v)∈C} μ\|wᵀv\|` (over the coreset) | `estimate` | `Pseudocode.lean:119` |

The `rfl` bridges to the analysis model (`DomainReduction.Mixture.Run`), **outside `Model/`**:

| Lean (Pseudocode) | equals (by `rfl`) | Run object | File:line |
|---|---|---|---|
| `candidateExtension (Rn.core t) D t` | `Rn.cand t` | `Run.cand` | `PseudocodeBridge.lean:37` |
| `IsExecution D Rn δ n` | `Rn.Faithful δ n` | `Run.Faithful` | `PseudocodeBridge.lean:49` |
| `estimate D (Rn.core n)` | `Rn.output n` | `Run.output` | `PseudocodeBridge.lean:54` |

### The circuit algorithms (`alg:circuit` driver, `alg:reduce` recursion)

The same treatment for Algorithms 2–3, in the same file.

| Line | Paper | Lean | File:line |
|---|---|---|---|
| `alg:circuit` 2 | `δ = ε/(3L)`, `η' = η/L` | `circuitStepTolerance`, `circuitStepFailure` | `Pseudocode.lean:159, 164` |
| `alg:circuit` 3 | `m = Θ(W log W · δ⁻² · log(1/η'))` | `circuitSampleSize` | `Pseudocode.lean:169` |
| `alg:reduce` 1 | leaf: `C ← {(a, 1, Φ(a)) : a ∈ Ω_i}` | `circuitLeafCoreset` | `Pseudocode.lean:176` |
| `alg:reduce` 2 | sum: `C ← {(z, μ, L_S Φ)}` | *(no counterpart — discharged definitionally; see below)* | — |
| `alg:reduce` 4 | product: `U ← C_h × C_ℓ` | `circuitCandidate` | `Pseudocode.lean:190` |
| `alg:reduce` 5 | `C ← Sparsify(U, m, η')` (the region interface) | `IsCircuitExecution` | `Pseudocode.lean:200` |
| `alg:circuit` 5 | `D̃ = ½ ∑ μ\|⟨a_TV, Φ⟩\|` | `circuitEstimate` | `Pseudocode.lean:221` |

The circuit-side `rfl` bridges. Those touching only `arlib` (`Reduction`) stay in `Model/`;
the one naming the analysis `Circuit.estimate` is in `PseudocodeBridge`:

| Lean (Pseudocode) | equals (by `rfl`) | analysis object | File:line |
|---|---|---|---|
| `(Reduction.leaf X Φ).core` | `circuitLeafCoreset X Φ` | `Reduction.core` | `Pseudocode.lean:181` |
| `IsCircuitExecution C R δ` | `R.Sparsifies δ` | `Reduction.Sparsifies` | `Pseudocode.lean:205` |
| product-node obligation | `Embeds … (circuitCandidate M Rl Rr) Cs` | `sparsifies_node` | `Pseudocode.lean:210` |
| `circuitEstimate C R` | `C.estimate R` | `Circuit.estimate` | `PseudocodeBridge.lean:60` |

**Why `alg:reduce`'s sum case has no row.** The region model has only `leaf` and product `node`
constructors: a sum layer is absorbed into the product node's structure tensor. That is sound
exactly because a sum layer is a *free* change of features (`Circuit.sum_layer_free`,
`Circuit/Main.lean:82`), so the three-case pseudocode becomes a two-constructor model. Recorded
as residual risk 4 in `Model/Theorem.lean`.

---

## 5. The proof — deterministic invariant + union bound

### Mixture (`Mixture/Algorithm`, `Mixture/Probability`)

| # | Paper | Lean | File:line | Status |
|---|---|---|---|---|
| Lem `lem:one_step` | one-step coreset guarantee, `E(U_t,·)≈E(C_t,·)` | `Arlib.Approximation.Embeds` (it *is* the definition) | — | **exact** |
| — | the candidate extension `U_{t+1} = C_t ⊗ Ω_t` | `Run.cand` | `Mixture/Algorithm.lean:80` | **exact** |
| — | a faithful run of Algorithm 1 | `Run.Faithful` | `Mixture/Algorithm.lean:87` | **exact** |
| Lem `lem:propagation` | propagation of error, `(1±δ)^t` on the whole exact prefix | `Run.embeds_prefix` | `Mixture/Algorithm.lean:120` | **stronger** (uniform in query) |
| Thm 2.1 (det. core) | telescoping to `(1±ε)` at `δ=ε/(3n)` | `Run.output_mem_relErr` | `Mixture/Algorithm.lean:157` | **exact** |
| — | randomised execution of Algorithm 1 | `RandomRun` | `Mixture/Probability.lean:104` | — |
| — | off no failure event, the run is faithful | `RandomRun.faithful_of_no_bad` | `Mixture/Probability.lean:139` | **exact** |
| **Thm 2.1** | union bound over `n` steps ⇒ `Pr[accurate] ≥ 1−η` | **`RandomRun.main`** | `Mixture/Probability.lean:164` | **exact** |

### Circuit (`Circuit/Main`)

| # | Paper | Lean | File:line | Status |
|---|---|---|---|---|
| §3.2 "Sum Gates" | a sum layer introduces no error | `Circuit.sum_layer_free` | `Circuit/Main.lean:82` | **exact** |
| §3.2 "Product Gates" | product regions sparsify a Cartesian product | `Arlib.Approximation.Embeds.tensor` (via `Reduction`) | — | **exact** |
| Lem `lem:pc_invariant` | coreset propagation invariant, `(1±δ)^{ℓ(S)}` | `Circuit.invariant` | `Circuit/Main.lean:97` | **stronger** (uniform in query) |
| Thm 3.1 (det. core) | telescoping to `(1±ε)` at `δ=ε/(3L)` | `Circuit.estimate_mem_relErr` | `Circuit/Main.lean:104` | **exact** |
| — | randomised bottom-up construction | `Circuit.RandomReduction` | `Circuit/Main.lean:139` | — |
| **Thm 3.1** | union bound over `L` product regions ⇒ `Pr[accurate] ≥ 1−η` | **`Circuit.RandomReduction.main`** | `Circuit/Main.lean:168` | **exact** |

The deterministic invariants (`embeds_prefix`, `invariant`) are **stronger** than the paper's
Lemma `lem:propagation` / `lem:pc_invariant`: they preserve *every* linear test uniformly, not
only the single aggregate the paper telescopes. The paper's own aggregate route is formalized
separately in `Mixture/Hybrid.lean` and is not depended on.

**The shared v-tree is explicit and load-bearing.** V-trees, single structured circuits, and
the *pair* of two circuits over a shared v-tree are all reusable machinery, defined in **arlib**
under the knowledge-compilation area's probabilistic-circuit substructure —
`Arlib.KnowledgeCompilation.Probabilistic.Vtree`, `…Probabilistic.Circuit V g`, and
`…Probabilistic.CircuitPair V gP gQ` (`Arlib/KnowledgeCompilation/Probabilistic/StructuredCircuit.lean`,
`…/CircuitPair.lean`). A `CircuitPair` is two `arlib` circuits indexed by the **same** `V`. That
shared `V` is the "same v-tree" hypothesis, made explicit in `circuit_fpras`'s signature
(`{V : Vtree} {C : CircuitPair V 1 1}`) and genuinely used: `pairRegion` recurses on both circuits
at once and only typechecks because
they share `V` (mixed leaf/node cases are impossible by the shared index), so a single `(x_h, x_ℓ)`
split and a single block-diagonal tensor serve both blocks and one coreset per region reduces both
circuits. The two circuits are otherwise free — different gate counts `gP`, `gQ` and different
wiring — i.e. **different computational structure over one v-tree**. Two circuits over different
v-trees cannot be paired at all.

---

## 6. The imported subroutine: `Sparsify` = Cohen–Peng Lewis weights (`thm:lewis_weights`)

`Sparsify` (`line:sparsify`) is Cohen–Peng ℓ₁ Lewis-weight row sampling. Its guarantee enters
the development as an explicit **hypothesis**, never an axiom, so `#print axioms` on the
headline stays `[propext, Classical.choice, Quot.sound]`.

| # | Paper | Lean | File:line | Status |
|---|---|---|---|---|
| `thm:lewis_weights` | the ℓ₁ subspace-embedding interface (accuracy) | `DomainReduction.SparsifyGuarantee` | `DomainReduction/Sparsify.lean:101` | **hypothesis** |
| `thm:lewis_weights` (size) | the row count `m = O(d log d · δ⁻² · log(1/η))` | `DomainReduction.SizedSparsifyGuarantee`, `sampleSize` | `DomainReduction/SizeGuarantee.lean:96` (size), `Model/Prelude/Cost.lean:35` | **hypothesis** (interface only) |
| — | *a `SparsifyGuarantee` supplies a `RandomRun`'s per-step data* | `SparsifyGuarantee.supplies_step` | `Mixture/Probability.lean:201` | **exact** (restatement, not a construction) |

### The accuracy half, developed from first principles in `Arlib.Approximation.LewisWeights`

`SparsifyGuarantee` is a *hypothesis* here, but its accuracy content is not merely asserted
elsewhere: the arlib area `Arlib.Approximation.LewisWeights` develops the Cohen–Peng ℓ₁
concentration argument from scratch (their §5–6 / appendix reduction). What is **proved**
there, green and axiom-clean:

| Ingredient | Lean | Module:line |
|---|---|---|
| sub-Gaussian sign MGF | `avg_exp_le` | `Rademacher.lean:104` |
| Khintchine, `𝔼_σ(∑σᵢxᵢ)^{2k} ≤ (2ek∑xᵢ²)^k` | `avg_pow_le` | `Khintchine.lean:51` |
| Lewis-weight defining equation | `IsLewis` | `LinAlg.lean:178` |
| the Lewis moment identity | `sum_sq_lev` | `LinAlg.lean:166` |
| per-row / summed finite moment bound | `avg_row_pow_le`, `avg_sum_row_pow_le` | `Concentration.lean:93, 113` |
| the moment-method tail | `avg_pow_tail` | `Probability.lean` |
| finite moment bound ⇒ high-probability | `momBound_highProb` | `HighProb.lean` |
| ℓ₁ sensitivity bounds | `abs_dot_le_lewis_L1` | `Sensitivity.lean:88` |
| Lewis-weight existence (Banach fixed point) | `exists_isLewis` | `Existence.lean:292` |
| trace identity `∑ᵢ w̄ᵢ = d` | `sum_lewis_eq_card` | `Trace.lean` |

On top of that moment machinery, the area proves the accuracy content of `thm:lewis_weights`
**twice**, by two independent routes:

| Route | Lean | Module | What it gives |
|---|---|---|---|
| **B** — importance sampling + ε-net + relative Chernoff | `lewis_importance_embeds` | `Embed.lean` | a genuine `(1 ± δ)` ℓ₁ subspace embedding, **all queries at once**, off an explicit small failure event; polynomial but **suboptimal** size `O(d² log d · δ⁻²)` |
| **A** — moment method on the supremum (no net, no matrix Chernoff) | `process_uniform_tail`, `process_uniform_tail_le_delta` | `RouteA.lean` | the **optimal-in-`d`** concentration core: `Pr[∃x, ‖Ax‖₁≤1, \|σᵀAx\|≥c] ≤ n(2ekU)^k/c^{2k}`, driven below `δ` at the optimal count `Θ(d · log(n/δ) · ε⁻²)` |

Route B is the sub-Gaussian sign MGF (`Rademacher`) → relative Chernoff (`Bernstein`) →
per-query concentration (`SampleConc`) → Euclidean + Lewis-metric nets (`Net`, `MNet`) →
metric geometry of the two functionals (`EmbedAux`) → union bound (`Embed`). Route A is the
`w̄⁻¹`-orthogonal projection identity (`Projection`) → ℓ₁/ℓ∞ duality (`Duality`) → the
sup-bridge `lewlinf` (`SupBridge`) → Markov on a single nonnegative variable (`RouteA`); the
event-inclusion trick lets it dodge the net entirely, which is what removes the extra `d`.

The **`momentreduct` reduction** (Cohen–Peng's `lem:momentreduct`) is also formalized, for the
*sampling moment*:

| Step | Lean | Module | What it gives |
|---|---|---|---|
| L4 — contraction (exact, per-query) | `avg_abs_sign_pow_eq` | `Contraction.lean` | stripping `\|·\|` inside the sign process leaves its even moments unchanged |
| swap primitive | `Ex_prodFinProb_swapPair` | `SymmSwap.lean` | measure-preserving per-coordinate swap on the product sampler space |
| L5 — symmetrization | `sampled_central_moment_le_symm` | `Symmetrize.lean` | `𝔼_ω[(Ê(y)−‖Ay‖₁)^{2k}] ≤ 2^{2k}·𝔼_{σ,ω}[(∑ᵣσᵣ sval(ωᵣ))^{2k}]` |
| L4∘L5∘Khintchine | `sampled_moment_le_energy` | `MomentReduct.lean` | the sampling moment reduced to the empirical energy `𝔼_ω[(2ek·∑ᵣ sval(ωᵣ)²)^k]` |

**What is still a hypothesis, and why.** Route B already supplies a genuine, inhabitant-grade
all-query embedding, and the `momentreduct` sampling-moment reduction above is proved. The one
remaining step to a *fully-optimal uniform* importance-sampling inhabitant is the
**supremum-level** contraction — uniform over *all* queries at the optimal rate, as opposed to
the exact per-query contraction of `Contraction.lean` — which needs suprema-of-stochastic-
processes infrastructure Mathlib lacks, together with the degeneracy (non-spanning-row)
bookkeeping. Both are documented, not forced; see the roadmap table in
`arlib/Arlib/Approximation/LewisWeights.lean`, `ROUTE_A_PLAN.md`, and
`DomainReduction/SizeGuarantee.lean`.

---

## 7. The running-time halves (`Cost/`)

The complexity clauses of `thm:main_fptas` / `thm:pc_fpras` are formalized in the `Cost/` area.
The imported Lewis solver's per-call cost `Õ(N d + d^ω)` enters as an explicit **interface**,
`SparsifyCost` — exactly parallel to `SparsifyGuarantee`, never an axiom — and everything above
it is proved.

| # | Paper | Lean | File | Status |
|---|---|---|---|---|
| — | the imported solver's per-call cost `Õ(Nd + d^ω)` | `Cost.SparsifyCost` | `Model/Prelude/Cost.lean:48` | **hypothesis** (interface) |
| — | feature-build + per-step cost, summed over the DP | `Cost.totalCost`, `Cost.stepCost` | `Cost/Model.lean` | **exact** |
| Thm 2.1 (runtime) | `O(n³ k² · maxΩ · ε⁻² · log(n/η)) + n·(2k)^ω` | `Cost.mixture_totalCost_le` | `Cost/Mixture.lean` | **exact** |
| Thm 3.1 (runtime) | `O(W³ L⁵ ε⁻⁴ log²(L/η)) + L·W^ω` | `Cost.circuit_totalCost_le` | `Cost/Circuit.lean` | **exact** |
| **Thm 2.1/3.1 (bundled)** | *accuracy ∧ running time*, per outcome | **`Model.mixture_fpras`, `Model.circuit_fpras`** | `Model/Theorem.lean` | **exact** (mirrors reference `approxNFA_countNFA`) |

The headline theorems `mixture_fpras` / `circuit_fpras` are the "correct **and** fast"
statements: one `∧` combining accuracy (`RandomRun.main` / `Circuit.RandomReduction.main`, prob.
`≥ 1−η`) with the operation-count bound holding on *every* outcome. The per-outcome size guarantee
they consume rides on the run object (`AlgorithmRun` / `AlgorithmReduction`) — exactly what a
`SizedSparsifyGuarantee` supplies on every coin sequence — not a floating hypothesis.

---

## Scope — read this before quoting the result

**In scope: accuracy *and* running time.** For both `thm:main_fptas` and `thm:pc_fpras`, what
is proved is the `(ε, η)` accuracy guarantee — *the estimator lands in `(1 ± ε)·d_TV(P, Q)`
with probability at least `1 − η`* — over the paper's telescoping-plus-union-bound argument,
for arbitrary real `ε ∈ [0, 1]`, with the target certified to be `Arlib.MarkovChains.tvDist`
(§2); **and** the polynomial operation-count bound (§7), bundled with accuracy in the
capstones.

**Entered as interfaces, never axioms** (so `#print axioms` stays clean):

1. **The imported Lewis subroutine's guarantee.** Its *accuracy* is a hypothesis here
   (`SparsifyGuarantee`) but is *proved from scratch* in `Arlib.Approximation.LewisWeights` —
   Route B gives a genuine all-query `(1 ± δ)` embedding, Route A its optimal-in-`d`
   concentration core (§6). Its *per-call cost* is the `SparsifyCost` interface (§7).
2. **A single optimal-size `SparsifyGuarantee` inhabitant.** Route B already inhabits the
   accuracy content at suboptimal size, and the `momentreduct` sampling-moment reduction is
   proved (`Symmetrize`/`Contraction`/`MomentReduct`, §6); the one remaining step to a
   fully-optimal *uniform* inhabitant — the supremum-level contraction over all queries — and
   the non-spanning-row degeneracy bookkeeping need process-suprema infrastructure Mathlib lacks
   and are documented, not forced (§6).

**One place the formalization is more careful than the paper.** The union bound consumes an
*unconditional* per-step failure bound (`RandomRun.bad_prob`), whereas `thm:lewis_weights`
literally gives a bound *conditional* on the (random) coreset it is handed. The two agree after
averaging over the past, by the tower rule; that averaging is pushed into the obligation a user
discharges when constructing a `RandomRun`, rather than modelled. See the module docstring of
`Mixture/Probability.lean`.

---

## How to verify

```bash
lake exe cache get        # prebuilt Mathlib oleans (do not compile Mathlib from source)
lake build DomainReduction.Model.Theorem
```

```lean
import DomainReduction.Model.Theorem
-- the two headline theorems (bundled accuracy ∧ running time)
#print axioms DomainReduction.Model.mixture_fpras     -- [propext, Classical.choice, Quot.sound]
#print axioms DomainReduction.Model.circuit_fpras     -- [propext, Classical.choice, Quot.sound]
```

And, for the imported subroutine's accuracy proved from scratch:

```lean
import Arlib.Approximation.LewisWeights
#print axioms Arlib.Approximation.Lewis.lewis_importance_embeds     -- Route B, genuine embedding
#print axioms Arlib.Approximation.Lewis.process_uniform_tail        -- Route A, optimal concentration
```

Any `sorryAx` or stray project axiom would mean a result is not actually proved. Reading
`ProblemSetting → Pseudocode → Theorem` in order tells you exactly what was proved, about which
algorithm, and what was deliberately left out.
