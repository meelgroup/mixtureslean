/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The domain-reduction dynamic program, and its deterministic correctness

Algorithm 1 of the paper, and the deterministic half of Theorem 2.1: *conditioned
on every sparsification step succeeding*, the output is within `(1 ± ε)` of the
total variation distance.  The probabilistic half — the union bound over the `n`
steps — is `Mixture.Probability`.

## What the algorithm is, once the implementation is stripped away

At step `t` the algorithm holds a coreset `C_t` of prefix assignments, forms the
candidate extension `U_{t+1} = C_t × Ω_t` (inheriting weights, multiplying feature
vectors coordinatewise), and sparsifies it to `C_{t+1}`.  The *assignments*
themselves are never used: only the weights and the feature vectors enter any
computation or any estimate.  So a run is modelled as a family of weighted point
sets `Arlib.Approximation.WPS`, and the extension step is literally `WPS.hadamard`.

* `Run` — a family of coresets, one per step, with its own index type at each
  step (the surviving assignments differ from step to step, and their number is
  not known in advance).
* `Run.cand` — the candidate extension `U_{t+1} = C_t ⊗ Ωₜ`.
* `Run.Faithful δ n` — the run starts at the paper's root coreset
  `{(∅, 1, 𝟙)}` and every step is a `(1 ± δ)` sparsification of the candidate.
* `Run.embeds_prefix` — **the invariant**: after `t` steps the coreset reproduces
  every linear test on the *whole* exact prefix domain to within `(1 ± δ)^t`.
  This is stronger than the paper's Lemma 2.3, which tracks only the single
  aggregate `F_t`; `Mixture.Hybrid` derives the paper's statement from it.
* `Run.output_mem_relErr` — the deterministic form of Theorem 2.1, at
  `δ = ε/(3n)`.

The invariant is uniform in the query, and that is the whole reason the argument
works: the future coordinates are not yet fixed when `C_t` is built, so the test
`C_t` will eventually be asked is not known when it is sparsified.

No `sorry`.
-/
import DomainReduction.Model.Prelude.Mixture

namespace DomainReduction.Mixture

open scoped BigOperators
open Finset Arlib Arlib.Approximation

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]

/-! ## Runs of the algorithm -/

/-- A **run of the dynamic program**: the coreset held after each step.

The index type is allowed to vary with the step — the surviving assignments after
step `t` are whatever the sparsifier returned, and their number is not determined
by the input.  Nothing here constrains the coresets; `Run.Faithful` is the
predicate saying that they are the ones Algorithm 1 produces. -/
structure Run (D : MixturePair k Ω) where
  /-- The index type of the coreset held after step `t`. -/
  Idx : ℕ → Type
  [fin : ∀ t, Fintype (Idx t)]
  /-- The coreset held after step `t`. -/
  core : ∀ t, WPS (Idx t) (Coord k)

attribute [instance] Run.fin

namespace Run

variable {D : MixturePair k Ω} (Rn : Run D)

/-- The **leaf weighted point set** at coordinate `t`: the whole domain `Ωₜ`,
every element with weight `1` and feature vector `r_t`. -/
def leaf (D : MixturePair k Ω) (t : ℕ) : WPS (Ω t) (Coord k) :=
  WPS.exact (Ω t) (D.r t)

/-- The **candidate extension domain** `U_{t+1}`: every surviving prefix extended
by every domain element, the weight inherited and the feature vectors multiplied
coordinatewise. -/
def cand (t : ℕ) : WPS (Rn.Idx t × Ω t) (Coord k) :=
  WPS.hadamard (Rn.core t) (leaf D t)

/-- **The run is a run of Algorithm 1 with per-step tolerance `δ`**: it starts at
the root coreset `{(∅, 1, 𝟙)}` — recorded, as everywhere here, only through its
evaluation functional — and each of the first `n` steps sparsifies the candidate
extension to within `(1 ± δ)`. -/
def Faithful (δ : ℝ) (n : ℕ) : Prop :=
  (∀ y, (Rn.core 0).E y = (WPS.exact (Pre Ω 0) (D.R 0)).E y) ∧
  (∀ t, t < n → Embeds (1 - δ) (1 + δ) (Rn.cand t) (Rn.core (t + 1)))

/-! ## The exact prefix domain decomposes as a Hadamard product -/

omit [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)] in
/-- **The extension step is exact on the exact domain.**  The unreduced domain of
prefixes of length `t+1` *is* the Hadamard product of the unreduced domain of
prefixes of length `t` with the domain of coordinate `t`.

This is an equality of weighted point sets, not an isomorphism, because
`Pre Ω (t+1)` is definitionally `Pre Ω t × Ω t` and `R (t+1)` is definitionally
the coordinatewise product.  The only content is `1 = 1 * 1`. -/
theorem exact_succ (D : MixturePair k Ω) (t : ℕ) :
    WPS.exact (Pre Ω (t + 1)) (D.R (t + 1))
      = WPS.hadamard (WPS.exact (Pre Ω t) (D.R t)) (leaf D t) := by
  refine WPS.ext ?_ ?_
  · funext x; simp [leaf, WPS.hadamard, WPS.tensor, WPS.exact]
  · funext x c
    simp [leaf, WPS.exact]

/-! ## The invariant -/

omit [∀ t, DecidableEq (Ω t)] in
/-- **The propagation invariant.**  After `t` faithful steps, the coreset `C_t`
reproduces *every* linear test on the exact domain of prefixes of length `t`, to
within `(1 ± δ)^t`.

The induction step is exactly two moves: the exact domain grows by a Hadamard
product (`exact_succ`), which `Embeds.hadamard` propagates with the *identity*
window on the new coordinate since that coordinate is enumerated exactly; and
then one sparsification, which `Embeds.trans` charges a further `(1 ± δ)`. -/
theorem embeds_prefix {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {n : ℕ}
    (h : Rn.Faithful δ n) :
    ∀ t, t ≤ n → Embeds ((1 - δ) ^ t) ((1 + δ) ^ t)
      (WPS.exact (Pre Ω t) (D.R t)) (Rn.core t) := by
  have h1δ : (0 : ℝ) ≤ 1 - δ := by linarith
  have h1δ' : (0 : ℝ) ≤ 1 + δ := by linarith
  intro t
  induction t with
  | zero =>
      intro _
      simpa using (Embeds.of_E_eq (h.1 ·) : Embeds 1 1 _ (Rn.core 0))
  | succ t ih =>
      intro htn
      have ihm := ih (Nat.le_of_succ_le htn)
      -- the exact domain grows by a Hadamard product, exactly
      have hgrow : Embeds ((1 - δ) ^ t * 1) ((1 + δ) ^ t * 1)
          (WPS.exact (Pre Ω (t + 1)) (D.R (t + 1))) (Rn.cand t) := by
        rw [exact_succ]
        exact Embeds.hadamard (pow_nonneg h1δ t) (pow_nonneg h1δ' t) ihm
          (Embeds.refl (leaf D t))
      -- one sparsification
      have hsp := h.2 t (Nat.lt_of_succ_le htn)
      have := Embeds.trans h1δ h1δ' hgrow hsp
      refine Embeds.mono ?_ ?_ this <;> · rw [pow_succ]; ring_nf; exact le_refl _

/-! ## The deterministic form of Theorem 2.1 -/

/-- The algorithm's **output**: half the weighted sum of absolute linear tests of
the final coreset against `w`. -/
noncomputable def output (n : ℕ) : ℝ := (1 / 2) * (Rn.core n).E D.w

omit [∀ t, DecidableEq (Ω t)] in
/-- **Theorem 2.1, deterministic half.**  With per-step tolerance `δ = ε/(3n)`,
a faithful run's output lies in `(1 ± ε) · d_TV(P, Q)`.

The `ε/(3n)` calibration is `Arlib.Approximation.Between.relErr_of_calibrated`; the
factor `½` passes through because the relative-error window is scale-invariant. -/
theorem output_mem_relErr {ε : ℝ} {n : ℕ} (hn : 0 < n) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h : Rn.Faithful (ε / (3 * n)) n) :
    Rn.output n ∈ relErr ε (D.tv n) := by
  have hδ0 : 0 ≤ ε / (3 * n) := by positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ1 : ε / (3 * n) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hinv := Rn.embeds_prefix hδ0 hδ1 h n le_rfl
  have hcal := Between.relErr_of_calibrated hn hε hε1
    ((WPS.exact (Pre Ω n) (D.R n)).E_nonneg D.w) (hinv D.w)
  rw [D.tv_eq_half_E n, output]
  exact Between.const_mul (by norm_num) hcal

end Run

end DomainReduction.Mixture
