/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The union bound over the `n` steps, and Theorem 2.1

`Mixture.Algorithm` proves the deterministic half of Theorem 2.1: *conditioned on
every one of the `n` sparsification steps meeting its `(1 ± δ)` guarantee*, the
output of Algorithm 1 lies in `(1 ± ε) · d_TV(P, Q)` when `δ = ε/(3n)`.  This
file supplies the missing half, which the paper disposes of in one sentence:

> By the union bound, the algorithm succeeds across all `n` steps with
> probability at least `1 - n η' = 1 - η`.  Conditioned on success, we telescope
> Lemma 2.3 …

* `RandomRun` — a randomised execution of Algorithm 1: one finite probability
  space carrying all of the algorithm's coin tosses, the deterministic `Run` it
  produces on each outcome, and, for each step, a *failure event* of probability
  at most `η'` off which that step's sparsification is a `(1 ± δ)` embedding.
* `RandomRun.faithful_of_no_bad` — off the union of the `n` failure events the
  run is `Run.Faithful δ n`, so `Algorithm`'s deterministic invariant applies.
* `RandomRun.main` — **Theorem 2.1**: with `δ = ε/(3n)` and `η' = η/n`, the
  output is a `(1 ± ε)` approximation of `d_TV(P, Q)` with probability at least
  `1 - η`.

The proof is `Arlib.FinProb.one_sub_card_mul_le_Pr_forall_not` (the union bound
in "no bad event occurs" form) followed by `Arlib.FinProb.Pr_mono`, since the
event "no step failed" is a *subset* of the event "the output is accurate" —
that inclusion is exactly `Run.output_mem_relErr`.

## Where the formalisation is more careful than the paper

**The failure bound is used unconditionally.**  The `bad_prob` field of
`RandomRun` asserts the *unconditional* bound `Pr[bad t] ≤ η'`, and that is what
the union bound consumes.  What Theorem 1.1 actually supplies is a *conditional*
guarantee: the sparsifier invoked at step `t` fails with probability at most `η'`
**given** the weighted point set it was handed — and that input, `cand t`, is
itself a random object, since it is built from the coresets produced by steps
`0, …, t-1`.  The two statements agree after averaging over the past, by the
tower rule: if `Pr[bad t | past] ≤ η'` pointwise then `Pr[bad t] ≤ η'`.  The
paper does not remark on this step, and stating `bad_prob` conditionally would
have forced a model of conditional expectation that nothing else here needs; so
the averaging is placed *outside* the formalisation, in the obligation a user
discharges when constructing a `RandomRun`.  This is a genuine gap between what
is written here and what Theorem 1.1 literally gives, and it is recorded rather
than hidden.

## How `Sparsify.SparsifyGuarantee` connects to `RandomRun`

`DomainReduction.SparsifyGuarantee (Coord k) δ η'` packages exactly the two
things a `RandomRun` needs at each step: an event `bad U` of probability at most
`η'` (`bad_prob`), and the promise `Embeds (1 - δ) (1 + δ) U (out U ω)` for
`ω ∉ bad U` (`succeeds`).  With `δ = ε/(3n)` and `η' = η/n` these are, field for
field, `RandomRun.bad_prob` and `RandomRun.step`; the correspondence is recorded
as `SparsifyGuarantee.supplies_step` below.

**What is not proved.**  That lemma is a restatement, not a construction: this
file does **not** build a `RandomRun` out of a `SparsifyGuarantee`.  Doing so
means constructing the product of the `n` sparsifiers' probability spaces — where
the `t`-th factor's *type* depends on the outcome of the first `t-1`, because the
input handed to the `t`-th call does — together with the pushforward argument
that turns each factor's `bad_prob` into an unconditional bound on the product,
which is the averaging discussed above.  That is a substantial development of
dependent product measures on `Arlib.FinProb`, and it is out of scope here.  A
user of `RandomRun.main` therefore supplies the probability space and the two
probabilistic fields themselves; what this file proves is that *given* them, the
union bound and the deterministic invariant compose to Theorem 2.1.

The size and running-time halves of Theorem 2.1 are not formalised anywhere; see
the module docstring of `DomainReduction.Sparsify`.

No `sorry`.
-/
import DomainReduction.Mixture.Algorithm
import DomainReduction.Sparsify
import Arlib.Probability.UnionBound

namespace DomainReduction.Mixture

open scoped BigOperators
open Finset Arlib Arlib.Approximation

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]

/-! ## Randomised runs -/

/-- A **randomised execution of Algorithm 1**: a finite probability space, the
run it produces on each outcome, and for each step a "failure" event of
probability at most `η'`, off which that step's sparsification meets its
`(1 ± δ)` guarantee.

All of the algorithm's coin tosses — every call to the sparsifier — live in the
single space `space`; `run ω` is the entire deterministic transcript on the coin
sequence `ω`.  The `root` field pins the initial coreset to the paper's
`{(∅, 1, 𝟙)}` on every outcome (it is not random), and `step` says that on the
outcomes where step `t` did not fail, `core (t+1)` is a `(1 ± δ)` subspace
embedding of the candidate extension `cand t`.

`bad_prob` is an **unconditional** bound; see the module docstring for why that
is stronger than what Theorem 1.1 literally gives, and what has to be averaged
to get it. -/
structure RandomRun (D : MixturePair k Ω) (n : ℕ) (δ η' : ℝ) where
  /-- The probability space of all of the algorithm's coin tosses. -/
  space : Arlib.FinProb
  /-- The deterministic transcript produced on a given coin sequence. -/
  run : space.Ω → Run D
  /-- `bad t` is the event that the sparsification at step `t` failed. -/
  bad : ℕ → space.Ω → Prop
  /-- The failure events are events, i.e. decidable. -/
  [badDec : ∀ t, DecidablePred (bad t)]
  /-- Each of the first `n` steps fails with probability at most `η'`. -/
  bad_prob : ∀ t ∈ Finset.range n, space.Pr (Finset.univ.filter (bad t)) ≤ η'
  /-- The run always starts at the paper's root coreset, recorded through its
  evaluation functional. -/
  root : ∀ ω y, ((run ω).core 0).E y = (WPS.exact (Pre Ω 0) (D.R 0)).E y
  /-- Off the failure event, step `t` is a `(1 ± δ)` sparsification of the
  candidate extension. -/
  step : ∀ ω, ∀ t < n, ¬ bad t ω →
      Embeds (1 - δ) (1 + δ) ((run ω).cand t) ((run ω).core (t + 1))

attribute [instance] RandomRun.badDec

namespace RandomRun

variable {D : MixturePair k Ω} {n : ℕ} {δ η' : ℝ}

/-! ## From "no step failed" to `Faithful` -/

omit [∀ t, DecidableEq (Ω t)] in
/-- **Off the union of the `n` failure events, the run is faithful.**

This is the bridge to `Mixture.Algorithm`: `Run.Faithful δ n` is precisely the
conjunction of the root condition and the `n` per-step embedding conditions, and
those are the `root` and `step` fields evaluated at an outcome on which no `bad t`
occurred.  There is no probability here at all — it is a pointwise statement
about a single outcome. -/
theorem faithful_of_no_bad (RR : RandomRun D n δ η') {ω : RR.space.Ω}
    (h : ∀ t ∈ Finset.range n, ¬ RR.bad t ω) : ((RR.run ω).Faithful δ n) :=
  ⟨RR.root ω, fun t ht => RR.step ω t ht (h t (Finset.mem_range.mpr ht))⟩

/-! ## Theorem 2.1 -/

omit [∀ t, DecidableEq (Ω t)] in
/-- **Theorem 2.1 (Correctness).**  With per-step tolerance `δ = ε/(3n)` and
per-step failure probability `η' = η/n`, the output of Algorithm 1 lies in
`(1 ± ε) · d_TV(P, Q)` with probability at least `1 - η`.

The proof is the paper's, in two moves and nothing else.

1. *Union bound.*  `Arlib.FinProb.one_sub_card_mul_le_Pr_forall_not` applied to
   the family `bad 0, …, bad (n-1)` with the uniform bound `η/n` gives
   `1 - n · (η/n) = 1 - η` for the probability that **no** step failed.
2. *Inclusion of events.*  The event "no step failed" is contained in the event
   "the output is accurate": on such an outcome `faithful_of_no_bad` gives
   `Run.Faithful (ε/(3n)) n`, and `Run.output_mem_relErr` — the deterministic
   half of the theorem, where the actual telescoping of Lemma 2.3 happens —
   turns that into membership in `relErr ε (D.tv n)`.  Monotonicity of `Pr`
   finishes.

Note that the statement is vacuously true when `η ≥ 1`; all the content is in the
regime `n · η' < 1`, and no hypothesis on `η` is needed to state it. -/
theorem main {ε η : ℝ} {n : ℕ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (RR : RandomRun D n (ε / (3 * n)) (η / n)) :
    1 - η ≤ RR.space.Pr (Finset.univ.filter
      (fun ω => (RR.run ω).output n ∈ Arlib.relErr ε (D.tv n))) := by
  -- the union bound, in "no bad event occurs" form
  have hub := RR.space.one_sub_card_mul_le_Pr_forall_not
    (Finset.range n) RR.bad RR.bad_prob
  refine le_trans ?_ (le_trans hub (RR.space.Pr_mono ?_))
  · -- `1 - |range n| · (η/n) = 1 - η`
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hcard : ((Finset.range n).card : ℝ) * (η / n) = η := by
      rw [Finset.card_range]; field_simp
    rw [hcard]
  · -- "no step failed" ⊆ "the output is accurate"
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact Run.output_mem_relErr _ hn hε hε1 (RR.faithful_of_no_bad hω)

end RandomRun

/-! ## What a `SparsifyGuarantee` supplies -/

/-- **A `SparsifyGuarantee` at parameters `(δ, η')` is exactly a `RandomRun`'s
per-step data.**  For every input weighted point set `U`, it provides an event of
probability at most `η'` — the shape of `RandomRun.bad_prob` — off which the
output is a `(1 ± δ)` subspace embedding of `U` — the shape of `RandomRun.step`,
with `U := (run ω).cand t` and the output `(run ω).core (t + 1)`.

At the calibration of `RandomRun.main`, `(δ, η') = (ε/(3n), η/n)`, this is
precisely the hypothesis Algorithm 1 invokes at each of its `n` steps.

**This is a restatement, not a construction.**  It does not build a `RandomRun`
from a `SparsifyGuarantee`; that needs the dependent product of the `n`
sparsifiers' probability spaces and the averaging that converts each call's
conditional failure bound into an unconditional one.  See the module docstring:
both are out of scope. -/
theorem SparsifyGuarantee.supplies_step {δ η' : ℝ}
    (S : DomainReduction.SparsifyGuarantee (Coord k) δ η')
    {ι : Type} [Fintype ι] (U : WPS ι (Coord k)) :
    (S.space U).Pr (S.bad U) ≤ η' ∧
      ∀ ω ∉ S.bad U, Embeds (1 - δ) (1 + δ) U (S.out U ω) :=
  ⟨S.bad_prob U, fun ω hω => S.succeeds U ω hω⟩

end DomainReduction.Mixture
