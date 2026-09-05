/-
Copyright (c) 2026 Anonymous Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author(s)
-/
/-
# The hybrid functional, and the paper's own route through §2.2

§2.2 of the paper analyses the dynamic program through a single scalar
*hybrid functional*.  Write `Ω_{>t} = ∏_{j>t} Ω_j` for the future domain and
`S_{>t}(x_{>t}) = ⨂_{j>t} r_j(x_j)` for the exact future multiplier vector.  The
hybrid functional is

  `F_t := ½ ∑_{x_{>t} ∈ Ω_{>t}} E(C_t, w ⊗ S_{>t}(x_{>t}))`,

the estimate one would report if the algorithm stopped sparsifying after step `t`
and enumerated the remaining coordinates exactly.  The two ends of the family are
the two quantities the theorem compares: `F_0 = d_TV(P, Q)` and `F_n = D̃`, the
algorithm's output.  Lemma 2.3 then says that one sparsification step moves `F`
by at most a factor `(1 ± δ)`, and the theorem follows by telescoping.

This file formalises exactly those objects and statements.

* `Suf Ω t m` — assignments to the `m` coordinates `t, …, t+m-1`, nested to the
  *right* (`Suf Ω t (m+1) = Ω t × Suf Ω (t+1) m`), the mirror image of `Pre`.
  The suffix length `m` is carried explicitly rather than as `n - t`: the paper's
  `F_t` is `Run.F Rn t (n - t)`, and writing `m` instead of `n - t` removes every
  truncated subtraction from the development at no mathematical cost.
* `MixturePair.S` — the future multiplier `S_{>t}`.
* `Run.F` — the hybrid functional.
* `Run.F_cand` — the first display of the proof of Lemma 2.3: evaluating the
  hybrid functional on the candidate extension domain `U_{t+1}` returns exactly
  the hybrid functional of `C_t`.  This is "distributivity of the Hadamard
  product" together with the re-indexing of `Ω_t × Ω_{>t}` as `Ω_{≥t}`.
* `Run.propagation` — **Lemma 2.3**.
* `Run.F_zero`, `Run.F_init` — the two endpoint identities `F_n = D̃` and
  `F_0 = d_TV(P, Q)`.

## An honest remark about the status of this file

Nothing else in the development depends on this file, and nothing should.
`Mixture.Algorithm` proves a *strictly stronger* invariant, `Run.embeds_prefix`:
after `t` faithful steps the coreset `C_t` reproduces **every** linear test on the
exact prefix domain to within `(1 ± δ)^t`, uniformly in the query.  Every
statement below is an immediate consequence of that invariant, whereas the
converse fails — `F_t` tracks one aggregate number, and one cannot recover a
uniform guarantee from it.  The uniformity is also the mathematically honest
description of what the algorithm needs, since the future coordinates are not
fixed when `C_t` is sparsified.

This file exists so that each numbered statement of §2.2 has a machine-checked
counterpart in the paper's own formulation, not because the capstone theorems
route through it.

Every statement below is fully proved; there are no unproved placeholders.
-/
import DomainReduction.Mixture.Algorithm

namespace DomainReduction.Mixture

open scoped BigOperators
open Finset Arlib Arlib.Approximation

/-! ## Suffix assignments -/

/-- **Assignments to the `m` coordinates `t, t+1, …, t+m-1`.**  The recursion
peels off the *first* coordinate, `Suf Ω t (m+1) = Ω t × Suf Ω (t+1) m`, so the
type is nested to the right and splitting off the coordinate `t` — the one the
algorithm is about to consume — is a definitional projection.  This is the mirror
image of the choice made for `Pre`, which is nested to the left because the
algorithm *appends* there; the two conventions are reconciled, once and for all,
by `preSufEquiv`. -/
def Suf (Ω : ℕ → Type) : ℕ → ℕ → Type
  | _, 0 => PUnit
  | t, m + 1 => Ω t × Suf Ω (t + 1) m

instance instFintypeSuf (Ω : ℕ → Type) [∀ t, Fintype (Ω t)] : ∀ t m, Fintype (Suf Ω t m)
  | _, 0 => inferInstanceAs (Fintype PUnit)
  | t, m + 1 => @instFintypeProd _ _ _ (instFintypeSuf Ω (t + 1) m)

instance instDecidableEqSuf (Ω : ℕ → Type) [∀ t, DecidableEq (Ω t)] :
    ∀ t m, DecidableEq (Suf Ω t m)
  | _, 0 => inferInstanceAs (DecidableEq PUnit)
  | t, m + 1 => @instDecidableEqProd _ _ _ (instDecidableEqSuf Ω (t + 1) m)

/-- The empty suffix is a one-point type. -/
instance instUniqueSuf (Ω : ℕ → Type) (t : ℕ) : Unique (Suf Ω t 0) :=
  inferInstanceAs (Unique PUnit)

/-- **Summing over the empty suffix** is evaluating at its unique point. -/
theorem sum_suf_zero {M : Type*} [AddCommMonoid M] {Ω : ℕ → Type} [∀ t, Fintype (Ω t)]
    (t : ℕ) (f : Suf Ω t 0 → M) :
    ∑ z : Suf Ω t 0, f z = f PUnit.unit := by
  rw [Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- **Summing over a nonempty suffix** splits off its first coordinate.  This is
nothing but `Fintype.sum_prod_type`, since `Suf Ω t (m+1)` *is* the product
`Ω t × Suf Ω (t+1) m`. -/
theorem sum_suf_succ {M : Type*} [AddCommMonoid M] {Ω : ℕ → Type} [∀ t, Fintype (Ω t)]
    (t m : ℕ) (f : Suf Ω t (m + 1) → M) :
    ∑ z : Suf Ω t (m + 1), f z = ∑ a : Ω t, ∑ z : Suf Ω (t + 1) m, f (a, z) :=
  Fintype.sum_prod_type f

/-! ## The future multiplier vector -/

namespace MixturePair

variable {k : ℕ} {Ω : ℕ → Type} (D : MixturePair k Ω)

/-- The **exact future multiplier vector** `S_{>t}(x_{>t}) = ⨂_{j>t} r_j(x_j)`,
here indexed by the *number* `m` of future coordinates that are still enumerated
exactly rather than by `n - t`.  The empty product is the all-ones vector. -/
def S : (t m : ℕ) → Suf Ω t m → Coord k → ℝ
  | _, 0, _ => fun _ => 1
  | t, m + 1, z => fun c => D.r t z.1 c * S (t + 1) m z.2 c

@[simp] theorem S_zero (t : ℕ) (z : Suf Ω t 0) : D.S t 0 z = fun _ => 1 := rfl

@[simp] theorem S_succ (t m : ℕ) (z : Suf Ω t (m + 1)) (c : Coord k) :
    D.S t (m + 1) z c = D.r t z.1 c * D.S (t + 1) m z.2 c := rfl

end MixturePair

/-! ## Reassociating a Hadamard product inside a linear test -/

/-- **Distributivity of the Hadamard product**, in the form the proof of Lemma 2.3
uses it: a linear test of `y` against a coordinatewise product `v ⊙ u` is a linear
test of the *modified query* `y ⊙ u` against `v`.

This is the algebraic reason the extension step is invisible to the analysis: the
new coordinate's local feature vector can be moved out of the point's feature and
into the query, where the sparsification guarantee — which is uniform in the
query — absorbs it. -/
theorem dot_mul_right {k : ℕ} (y v u : Coord k → ℝ) :
    dot y (fun c => v c * u c) = dot (fun c => y c * u c) v := by
  simp only [dot]
  exact Finset.sum_congr rfl fun c _ => by ring

/-! ## The hybrid functional -/

namespace Run

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]
variable {D : MixturePair k Ω} (Rn : Run D)

/-- The paper's **hybrid functional** `F_t`: the accumulated TV distance evaluated
from the coreset held after `t` steps, with the remaining `m` coordinates still
enumerated exactly,

  `F_t = ½ ∑_{x_{>t}} E(C_t, w ⊗ S_{>t}(x_{>t}))`.

The paper's `F_t` is `Run.F Rn t (n - t)`; carrying the number `m` of remaining
coordinates explicitly instead of `n - t` avoids all truncated `Nat` subtraction,
and the two endpoints are then `Run.F Rn n 0 = D̃` (`Run.F_zero`) and
`Run.F Rn 0 n = d_TV(P, Q)` (`Run.F_init`). -/
noncomputable def F (Rn : Run D) (t m : ℕ) : ℝ :=
  (1 / 2) * ∑ z : Suf Ω t m, (Rn.core t).E (fun c => D.w c * D.S t m z c)

/-! ### The candidate extension changes nothing -/

omit [∀ t, DecidableEq (Ω t)] in
/-- **The functional of the candidate extension, one coordinate at a time.**
`E(U_{t+1}, y) = ∑_{a ∈ Ω_t} E(C_t, y ⊙ r_t(a))`: the extension domain's
functional at a query `y` is the sum, over the values of the new coordinate, of
the old coreset's functional at the query modified by that value's local feature
vector.

This is `dot_mul_right` applied under the absolute value, plus Fubini on the
product index type `Idx t × Ω t`. -/
theorem cand_E (t : ℕ) (y : Coord k → ℝ) :
    (Rn.cand t).E y = ∑ a : Ω t, (Rn.core t).E (fun c => y c * D.r t a c) := by
  have key : ∀ (i : Rn.Idx t) (a : Ω t),
      (Rn.cand t).wt (i, a) * |dot y ((Rn.cand t).feat (i, a))|
        = (Rn.core t).wt i * |dot (fun c => y c * D.r t a c) ((Rn.core t).feat i)| := by
    intro i a
    have hf : (Rn.cand t).feat (i, a) = fun c => (Rn.core t).feat i c * D.r t a c := by
      funext c; simp [Run.cand, Run.leaf]
    rw [hf, dot_mul_right]
    simp [Run.cand, Run.leaf]
  rw [WPS.E_apply, ← Finset.univ_product_univ, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [WPS.E_apply]
  exact Finset.sum_congr rfl fun i _ => key i a

omit [∀ t, DecidableEq (Ω t)] in
/-- **The candidate extension changes nothing.**  Evaluating the hybrid functional
on the candidate extension domain `U_{t+1}` with `m` coordinates remaining gives
exactly the hybrid functional of `C_t` with `m+1` remaining.

This is the first display of the proof of Lemma 2.3: by the definition of `U_t`
and distributivity of the Hadamard product, the double sum over `Ω_t × Ω_{>t}`
re-indexes as a single sum over `Ω_{≥t}`. -/
theorem F_cand (t m : ℕ) :
    (1 / 2) * ∑ z : Suf Ω (t + 1) m, (Rn.cand t).E (fun c => D.w c * D.S (t + 1) m z c)
      = Rn.F t (m + 1) := by
  rw [Run.F, sum_suf_succ]
  congr 1
  simp only [Rn.cand_E]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun z _ => ?_
  congr 1
  funext c
  simp only [MixturePair.S_succ]
  ring

/-! ### Lemma 2.3 -/

omit [∀ t, DecidableEq (Ω t)] in
/-- **Lemma 2.3 (Propagation of Error).**  Conditioned on the sparsification at
step `t` succeeding, `(1-δ) F_t ≤ F_{t+1} ≤ (1+δ) F_t` — here with the remaining
coordinate count made explicit, so that the paper's `F_{t-1}, F_t` are
`Run.F Rn t (m+1)` and `Run.F Rn (t+1) m`.

The proof is the paper's: `F_cand` identifies the hybrid functional of `C_t` with
that of the candidate extension `U_{t+1}`, and then the sparsification guarantee
is applied at each of the queries `w ⊗ S_{>t}(x_{>t})` separately and summed —
a positive linear operation, so the window survives. -/
theorem propagation {δ : ℝ} {t m : ℕ}
    (hsp : Embeds (1 - δ) (1 + δ) (Rn.cand t) (Rn.core (t + 1))) :
    Between (1 - δ) (1 + δ) (Rn.F (t + 1) m) (Rn.F t (m + 1)) := by
  rw [← Rn.F_cand t m, Run.F]
  refine Between.const_mul (by norm_num) ?_
  exact Between.sum Finset.univ _ _ fun z _ => hsp _

/-! ### The endpoint `F_n = D̃` -/

omit [∀ t, DecidableEq (Ω t)] in
/-- `F_n = D̃`: with no coordinates remaining the hybrid functional is the
algorithm's output.  The future domain is a point and the future multiplier is
the all-ones vector, so the only query is `w` itself. -/
theorem F_zero (n : ℕ) : Rn.F n 0 = Rn.output n := by
  rw [Run.F, Run.output, sum_suf_zero]
  congr 2
  funext c
  simp

end Run

/-! ## Prefixes and suffixes assemble into prefixes -/

/-- Transporting a prefix assignment along an equality of lengths.  Only ever used
to repair the difference between `t + 1 + m` and `t + (m + 1)`, which is an
equality of naturals but not a definitional one. -/
def preCast (Ω : ℕ → Type) {a b : ℕ} (h : a = b) : Pre Ω a ≃ Pre Ω b :=
  Equiv.cast (congrArg (Pre Ω) h)

/-- **Prefix and suffix assemble into a longer prefix.**  A prefix of length `t`
followed by `m` further coordinates is a prefix of length `t + m`.

The two types are genuinely different — `Pre` nests to the left and `Suf` to the
right — so this equivalence, and not a definitional equality, is what transports
sums between them. -/
def preSufEquiv (Ω : ℕ → Type) : (t m : ℕ) → (Pre Ω t × Suf Ω t m) ≃ Pre Ω (t + m)
  | t, 0 => Equiv.prodPUnit (Pre Ω t)
  | t, m + 1 =>
      ((Equiv.prodAssoc (Pre Ω t) (Ω t) (Suf Ω (t + 1) m)).symm.trans
          (preSufEquiv Ω (t + 1) m)).trans (preCast Ω (by omega))

namespace MixturePair

variable {k : ℕ} {Ω : ℕ → Type} (D : MixturePair k Ω)

/-- The accumulated feature vector is unchanged by transporting along an equality
of prefix lengths. -/
theorem R_preCast {a b : ℕ} (h : a = b) (x : Pre Ω a) (c : Coord k) :
    D.R b (preCast Ω h x) c = D.R a x c := by
  subst h; rfl

/-- **The accumulated feature vector splits as prefix times future multiplier.**
`R_{≤t+m}(x_{≤t} · x_{>t}) = R_{≤t}(x_{≤t}) ⊙ S_{>t}(x_{>t})`, which is the
statement that `preSufEquiv` is compatible with the feature maps.  Proved by the
same recursion that defines the equivalence. -/
theorem R_preSufEquiv (t m : ℕ) (x : Pre Ω t) (z : Suf Ω t m) (c : Coord k) :
    D.R (t + m) (preSufEquiv Ω t m (x, z)) c = D.R t x c * D.S t m z c := by
  induction m generalizing t x with
  | zero =>
      simp only [MixturePair.S_zero, mul_one]
      rfl
  | succ m ih =>
      obtain ⟨a, z⟩ := z
      rw [show preSufEquiv Ω t (m + 1) (x, (a, z))
            = preCast Ω (by omega) (preSufEquiv Ω (t + 1) m ((x, a), z)) from rfl,
        R_preCast, ih (t + 1) (x, a) z]
      simp only [S_succ, R_succ]
      ring

end MixturePair

namespace Run

variable {k : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, DecidableEq (Ω t)]
variable {D : MixturePair k Ω} (Rn : Run D)

omit [∀ t, DecidableEq (Ω t)] in
/-- **Summing the exact prefix domain against the future multipliers reassembles
the exact domain of length `N = t + m`.**  This is the identity that makes the
hybrid functional at time `0` equal to the total variation distance: enumerating
prefixes of length `t` and suffixes of length `m` separately, with the suffix
folded into the query, is the same as enumerating prefixes of length `t + m` and
testing against `w`. -/
theorem sum_prefix_suffix (t m N : ℕ) (hN : t + m = N) :
    ∑ p : Pre Ω t × Suf Ω t m, |dot (fun c => D.w c * D.S t m p.2 c) (D.R t p.1)|
      = ∑ x : Pre Ω N, |dot D.w (D.R N x)| := by
  refine Fintype.sum_equiv ((preSufEquiv Ω t m).trans (preCast Ω hN)) _ _ ?_
  rintro ⟨x, z⟩
  congr 1
  rw [← dot_mul_right]
  simp only [dot]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Equiv.trans_apply, D.R_preCast, D.R_preSufEquiv]

/-! ### The endpoint `F_0 = d_TV(P, Q)` -/

omit [∀ t, DecidableEq (Ω t)] in
/-- `F_0 = d_TV(P,Q)`: with the root coreset and all `n` coordinates remaining, the
hybrid functional is the total variation distance.

The root coreset is the single empty assignment with weight `1` and the all-ones
feature vector, so the hybrid functional at time `0` is the sum, over all
assignments to *all* `n` coordinates, of `|⟨w, R(x)⟩|` — halved, this is
`d_TV(P, Q)` by `MixturePair.tv_eq_half_E`.  The only real content is the
re-indexing `sum_prefix_suffix`. -/
theorem F_init (n : ℕ)
    (hroot : ∀ y, (Rn.core 0).E y = (WPS.exact (Pre Ω 0) (D.R 0)).E y) :
    Rn.F 0 n = D.tv n := by
  have h1 : ∑ z : Suf Ω 0 n, (Rn.core 0).E (fun c => D.w c * D.S 0 n z c)
      = ∑ p : Pre Ω 0 × Suf Ω 0 n, |dot (fun c => D.w c * D.S 0 n p.2 c) (D.R 0 p.1)| := by
    rw [Fintype.sum_prod_type_right]
    exact Finset.sum_congr rfl fun z _ => by rw [hroot, WPS.E_exact]
  rw [Run.F, D.tv_eq_half_E n, WPS.E_exact, h1,
    sum_prefix_suffix (D := D) 0 n n (Nat.zero_add n)]

end Run

end DomainReduction.Mixture
