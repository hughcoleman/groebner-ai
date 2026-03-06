import Groebner.CBuchberger
import Groebner.Defs

/-!
# Bridge: CMvPolynomial ↔ MvPolynomial

This file defines the canonical ring homomorphism

  `embed : CMvPolynomial σ k → MvPolynomial σ k`

from the computable polynomial type to Mathlib's `MvPolynomial`, and develops
the homomorphism lemmas needed to:

1. Transfer correctness properties of the computable division algorithm to the formal side.
2. Prove termination of `CBuchberger.buchbergerLoop` via the Hilbert basis theorem.

## Design

`embedMon` maps a `CMonomial σ` (sorted list of `(variable, exponent)` pairs) to
`σ →₀ ℕ` by summing `Finsupp.single x e` over the variable–exponent list.  Since
`CMonomial σ` stores each variable at most once (canonical form), this sum has
disjoint supports and `(embedMon m) x = m.expOf x` for every `x`.

`embed` then maps each `(m, c)` term to `MvPolynomial.monomial (embedMon m) c` and
sums over the term list.

## Sorry inventory (this file)

* `embedMon_expOf`      — sum-over-disjoint-singletons; needs canonical-form invariant.
* `embedMon_injective`  — follows from `embedMon_expOf`.
* `embedMon_mul`        — exponent-addition after `mergeAdd`; follows from `embedMon_expOf`.
* `embed_add`           — needs `embedMon_injective` to show `normTerms` is transparent.
* `embed_neg`           — list-map over negation.
* `embed_smul`          — scalar multiplication through `monomial`'s linearity.
* `embed_monomialMul`   — monomial-shift commutation with `monomial_mul`.
* `embed_sPolyPoly`     — requires order-compatibility hypothesis (deferred).
* `lmIdeal_strictMono`  — key Buchberger-termination lemma (deferred).
* `WellFoundedRelation` — well-foundedness of `>` on ideals via Hilbert basis theorem.

-/

open MvPolynomial

namespace Bridge

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]
variable {k : Type*} [Field k] [DecidableEq k]

-- ============================================================
-- Embedding
-- ============================================================

/-- Embed a computable monomial into `σ →₀ ℕ` by summing `Finsupp.single x e`
over all `(x, e)` pairs.  The canonical representation of `CMonomial` guarantees
each variable appears at most once, so `(embedMon m) x = m.expOf x`. -/
noncomputable def embedMon (m : CMonomial σ) : σ →₀ ℕ :=
  ((m.toExps : List (σ × ℕ)).map fun (x, e) => Finsupp.single x e).sum

/-- Embed a computable polynomial into `MvPolynomial σ k` by mapping each
`(monomial, coefficient)` pair to `MvPolynomial.monomial (embedMon m) c` and summing. -/
noncomputable def embed (p : CMvPolynomial σ k) : MvPolynomial σ k :=
  ((p.toTerms : List (CMonomial σ × k)).map fun (m, c) =>
    MvPolynomial.monomial (embedMon m) c).sum

-- ============================================================
-- Basic properties of embedMon
-- ============================================================

/-- The `embedMon` of the trivial monomial `1` is `0 : σ →₀ ℕ`. -/
@[simp]
lemma embedMon_one : embedMon (CMonomial.one (σ := σ)) = 0 := by
  simp [embedMon, CMonomial.one, CMonomial.toExps]

/-- `(embedMon m) x = m.expOf x` — the Finsupp value at `x` equals the stored exponent.

Proof sketch: the sum of disjoint singletons evaluates to the unique summand whose
variable matches `x`, which is exactly `m.expOf x`.  Formally this uses the
canonical-form invariant of `CMonomial` (no duplicate variables in `toExps`). -/
lemma embedMon_expOf (m : CMonomial σ) (x : σ) :
    embedMon m x = m.expOf x := by
  sorry

/-- `embedMon` is injective: distinct canonical monomials give distinct Finsupps.
Follows from `embedMon_expOf` and the fact that canonical monomials are determined
by their `expOf` function. -/
lemma embedMon_injective : Function.Injective (embedMon (σ := σ)) := by
  intro a b hab
  -- embedMon a = embedMon b implies expOf x a = expOf x b for all x,
  -- which determines the canonical list uniquely.
  sorry

/-- `embedMon` respects monomial multiplication:
    `embedMon (a * b) = embedMon a + embedMon b`.

Proof: `CMonomial.mul = mergeAdd` sums exponents componentwise, matching
`Finsupp.add`; and `embedMon m x = m.expOf x` (by `embedMon_expOf`). -/
lemma embedMon_mul (a b : CMonomial σ) :
    embedMon (a * b) = embedMon a + embedMon b := by
  ext x
  simp only [Finsupp.add_apply, embedMon_expOf]
  -- Reduces to: (a * b).expOf x = a.expOf x + b.expOf x,
  -- which holds because CMonomial.mul = mergeAdd, which sums exponents.
  sorry

-- ============================================================
-- Basic properties of embed
-- ============================================================

@[simp]
lemma embed_zero : embed (0 : CMvPolynomial σ k) = 0 := rfl

/-- `embed` applied to a single-term polynomial `c * m` gives `monomial (embedMon m) c`. -/
lemma embed_ofMon (m : CMonomial σ) (c : k) (hc : c ≠ 0) :
    embed (CMvPolynomial.ofMon m c) = MvPolynomial.monomial (embedMon m) c := by
  simp [embed, CMvPolynomial.ofMon, CMvPolynomial.toTerms, hc]

/-- A computable polynomial is zero iff its embedding is zero. -/
lemma embed_eq_zero_iff (p : CMvPolynomial σ k) :
    embed p = 0 ↔ p = 0 := by
  sorry

-- ============================================================
-- Homomorphism lemmas
-- ============================================================

/-- `embed` is additive.

Key step: `CMvPolynomial.add` normalizes via `normTerms`, which combines duplicate
monomials by adding coefficients.  Since `embedMon` is injective, two distinct
canonical monomials produce distinct Finsupp keys, so the normalization is
transparent to the `MvPolynomial` sum. -/
lemma embed_add (p q : CMvPolynomial σ k) :
    embed (p + q) = embed p + embed q := by
  sorry

/-- `embed` commutes with negation. -/
lemma embed_neg (p : CMvPolynomial σ k) :
    embed (-p) = -embed p := by
  simp only [embed, CMvPolynomial.neg, CMvPolynomial.toTerms, List.map_map]
  sorry

/-- `embed` commutes with subtraction. -/
@[simp]
lemma embed_sub (p q : CMvPolynomial σ k) :
    embed (p - q) = embed p - embed q := by
  have : p - q = p + (-q) := rfl
  rw [this, embed_add, embed_neg]; ring

/-- `embed` commutes with scalar multiplication. -/
lemma embed_smul (c : k) (p : CMvPolynomial σ k) :
    embed (CMvPolynomial.smul c p) = c • embed p := by
  sorry

/-- `embed` commutes with multiplication by a monomial shift:
    `embed (monomialMul shift p) = monomial (embedMon shift) 1 * embed p`.

Proof: each term `(m, c)` maps to
`monomial (embedMon shift + embedMon m) c = monomial (embedMon shift) 1 * monomial (embedMon m) c`
(by `embedMon_mul` and `MvPolynomial.monomial_mul_monomial`),
then distribute over the sum. -/
lemma embed_monomialMul (shift : CMonomial σ) (p : CMvPolynomial σ k) :
    embed (CMvPolynomial.monomialMul shift p) =
    MvPolynomial.monomial (embedMon shift) 1 * embed p := by
  sorry

-- ============================================================
-- S-polynomial compatibility
-- ============================================================

/-- `embed` commutes with `CBuchberger.sPolyPoly` relative to a compatible formal
monomial order.  "Compatible" means that for each `f : CMvPolynomial σ k`,
`m.degree (embed f)` equals `embedMon (f.leadMon ord).get _`.

This is the key compatibility for lifting the Buchberger criterion from the
computable to the formal side. -/
lemma embed_sPolyPoly (ord : CMonomialOrder σ) (m : MonomialOrder σ)
    (f g : CMvPolynomial σ k) :
    embed (CBuchberger.sPolyPoly ord f g) =
    MonomialOrder.sPolynomial m (embed f) (embed g) := by
  sorry

-- ============================================================
-- Termination infrastructure for buchbergerLoop
-- ============================================================

/-- The leading-monomial ideal of a list of computable polynomials, via `embed`. -/
noncomputable def lmIdeal (ord : CMonomialOrder σ)
    (G : List (CMvPolynomial σ k)) : Ideal (MvPolynomial σ k) :=
  Ideal.span (Set.range fun i : Fin G.length =>
    match (G.get i).leadMon ord with
    | none   => (0 : MvPolynomial σ k)
    | some m => MvPolynomial.monomial (embedMon m) 1)

@[simp]
lemma lmIdeal_nil (ord : CMonomialOrder σ) :
    lmIdeal ord ([] : List (CMvPolynomial σ k)) = ⊥ := by
  simp [lmIdeal, Ideal.span_empty]

/-- When a nonzero reduced remainder `r` is appended to `G`, the leading-monomial
ideal strictly increases.

**Proof sketch**: `r` is fully reduced modulo `G` (no term of `r` has a leading
monomial divisible by any `lm(g)` for `g ∈ G`), so `lm(embed r) ∉ lmIdeal ord G`.
The strict inclusion follows.

This is the key lemma for Buchberger-algorithm termination; deferred because it
requires formalising that `remainderPoly` returns a fully-reduced polynomial. -/
lemma lmIdeal_strictMono (ord : CMonomialOrder σ)
    (G : List (CMvPolynomial σ k))
    (r : CMvPolynomial σ k) (hr : r ≠ 0) :
    lmIdeal ord G < lmIdeal ord (G ++ [r]) := by
  sorry

/-- The strict `>` relation on ideals of `MvPolynomial σ k` is well-founded when
`σ` is finite, as a consequence of the Hilbert basis theorem (which gives the
ascending chain condition on ideals of `MvPolynomial σ k`).

Used as the termination measure for `CBuchberger.buchbergerLoop`. -/
noncomputable instance lmIdealWF [Finite σ] :
    WellFoundedRelation (Ideal (MvPolynomial σ k)) where
  rel := (· > ·)
  -- Follows from IsNoetherianRing (MvPolynomial σ k) (Hilbert basis theorem)
  -- and isNoetherian_iff': IsNoetherian R M ↔ WellFoundedGT (Submodule R M).
  wf := by sorry

end Bridge
