import Groebner.CMonomialOrder

/-!
# Computable Buchberger's Algorithm

This file provides the fully computable implementation of Buchberger's algorithm
for computing Gröbner bases, using the types and operations from `CMvPolynomial`
and `CMonomialOrder`.

## Main definitions

* `reduceStep ord b f` — one reduction step: subtract a multiple of `b` from `f`
  if `lm(b) | lm(f)`.
* `remainderPoly ord G f` — reduce `f` modulo `G` until no reducer applies.
* `sPolyPoly ord f g` — the S-polynomial of `f` and `g`.
* `allSpolyRemaindersZero ord G` — computable Boolean certificate that all
  pairwise S-polynomial remainders vanish.
* `buchberger ord gens` — compute a Gröbner basis (`partial def`; for `#eval` / `native_decide`).
* `buchbergerDef ord gens` — kernel-reducible variant using fuel bound (no `partial`; for proofs).
* `CGroebnerBasis` — a certified Gröbner basis.

## Usage pattern

```lean
-- 1. Compute
let G := buchberger CMonomialOrder.grlex [f₁, f₂, f₃]
-- 2. Certify (native_decide compiles and evaluates the checker natively)
have h : allSpolyRemaindersZero CMonomialOrder.grlex G = true := by native_decide
-- 3. Package
let gb := CGroebnerBasis.certify CMonomialOrder.grlex [f₁, f₂, f₃] G h
```
-/

namespace CBuchberger

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]
variable {R : Type*} [Field R] [DecidableEq R]

-- ============================================================
-- Single-step reduction
-- ============================================================

/-- Attempt one reduction step: if `lm(b) | lm(f)`, return
    `f - (lc(f) / lc(b)) * (lm(f) / lm(b)) * b`.
    Returns `none` if `b` does not reduce `f`. -/
def reduceStep (ord : CMonomialOrder σ)
    (b f : CMvPolynomial σ R) : Option (CMvPolynomial σ R) :=
  match f.leadMon ord, b.leadMon ord, f.leadCoeff ord, b.leadCoeff ord with
  | some mf, some mb, some cf, some cb =>
    if CMonomial.dvd mb mf then
      let shift := CMonomial.tdiv mf mb  -- mf / mb
      let quot  := cf / cb
      some (f - CMvPolynomial.smul quot (CMvPolynomial.monomialMul shift b))
    else none
  | _, _, _, _ => none

-- ============================================================
-- Full reduction (remainder)
-- ============================================================

/-- Fuel-bounded remainder computation.  Terminates by structural recursion on `fuel`.
    Returns `f` unchanged if fuel runs out (shouldn't happen with adequate fuel). -/
private def remainderPolyAux (fuel : ℕ) (ord : CMonomialOrder σ)
    (G : List (CMvPolynomial σ R)) (f : CMvPolynomial σ R) : CMvPolynomial σ R :=
  match fuel with
  | 0       => f
  | fuel + 1 =>
    if f == 0 then 0
    else
      match G.findSome? (fun b => reduceStep ord b f) with
      | some f' => remainderPolyAux fuel ord G f'
      | none    =>
        -- No reducer; move the leading term to the output and recurse on the tail.
        f.leadTerm ord + remainderPolyAux fuel ord G (f.tail ord)

/-- Reduce `f` modulo the list `G` until no element of `G` can reduce `f`.

    Uses a fuel bound proportional to the input size.  The actual number of reduction
    steps is always finite (the leading monomial strictly decreases at each step), so
    the fuel is never exhausted in practice.

    This replaces the earlier `partial def`; all sub-operations are now kernel-reducible,
    making `allSpolyRemaindersZero` checkable by `decide` for concrete inputs. -/
def remainderPoly (ord : CMonomialOrder σ)
    (G : List (CMvPolynomial σ R)) (f : CMvPolynomial σ R) : CMvPolynomial σ R :=
  remainderPolyAux (f.toTerms.length * (G.length + 1) * 1000) ord G f

-- ============================================================
-- S-polynomial
-- ============================================================

/-- The S-polynomial of `f` and `g`:
    `spoly(f, g) = lc(g) * (lcm / lm(f)) * f - lc(f) * (lcm / lm(g)) * g`
    where `lcm = lcm(lm(f), lm(g))`. -/
def sPolyPoly (ord : CMonomialOrder σ)
    (f g : CMvPolynomial σ R) : CMvPolynomial σ R :=
  match f.leadMon ord, g.leadMon ord, f.leadCoeff ord, g.leadCoeff ord with
  | some mf, some mg, some cf, some cg =>
    let lcm    := CMonomial.lcm mf mg
    let shiftF := CMonomial.tdiv lcm mf
    let shiftG := CMonomial.tdiv lcm mg
    CMvPolynomial.smul cg (CMvPolynomial.monomialMul shiftF f) -
    CMvPolynomial.smul cf (CMvPolynomial.monomialMul shiftG g)
  | _, _, _, _ => 0

-- ============================================================
-- Computable certificate checker
-- ============================================================

/-- Check that every pairwise S-polynomial remainder vanishes mod `G`.
    This is the key computable predicate: `allSpolyRemaindersZero ord G = true`
    implies (via the bridge theorem, once proved) that `G` is a Gröbner basis. -/
def allSpolyRemaindersZero (ord : CMonomialOrder σ)
    (G : List (CMvPolynomial σ R)) : Bool :=
  G.all fun p => G.all fun q =>
    remainderPoly ord G (sPolyPoly ord p q) == 0

-- ============================================================
-- Buchberger's algorithm
-- ============================================================

/-- Fuel-bounded Buchberger loop.  Terminates by structural recursion on `fuel`.
    Returns `G` unchanged if fuel runs out (doesn't happen with adequate fuel).

    This mirrors the design of `remainderPolyAux`: all sub-operations are proper `def`s,
    making the result kernel-reducible and suitable for `decide`/`native_decide` proofs.

    **Termination of the algorithm**: in the `r ≠ 0` branch the leading-monomial ideal
    of `G` strictly increases (by `Bridge.lmIdeal_strictMono`), and by the Hilbert basis
    theorem the ascending chain stabilizes.  The formal proof is in `Bridge.lean`. -/
private def buchbergerLoopAux
    (fuel : ℕ) (ord : CMonomialOrder σ)
    (G : List (CMvPolynomial σ R))
    (B : List (CMvPolynomial σ R × CMvPolynomial σ R)) :
    List (CMvPolynomial σ R) :=
  match fuel with
  | 0        => G    -- out of fuel; upper bound should always prevent this
  | fuel + 1 =>
    match B with
    | [] => G
    | (p, q) :: B' =>
      let r := remainderPoly ord G (sPolyPoly ord p q)
      if r == 0 then
        buchbergerLoopAux fuel ord G B'
      else
        let G' := G ++ [r]
        let newPairs := G.map fun g => (g, r)
        buchbergerLoopAux fuel ord G' (B' ++ newPairs)

/-- Inner loop for Buchberger's algorithm.  `partial def` for use with `#eval` and
    `native_decide`; see `buchbergerLoopAux` for the kernel-reducible fuel-bounded
    counterpart used in formal proofs. -/
private partial def buchbergerLoop (ord : CMonomialOrder σ)
    (G : List (CMvPolynomial σ R))
    (B : List (CMvPolynomial σ R × CMvPolynomial σ R)) :
    List (CMvPolynomial σ R) :=
  match B with
  | [] => G
  | (p, q) :: B' =>
    let r := remainderPoly ord G (sPolyPoly ord p q)
    if r == 0 then
      buchbergerLoop ord G B'
    else
      let G' := G ++ [r]
      let newPairs := G.map fun g => (g, r)
      buchbergerLoop ord G' (B' ++ newPairs)

/-- Given a list of generators, compute a Gröbner basis using Buchberger's algorithm.

    `partial def` for interactive use (`#eval`) and certification (`native_decide`).
    For kernel-reducible computation in formal proofs, see `buchbergerDef` which uses
    `buchbergerLoopAux` with an adequate fuel bound. -/
partial def buchberger (ord : CMonomialOrder σ)
    (gens : List (CMvPolynomial σ R)) : List (CMvPolynomial σ R) :=
  buchbergerLoop ord gens (gens.product gens)

/-- Kernel-reducible variant of `buchberger`.  Uses `buchbergerLoopAux` with a
    generous fuel bound instead of `partial def`.  Suitable for `decide`-based
    certification proofs.

    The fuel bound `n^2 * 1000` is a heuristic; Buchberger's algorithm terminates
    by the Hilbert basis theorem (see `Bridge.lmIdeal_strictMono`), so the fuel is
    never exhausted in practice.  If it ever were, the function would return the
    current (possibly incomplete) basis rather than a Gröbner basis. -/
def buchbergerDef (ord : CMonomialOrder σ)
    (gens : List (CMvPolynomial σ R)) : List (CMvPolynomial σ R) :=
  let pairs := gens.product gens
  let fuel  := (gens.length ^ 2 + pairs.length) * 1000
  buchbergerLoopAux fuel ord gens pairs

-- ============================================================
-- IsCGroebnerBasis
-- ============================================================

/-- `G` is a computable Gröbner basis iff all pairwise S-polynomial remainders vanish.

    Since `allSpolyRemaindersZero` is a `Bool`-valued computable function (all
    sub-operations are proper `def`s), this `Prop` is decidable.  For any concrete
    list `G`, the proof obligation `IsCGroebnerBasis ord G` can be discharged
    by `decide`. -/
def IsCGroebnerBasis (ord : CMonomialOrder σ)
    (G : List (CMvPolynomial σ R)) : Prop :=
  allSpolyRemaindersZero ord G = true

/-- `IsCGroebnerBasis` is decidable: it reduces to `Bool` equality. -/
instance (ord : CMonomialOrder σ) (G : List (CMvPolynomial σ R)) :
    Decidable (IsCGroebnerBasis ord G) :=
  inferInstanceAs (Decidable (allSpolyRemaindersZero ord G = true))

-- ============================================================
-- CGroebnerBasis
-- ============================================================

/-- A certified Gröbner basis for the ideal generated by `gens`.

    `gens` is a type-level parameter recording which ideal is being considered.
    `is_groebner` is a proof (dischargeable by `decide` for concrete inputs) that
    all S-polynomial remainders of `basis` vanish.  This is the computable analogue
    of `IsGroebnerBasis`; the formal bridge theorem (future work) will connect them. -/
structure CGroebnerBasis (σ R : Type*) [DecidableEq σ] [LinearOrder σ]
    [Field R] [DecidableEq R]
    (gens : List (CMvPolynomial σ R))
    (ord : CMonomialOrder σ) where
  /-- The computed Gröbner basis. -/
  basis : List (CMvPolynomial σ R)
  /-- Certificate that all pairwise S-polynomial remainders vanish. -/
  is_groebner : IsCGroebnerBasis ord basis

/-- Package a pre-computed basis with a certificate into a `CGroebnerBasis`.

    Typical usage:
    ```lean
    have h : IsCGroebnerBasis ord G := by decide
    exact CGroebnerBasis.certify ord G h
    ``` -/
def CGroebnerBasis.certify {σ R : Type*} [DecidableEq σ] [LinearOrder σ]
    [Field R] [DecidableEq R]
    {gens : List (CMvPolynomial σ R)}
    (ord : CMonomialOrder σ)
    (basis : List (CMvPolynomial σ R))
    (h : IsCGroebnerBasis ord basis) :
    CGroebnerBasis σ R gens ord :=
  ⟨basis, h⟩

end CBuchberger
