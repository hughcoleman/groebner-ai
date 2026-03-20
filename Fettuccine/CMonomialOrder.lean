import Fettuccine.CMvPolynomial
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Order.WellFounded

/-!
# Computable monomial orders

This file defines `CMonomialOrder`, a typeclass for monomial orders on
`CMonomial σ`, and provides the lexicographic order as the canonical instance.

## Definitions

* `CMonomialOrder σ` : a well-founded, translation-invariant total order on
  `CMonomial σ`.
* `CMonomialOrder.lex` : the lexicographic monomial order.

## Notation

* `m₁ ≺[ord] m₂` : strict inequality under the monomial order `ord`.
* `m₁ ≼[ord] m₂` : non-strict inequality under the monomial order `ord`.
-/

/-- A **monomial order** on `σ` is a well-founded, translation-invariant total
    order on `CMonomial σ`. -/
class CMonomialOrder (σ : Type*) [DecidableEq σ] extends LinearOrder (CMonomial σ) where
  /-- The order is well-founded. -/
  wf : WellFoundedRelation (CMonomial σ)
  /-- The order is translation-invariant on the right. -/
  mul_le_mul_right :
    ∀ m₁ m₂ m₃ : CMonomial σ, m₁ ≤ m₂ → m₁ * m₃ ≤ m₂ * m₃

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ]

section Notation

/-- The strict order relation for a given monomial order. -/
def moLt (ord : CMonomialOrder σ) (m₁ m₂ : CMonomial σ) : Prop :=
  ord.toLinearOrder.lt m₁ m₂

/-- The non-strict order relation for a given monomial order. -/
def moLe (ord : CMonomialOrder σ) (m₁ m₂ : CMonomial σ) : Prop :=
  ord.toLinearOrder.le m₁ m₂

/-- Notation for the strict order relation for monomial orders. -/
scoped notation:25 lhs " ≺[" ord "] " rhs => CMonomialOrder.moLt ord lhs rhs

/-- Notation for the non-strict order relation for monomial orders. -/
scoped notation:25 lhs " ≼[" ord "] " rhs => CMonomialOrder.moLe ord lhs rhs

end Notation

/-- By commutativity, monomial orders are left translation-invariant. -/
lemma mul_le_mul_left (ord : CMonomialOrder σ) (m₁ m₂ m₃ : CMonomial σ)
    (h : m₁ ≼[ord] m₂) : m₃ * m₁ ≼[ord] m₃ * m₂ := by
  rw [mul_comm m₃ m₁, mul_comm m₃ m₂]
  exact ord.mul_le_mul_right _ _ _ h

/-- If a product of monomials is equal to a product of upper bounds, then the
    factors attain the upper bound. -/
lemma eq_of_mul_eq_of_le (ord : CMonomialOrder σ) {m₁ m₂ m₁' m₂' : CMonomial σ}
    (h₁ : m₁' ≼[ord] m₁) (h₂ : m₂' ≼[ord] m₂) (h : m₁' * m₂' = m₁ * m₂) :
    m₁' = m₁ ∧ m₂' = m₂ := by
  have hle₁ : m₁' * m₂' ≼[ord] m₁ * m₂' := ord.mul_le_mul_right _ _ _ h₁
  have hle₂ : m₁  * m₂' ≼[ord] m₁ * m₂  := ord.mul_le_mul_left  _ _ _ h₂
  -- These inequalities are in fact equalities, by the assumed bounds on m₁'
  -- and m₂'. We can then cancel to get the desired result.
  have heq₁ : m₁' * m₂' = m₁ * m₂' := le_antisymm hle₁ (h ▸ hle₂)
  have heq₂ : m₁  * m₂' = m₁ * m₂  := le_antisymm hle₂ (h ▸ hle₁)
  exact ⟨mul_right_cancel heq₁, mul_left_cancel heq₂⟩

/-- The ordering is strictly monotone on the right. -/
lemma mul_lt_mul_right (ord : CMonomialOrder σ) (m₁ m₂ m₃ : CMonomial σ)
    (h : m₁ ≺[ord] m₂) : m₁ * m₃ ≺[ord] m₂ * m₃ := by
  sorry

/-- The ordering is strictly monotone on the left. -/
lemma mul_lt_mul_left (ord : CMonomialOrder σ) (m₁ m₂ m₃ : CMonomial σ)
    (h : m₁ ≺[ord] m₂) : m₃ * m₁ ≺[ord] m₃ * m₂ := by
  rw [mul_comm m₃ m₁, mul_comm m₃ m₂]
  exact mul_lt_mul_right ord _ _ _ h

/-- The constant monomial is minimal. -/
lemma one_le (ord : CMonomialOrder σ) (m : CMonomial σ) : 1 ≼[ord] m := by
  -- If 1 ≻ₒ m, then 1 ≻ₒ m ≻ₒ m^2 ≻ₒ m^3 ≻ₒ ... which contradicts the
  -- well-foundedness axiom.
  by_contra h
  simp only [CMonomialOrder.moLe, not_le] at h
  have hdesc : ∀ n : ℕ, m ^ (n + 1) ≺[ord] m ^ n := by
    intro n
    induction n with
    | zero      => simpa [CMonomialOrder.moLt]
    | succ n ih =>
        calc m ^ (n + 2) = m ^ (n + 1) * m := by rfl
          _ ≺[ord] m ^ n * m               := mul_lt_mul_right ord _ _ _ ih
          _ = m ^ (n + 1)                  := by rfl
  sorry

section LeadingMonomial

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [DecidableEq R] [CommSemiring R]

/-- The **leading monomial** of a polynomial `f` with respect to a monomial
    order `ord`. By convention, this is typically zero for the zero polynomial
    but we are good computer scientists so we will use an Optional type. -/
def CMvPolynomial.leadingMonomial (ord : CMonomialOrder σ) (f : CMvPolynomial σ R)
    : Option (CMonomial σ) :=
  let supp := f.support
  if h : supp.Nonempty then
    some (supp.max' h)
  else
    none

open CMvPolynomial

/-- The leading monomial of the zero polynomial is none. -/
lemma leadingMonomial_zero (ord : CMonomialOrder σ) :
    leadingMonomial ord (0 : CMvPolynomial σ R) = none := by
  simp [leadingMonomial]; rfl

/-- The leading monomial of a non-zero polynomial is an element of its support. -/
lemma leadingMonomial_eq_some_of_nonempty (ord : CMonomialOrder σ) (f : CMvPolynomial σ R)
    (h : f.support.Nonempty) : leadingMonomial ord f = some (f.support.max' h) := by
  simp [leadingMonomial, h]

/-- The leading monomial actually belongs to the support -/
lemma leadingMonomial_mem_support (ord : CMonomialOrder σ) (f : CMvPolynomial σ R)
    (h : f.support.Nonempty) : f.support.max' h ∈ f.support := by
  sorry

/- The leading monomial is none if and only if the polynomial is zero. -/
lemma leadingMonomial_eq_none_iff (ord : CMonomialOrder σ) (f : CMvPolynomial σ R) :
    leadingMonomial ord f = none ↔ f = 0 := by
  sorry

/-- The leading monomial is indeed an upper bound for the support. -/
lemma le_leadingMonomial (ord : CMonomialOrder σ) (f : CMvPolynomial σ R) {m : CMonomial σ}
    (hm : m ∈ f.support) : m ≤ f.support.max' ⟨m, hm⟩ := by
  exact Finset.le_max' _ _ hm

/-- The leading monomial of a single term c * m is just m (when c ≠ 0) -/
lemma leadingMonomial_monomial (ord : CMonomialOrder σ) (m : CMonomial σ) (c : R) (hc : c ≠ 0) :
    leadingMonomial ord (CMvPolynomial.ofMonomial c m) = some m := by
  sorry

/-- The leading monomial of a product is the product of leading monomials. -/
lemma leadingMonomial_mul (ord : CMonomialOrder σ) (f g : CMvPolynomial σ R)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    leadingMonomial ord (f * g) = (leadingMonomial ord f).map₂ (· * ·) (leadingMonomial ord g) :=
  sorry

/-- The leading monomial of a sum is bounded by the larger of the leading
    monomials of the summands. -/
lemma leadingMonomial_add_le (ord : CMonomialOrder σ) (f g : CMvPolynomial σ R)
    (hf : f.support.Nonempty) (hg : g.support.Nonempty) (h : (f + g).support.Nonempty) :
    (f + g).support.max' h ≤ max (f.support.max' hf) (g.support.max' hg) :=
  sorry

end LeadingMonomial

end CMonomialOrder

/-! ## Monomial Orders -/

/-! ### Lex -/

section Lex

/-- Lift the lexicographic order to a linear order on `CMonomial σ`. -/
instance CMonomial.instLexLinearOrder {σ : Type*} [DecidableEq σ] [LinearOrder σ] :
    LinearOrder (CMonomial σ) :=
  LinearOrder.lift' (fun m => toLex m.toFun)
    (fun m₁ m₂ h => by cases m₁; cases m₂; simp_all)

/-- Lift the well-foundedness of the lexicographic order. -/
instance CMonomial.instLexWellFoundedLT {σ : Type*} [DecidableEq σ] [LinearOrder σ]
    [WellFoundedGT σ] : WellFoundedLT (CMonomial σ) :=
  ⟨InvImage.wf (fun (m : CMonomial σ) => toLex m.toFun) DFinsupp.Lex.wellFoundedLT.wf⟩

/-- Proof that the lexicographic order is translation-invariant. -/
theorem CMonomial.lex_mul_le_mul_right {σ : Type*} [DecidableEq σ] [LinearOrder σ]
    (m₁ m₂ m₃ : CMonomial σ) (h : toLex m₁.toFun ≤ toLex m₂.toFun) :
    toLex (m₁ * m₃).toFun ≤ toLex (m₂ * m₃).toFun := by
  simp only [HMul.hMul, Mul.mul, toLex_add]
  exact add_le_add_left h _

/-- The lexicographic order on `CMonomial σ`. -/
instance CMonomialOrder.lex {σ : Type*} [DecidableEq σ] [LinearOrder σ]
    [WellFoundedGT σ] : CMonomialOrder σ where
  __ := CMonomial.instLexLinearOrder
  wf := inferInstanceAs (WellFoundedRelation (CMonomial σ))
  mul_le_mul_right := CMonomial.lex_mul_le_mul_right

end Lex

/-! ### Grlex -/

section Grlex

/-- The graded lexicographic order on `CMonomial σ`. -/
instance CMonomialOrder.grlex {σ : Type*} [DecidableEq σ] [LinearOrder σ]
    [WellFoundedGT σ] : CMonomialOrder σ :=
  sorry

end Grlex

/-! ### Grevlex -/

section Grevlex

/-- The graded reverse lexicographic order on `CMonomial σ`. -/
instance CMonomialOrder.grevlex {σ : Type*} [DecidableEq σ] [LinearOrder σ]
    [WellFoundedGT σ] : CMonomialOrder σ :=
  sorry

end Grevlex
