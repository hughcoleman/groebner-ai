import Fettuccine.CMvPolynomial
import Mathlib.Data.DFinsupp.WellFounded

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

set_option quotPrecheck false

/-- Notation for the strict order relation for monomial orders. -/
scoped notation:25 lhs " ≺[" m:25 "] " rhs:25 =>
  @LT.lt _ (CMonomialOrder.toLinearOrder (self := m)).toLT lhs rhs

-- /-- Notation for the non-strict order relation for monomial orders. -/
scoped notation:25 lhs " ≼[" m:25 "] " rhs:25 =>
  @LE.le _ (CMonomialOrder.toLinearOrder (self := m)).toLE lhs rhs

end Notation

/-- The ordering is translation-invariant on the left. -/
lemma mul_le_mul_left (ord : CMonomialOrder σ) (m₁ m₂ m₃ : CMonomial σ)
    (h : m₁ ≼[ord] m₂) : m₃ * m₁ ≼[ord] m₃ * m₂ := by
  rw [mul_comm m₃ m₁, mul_comm m₃ m₂]
  exact ord.mul_le_mul_right _ _ _ h

/-- If a product of monomials is equal over ordered factors, then the factors
    are equal. -/
lemma eq_of_mul_eq_of_le (ord : CMonomialOrder σ) {m₁ m₂ m₁' m₂' : CMonomial σ}
    (h₁ : m₁' ≼[ord] m₁) (h₂ : m₂' ≼[ord] m₂) (h : m₁' * m₂' = m₁ * m₂) :
    m₁' = m₁ ∧ m₂' = m₂ := by
  have h_left  : m₁' * m₂' ≼[ord] m₁ * m₂' := ord.mul_le_mul_right _ _ _ h₁
  have h_right : m₁  * m₂' ≼[ord] m₁ * m₂  := mul_le_mul_left ord _ _ _ h₂
  have heq₁ : m₁' * m₂' = m₁ * m₂' :=
    ord.toLinearOrder.le_antisymm _ _ h_left (h ▸ h_right)
  have heq₂ : m₁  * m₂' = m₁ * m₂  :=
    ord.toLinearOrder.le_antisymm _ _ h_right (h ▸ h_left)
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

section LeadingMonomial

open CMvPolynomial

variable {σ : Type*} [DecidableEq σ] [CMonomialOrder σ]
variable {R : Type*} [DecidableEq R] [CommSemiring R]

/-- The **leading monomial** of a polynomial `f` with respect to a monomial
    order `ord`. By convention, this is typically zero for the zero polynomial
    but we are good computer scientists so we will use an Optional type. -/
def CMvPolynomial.leadingMonomial (f : CMvPolynomial σ R) : Option (CMonomial σ) :=
  let supp := f.support
  if h : supp.Nonempty then
    some (supp.max' h)
  else
    none

/-- The leading monomial of the zero polynomial is none. -/
lemma leadingMonomial_zero : CMvPolynomial.leadingMonomial (0 : CMvPolynomial σ R) = none := by
  simp [CMvPolynomial.leadingMonomial]; rfl

/-- The leading monomial of a non-zero polynomial is an element of its support. -/
lemma leadingMonomial_eq_some_of_nonempty (f : CMvPolynomial σ R) (h : f.support.Nonempty) :
    CMvPolynomial.leadingMonomial f = some (f.support.max' h) := by
  simp [CMvPolynomial.leadingMonomial, h]

/-- The leading monomial is indeed an upper bound for the support. -/
lemma le_leadingMonomial (f : CMvPolynomial σ R) {m : CMonomial σ} (hm : m ∈ f.support) :
    m ≤ f.support.max' ⟨m, hm⟩ := by
  exact Finset.le_max' _ _ hm

end LeadingMonomial

end CMonomialOrder

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
