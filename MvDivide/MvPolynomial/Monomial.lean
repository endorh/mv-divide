import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Zip
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

import Mathlib.Order.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Finsupp.WellFounded

import MvDivide.Vector.Dot

noncomputable section

namespace MvPolynomial

open Classical

variable {σ : Type _} {R : Type _} [CommRing R] (p q : MvPolynomial σ R)

section AuxiliaryLemmas

-- Añadido en Mathlib v4.0.0
-- @[simp]
-- lemma coeff_neg : (-p).coeff m = -p.coeff m := by
--   simp only [coeff, Neg.neg, Finsupp.mapRange_apply]

lemma one_eq_monomial_zero_one : (1 : MvPolynomial σ R) = monomial 0 1 := rfl

end AuxiliaryLemmas

section Monomial

variable (σ R)

def Monomial := (σ →₀ ℕ)
@[ext]
structure Term where
  coeff : R
  monomial : Monomial σ

-- Explicit coercions
variable {σ R}
def Monomial.toFinsupp (m : Monomial σ) : σ →₀ ℕ := m
def Monomial.ofFinsupp (m : σ →₀ ℕ) : Monomial σ := m

-- Simp lemmas for coercions
@[simp]
lemma Monomial.toFinsupp_def (m : Monomial σ) : m.toFinsupp = ↑m := rfl
@[simp]
lemma Monomial.ofFinsupp_def (m : σ →₀ ℕ) : Monomial.ofFinsupp m = ↑m := rfl

variable (σ R)
instance monomialCommMonoid : CommMonoid (Monomial σ) :=
  @Multiplicative.commMonoid (Monomial σ) (@Finsupp.addCommMonoid σ ℕ _)

-- Coercions to polynomial and function type
@[default_instance]
instance monomial_coe : Coe (Monomial σ) (MvPolynomial σ R) where
  coe m := monomial m 1
instance monomial_coe_fun : CoeFun (Monomial σ) (λ_ ↦ σ → ℕ) :=
  ⟨Finsupp.toFun⟩

instance monomial_hmul : HMul (Monomial σ) (MvPolynomial σ R) (MvPolynomial σ R) where
  hMul m p := ↑m * p
instance monomial_hmulr : HMul (MvPolynomial σ R) (Monomial σ) (MvPolynomial σ R) where
  hMul p m := p * ↑m
instance monomial_hadd : HAdd (Monomial σ) (MvPolynomial σ R) (MvPolynomial σ R) where
  hAdd m p := ↑m + p
instance monomial_haddr : HAdd (MvPolynomial σ R) (Monomial σ) (MvPolynomial σ R) where
  hAdd p m := p + ↑m

/-- The monomial product is compatible with the polynomial product -/
@[norm_cast]
lemma monomial_mul_coe (m n : Monomial σ) : (↑m : MvPolynomial σ R) * ↑n = ↑(m * n) := by
  conv_rhs =>
    simp [HMul.hMul, Mul.mul, HAdd.hAdd, Add.add]
    rw [Multiplicative.toAdd, Multiplicative.ofAdd]
    simp
  simp [monomial_mul]
  conv in (m + n) =>
    unfold HAdd.hAdd instHAdd Add.add Finsupp.add
    simp

instance monomialDvd : Dvd (Monomial σ) where
  dvd m n := ∀i, m i ≤ n i

/-- Required to use tsub_add_cancel_* -/
instance monomial_ordered_sub : OrderedSub (σ →₀ ℕ) where
  tsub_le_iff_right a b c := by
    constructor <;>
    . intro h
      unfold LE.le Finsupp.instLEFinsupp at *
      simp at *
      assumption

instance monomial_exists_add_of_le : ExistsAddOfLE (σ →₀ ℕ) where
  exists_add_of_le {a b} := by
    intro h
    use b.zipWith (λ b₁ a₁ => b₁ - a₁) (by simp) a
    ext x
    have h_x : a x ≤ b x := by
      unfold LE.le Finsupp.instLEFinsupp at h
      simp at h
      exact h x
    simp [Finsupp.zipWith_apply, h_x]

@[default_instance]
instance term_coe : Coe (Term σ R) (MvPolynomial σ R) where
  coe t := monomial t.monomial t.coeff

variable {σ R}

variable (s : Monomial σ) (c : R)

def monomials (p : MvPolynomial σ R) : Finset (Monomial σ) :=
  p.support

@[simp]
lemma monomials_of_monomial : (monomial s c).monomials = if c = 0 then ∅ else {s} := by
  simp [monomials, support, monomial]
  exact support_monomial

/-- Same simp normal form as `x ∈ f.support` -/
@[simp]
lemma mem_monomials_iff : x ∈ p.monomials ↔ coeff x p ≠ 0 := by
  simp [monomials, support, coeff]

def terms (p : MvPolynomial σ R) : Finset (Term σ R) :=
  p.support.image fun m => ⟨p.coeff m, m⟩

def coeffs (p : MvPolynomial σ R) : Finset R :=
  p.support.image fun m => p.coeff m

section Order

section Prec
class PrecEq (α : Type _) where
  precEq : α → α → Prop
class Prec (α : Type _) where
  prec : α → α → Prop

infix:25 " ≼ " => PrecEq.precEq
infix:25 " ≺ " => Prec.prec

end Prec

variable (σ R)
-- class MonomialOrder extends LinearOrder (Monomial σ) where
--   le_mul : ∀ (a b c : Monomial σ), a ≤ b → a*c ≤ b*c
--   well_founded : WellFoundedLT (Monomial σ)
class MonomialOrder where
  linear_order : LinearOrder (σ →₀ ℕ)
  le_add : ∀ {a b c : σ →₀ ℕ}, linear_order.le a b → linear_order.le (a + c) (b + c)
  well_founded_lt : IsWellFounded (σ →₀ ℕ) linear_order.lt


variable {σ R}
def MonomialOrder.le {o : MonomialOrder σ} := o.linear_order.le
def MonomialOrder.lt {o : MonomialOrder σ} := o.linear_order.lt

-- Monomial order notation
variable (σ R)
instance monomialOrderPrecEq [o : MonomialOrder σ] : PrecEq (Monomial σ) where
  precEq a b := o.le a.toFinsupp b.toFinsupp
instance monomialOrderPrec [o : MonomialOrder σ] : Prec (Monomial σ) where
  prec a b := o.lt a.toFinsupp b.toFinsupp
instance monomialOrderWithBotPrecEq [MonomialOrder σ] : PrecEq (WithBot (Monomial σ)) where
  precEq a b := WithBot.le.le (a.map Monomial.toFinsupp) (b.map Monomial.toFinsupp)
instance monomialOrderWithBotPrec [MonomialOrder σ] : Prec (WithBot (Monomial σ)) where
  prec a b := WithBot.lt.lt (a.map Monomial.toFinsupp) (b.map Monomial.toFinsupp)


-- Class inference shortcuts for the linear order induced by a monomial order
@[default_instance 100]
instance monomialOrderFinsuppLinearOrder [o : MonomialOrder σ] : LinearOrder (σ →₀ ℕ) :=
  o.linear_order
@[default_instance 100]
instance monomialOrderFinsuppPartialOrder [o : MonomialOrder σ] : PartialOrder (σ →₀ ℕ) :=
  o.linear_order.toPartialOrder
@[default_instance 100]
instance monomialOrderFinsuppPreorder [o : MonomialOrder σ] : Preorder (σ →₀ ℕ) :=
  o.linear_order.toPreorder
@[default_instance 100]
instance monomialOrderFinsuppLE [o : MonomialOrder σ] : LE (σ →₀ ℕ) :=
  o.linear_order.toLE
@[default_instance 100]
instance monomialOrderFinsuppLT [o : MonomialOrder σ] : LT (σ →₀ ℕ) :=
  o.linear_order.toLT

@[default_instance 100]
instance monomialOrderLinealOrder [o : MonomialOrder σ] : LinearOrder (Monomial σ) :=
  o.linear_order

-- Strict inequality of the monomial order property
theorem MonomialOrder.lt_add {o : MonomialOrder σ} : ∀ {a b c : σ →₀ ℕ},
    linear_order.lt a b → linear_order.lt (a + c) (b + c) := by
  intro a b c h_lt
  have h_le := le_of_lt h_lt
  have h_add_le := o.le_add (c := c) h_le
  have h_not_eq : a + c ≠ b + c := by
    intro h
    simp_arith at h
    have h_c := ne_of_lt h_lt
    contradiction
  apply lt_of_le_of_ne <;> assumption

-- Definitional lemma for the monomial product
lemma monomial_mul_def (a b : Monomial σ) : a * b = a.toFinsupp + b.toFinsupp := rfl

-- Monomial order property induced over the `Monomial` type
theorem MonomialOrder.le_mul {o : MonomialOrder σ} {a b c : Monomial σ} : a ≼ b → a * c ≼ b * c := by
  simp [PrecEq.precEq, monomial_mul_def]
  exact o.le_add
theorem MonomialOrder.lt_mul {o : MonomialOrder σ} {a b c : Monomial σ} : a ≺ b → a * c ≺ b * c := by
  simp [Prec.prec, monomial_mul_def]
  exact o.lt_add


-- Definitional lemmas for the monomial order notation
lemma monomial_prec_eq_def [MonomialOrder σ] (a b : Monomial σ) :
    (a ≼ b) = (a.toFinsupp ≤ b.toFinsupp) := rfl
lemma monomial_prec_def [MonomialOrder σ] (a b : Monomial σ) :
    (a ≺ b) = (a.toFinsupp < b.toFinsupp) := rfl


-- The lexicographic order induces a monomial order (if σ is finite)
instance lex_monomial_order [LinearOrder σ] [Finite σ] : MonomialOrder σ where
  linear_order := Finsupp.Lex.linearOrder
  le_add {a b c} h := by
    simp [LE.le, LT.lt] at h ⊢
    cases h
    case inl h' => left; rw [h']
    case inr h' =>
      right
      simp [Pi.Lex] at h' ⊢
      let ⟨i, h₁, h₂⟩ := h'
      use i
      constructor
      . intro j h_j
        have h₁' := h₁ j h_j
        simp [ofLex] at h₁' ⊢
        simp [Add.add, h₁']
      . simp [ofLex] at h₂ ⊢
        simp [Add.add, h₂]
  well_founded_lt := Finsupp.Lex.wellFoundedLT_of_finite

end Order

section Lead

section AuxiliaryLemmas

-- These technical lemmas could be provided by `WithBot`

@[simp]
lemma WithBot.unbot_some : WithBot.unbot (some a) h = a := rfl
lemma WithBot.some_of_unbot : WithBot.unbot (a) h = b → a = some b := by
  intro h'
  match a with
  | none   => contradiction
  | some x => simp [WithBot.unbot_some] at h'; rw [h']

end AuxiliaryLemmas


-- Monomial properties

variable [Finite σ] [MonomialOrder σ]

/-- The leading monomial of a multivariate polynomial, according to a given
(or inferred) order.

Since `0` is not a `Monomial σ`, the result has the type `WithBot (Monomial σ)`.
The variant `lead_monomial''` maps the leading monomial of the zero polynomial to 0 -/
def lead_monomial : WithBot (Monomial σ) :=
  p.monomials.max

-- Simp lemmas
@[simp]
lemma lead_monomial_zero : lead_monomial (0 : MvPolynomial σ R) = ⊥ := rfl
lemma lead_monomial_ne_zero (h : p ≠ 0) : lead_monomial p ≠ ⊥ := by
  simpa [lead_monomial, monomials, support, Finset.max_eq_bot]
@[simp]
lemma lead_monomial_monomial (s : Monomial σ) (c : R) (hc : c ≠ 0) :
    (monomial s c).lead_monomial = some s := by
  simp [lead_monomial, hc, WithBot.some]

@[simp]
lemma monomials_empty_iff : Finset.Nonempty (p.monomials) ↔ p ≠ 0 := by
  apply Iff.intro
  . intro h h_abs
    rw [monomials, h_abs, Finset.Nonempty, support, Finsupp.support_zero] at h
    choose x h using h
    contradiction
  . intro h
    rw [Finset.Nonempty]
    have h := exists_coeff_ne_zero h
    choose d h using h
    use d
    simp [h, mem_monomials_iff]

/-- The leading monomial of a multivariate polynomial, according to a given
(or inferred) order, given the proof that the polynomial is not zero. -/
def lead_monomial' (h₀ : p ≠ 0) : Monomial σ :=
  p.monomials.max' (monomials_empty_iff p |>.mpr h₀)

lemma lead_monomial'_def (h : p ≠ 0) : p.lead_monomial = ↑(p.lead_monomial' h) := by
  unfold lead_monomial lead_monomial' Finset.max Finset.max' Finset.sup'
  simp

@[simp]
lemma lead_monomial'_monomial (s : Monomial σ) (c : R) (hr : monomial s c ≠ 0) (hc : c ≠ 0) :
    (monomial s c).lead_monomial' hr = s := by
  simp [lead_monomial', hc]

/-- The leading monomial of a multivariate polynomial, according to a given
(or inferred) order.

Unlike `lead_monomial`, the leading coefficient of the zero polynomial is
defined as 0. -/
def lead_coeff : R :=
  match p.lead_monomial with
  | some m => p.coeff m
  | none   => 0

-- Simp lemmas
@[simp]
lemma lead_coeff_zero : lead_coeff (0 : MvPolynomial σ R) = 0 := rfl
@[simp]
lemma lead_coeff_ne_zero (h₀ : p ≠ 0) : p.lead_coeff ≠ 0 := by
  intro h
  rw [lead_coeff] at h
  have h' := lead_monomial_ne_zero p h₀
  match h_h : lead_monomial p with
  | none   => contradiction
  | some b =>
    simp [h_h] at h
    rw [lead_monomial] at h_h
    have h_mx := Finset.mem_of_max h_h
    rw [coeff] at h
    rw [monomials, support] at h_mx
    have h_c := (p.mem_support_toFun b).mp h_mx
    contradiction

@[simp]
lemma lead_coeff_def (h₀ : p ≠ 0) : p.coeff (p.lead_monomial' h₀) = p.lead_coeff := by
  rw [lead_coeff, lead_monomial'_def]

@[simp]
lemma lead_coeff_monomial (s : Monomial σ) (c : R) (hc : c ≠ 0) :
    (monomial s c).lead_coeff = c := by
  simp [lead_coeff, lead_monomial, hc]

/-- The leading term of a multivariate polynomial, according to a given
(or inferred) order.

The leading term of the zero polynomial is defined as the zero term, having
monomial `1` and coefficient `0`.
-/
def lead_term : WithBot (Term σ R) :=
  p.lead_monomial.map λ m => ⟨p.coeff m, m⟩

-- Simp lemmas
@[simp]
def lead_term_zero : lead_term (0 : MvPolynomial σ R) = ⊥ := rfl
def lead_term_ne_zero (h : p ≠ 0) : lead_term p ≠ ⊥ := by
  have h' : lead_monomial p ≠ ⊥  := lead_monomial_ne_zero p h
  simp [lead_term]
  match h'' : lead_monomial p with
  | some m => simp [h', WithBot.map, Option.map_some']
  | none   => contradiction

def lead_term' (h : p ≠ 0) : Term σ R :=
  p.lead_term.unbot (by
    simp [lead_term, WithBot.map]
    have h' : lead_monomial p ≠ ⊥ := lead_monomial_ne_zero p h
    match h'' : lead_monomial p with
    | some m => simp [h'', h']
    | none   => contradiction)

lemma lead_term_def (h : p ≠ 0) : p.lead_term = some (p.lead_term' h) := by
  match h' : p.lead_term with
  | none =>
    have h'' := lead_term_ne_zero p h
    contradiction
  | some m =>
    rw [lead_term']
    congr
    -- Without `conv`, rewrite fails as the motive is not type correct
    conv_rhs => arg 1; rw [h']


@[simp]
lemma lead_term'_def (h : p ≠ 0) : p.lead_term' h = ⟨p.lead_coeff, p.lead_monomial' h⟩ := by
  match h' : lead_monomial p with
  | none   => haveI := lead_monomial_ne_zero p h; contradiction
  | some m =>
    simp [lead_term', lead_term]
    conv in (lead_monomial p) => rw [h']
    -- Match uses `Option.some`, instead of `WithBot.some`,
    -- so we need to rewrite that to apply `WithBot.map_coe`
    have h'' : some m = WithBot.some m := rfl
    conv in (some m) => rw [h'']
    simp [WithBot.map_coe]
    simp [lead_coeff, h']
    apply WithBot.coe_injective
    have h''' : (fun (a : Monomial σ) => WithBot.some a) = some := rfl
    rw [h''', ←h']
    apply lead_monomial'_def

@[simp]
lemma lead_term'_coeff_def (h : p ≠ 0) : (p.lead_term' h).coeff = p.lead_coeff := by
  rw [lead_term'_def]

@[simp]
lemma lead_term'_monomial_def (h : p ≠ 0) : (p.lead_term' h).monomial = p.lead_monomial' h := by
  rw [lead_term'_def]

@[simp]
lemma lead_term_monomial (s : Monomial σ) (c : R) (hc : c ≠ 0) :
    (monomial s c).lead_term = some ⟨c, s⟩ := by
  have h_m := lead_monomial_monomial s c hc
  have h_c := lead_coeff_monomial s c hc
  have h₀ : monomial s c ≠ 0 := by simp [hc]
  have h_m' : (monomial s c).lead_monomial' h₀ = s := by
    simp [lead_monomial', h_m, hc]
  have h_t' : (monomial s c).lead_term' h₀ = ⟨c, s⟩ := by
    conv_rhs =>
      congr
      . rw [←h_c]
      . rw [←h_m']
    apply lead_term'_def
  rw [lead_term'] at h_t'
  exact WithBot.some_of_unbot h_t'

/-- The multi-degree of a polynomial, according to a given (or inferred) order.
The multi-degree of the zero polynomial is ⊥. -/
def multi_deg : WithBot (σ →₀ ℕ) :=
  p.lead_monomial


-- Simp lemmas
@[simp]
lemma multi_deg_bot : multi_deg (0 : MvPolynomial σ R) = ⊥ := by
  simp [multi_deg, lead_monomial_zero]

@[simp]
lemma multi_deg_ne_bot (h : p ≠ 0) : multi_deg p ≠ ⊥ := by
  rw [multi_deg]
  apply lead_monomial_ne_zero p h

-- Properties of the set of `monomials`

-- `Finsupp.support_add` requires [DecidableEq σ] as a parameter
lemma monomials_add [DecidableEq (σ →₀ ℕ)] (p q : MvPolynomial σ R) :
    (p + q).monomials ⊆ p.monomials ∪ q.monomials := by
  rw [monomials, support]
  apply Finsupp.support_add

lemma monomials_mul [i : DecidableEq σ] (p q : MvPolynomial σ R) :
    monomials (p * q) ⊆ Finset.biUnion (monomials p) fun a => Finset.biUnion (monomials q)
    fun b => {a * b} := by
  conv in {_ * _} => rw [monomial_mul_def]
  unfold monomials Monomial Monomial.toFinsupp
  -- The `convert` tactic seems able to solve class instance
  -- definitional equality issues that `apply` can't
  convert support_mul p q

@[simp]
lemma monomials_neg : (-p).monomials = p.monomials := by
  rw [monomials, support, Neg.neg]
  exact Finsupp.support_mapRange_of_injective (ι := (σ →₀ ℕ)) (M := R) (N := R)
    (e := Neg.neg) (by simp_arith) (p : (σ →₀ ℕ) →₀ R) (by
      intro a b h
      rw [←neg_neg a, ←neg_neg b, h])

-- `lead_monomial` properties

@[simp]
lemma lead_monomial_neg : (-p).lead_monomial = p.lead_monomial := by
  simp [lead_monomial, monomials_neg]

@[simp]
lemma coeff_gt_lead_monomial_eq_zero (h₀ : p ≠ 0) (h : p.lead_monomial' h₀ < m) :
    p.coeff m = 0 := by
  have h_max : Finset.max p.monomials = ↑(p.lead_monomial' h₀) :=
    lead_monomial'_def p h₀
  have h' := Finset.not_mem_of_max_lt h h_max
  rw [monomials] at h'
  simp only [coeff, FunLike.coe, Finsupp.funLike]
  -- We need to specify the correct instance to `@Finsupp.mem_support_toFun`
  rename_i instCommRing _ _
  exact not_ne_iff.mp <| (@Finsupp.mem_support_toFun _ _ (instCommRing.toZero) p m).not.mp h'

lemma coeff_ne_zero_le_lead_monomial (h₀ : p ≠ 0) (h : p.coeff m ≠ 0) : m ≤ p.lead_monomial' h₀ := by
  apply le_of_not_lt
  intro h_absurd
  have h_contr := coeff_gt_lead_monomial_eq_zero p h₀ h_absurd
  contradiction


-- We need this class to apply `add_lt_add_of_le_of_lt` later in the
-- proof of `coeff_lead_monomial_mul`
instance monomialCovariantMulOrder [o : MonomialOrder σ] : CovariantClass (σ →₀ ℕ) (σ →₀ ℕ) (· + ·) (· ≤ ·) where
  elim x₁ x₂ n₂ h := by
    rw [add_comm]
    conv_rhs => rw [add_comm]
    apply o.le_add h

-- We don't need this one, but we prove it anyways
instance monomialContravariantMulOrder [o : MonomialOrder σ] : ContravariantClass (σ →₀ ℕ) (σ →₀ ℕ) (· + ·) (· ≤ ·) where
  elim x₁ x₂ n₂ h_add_le := by
    by_cases h_le : x₂ ≤ n₂
    . assumption
    . have h_lt := lt_of_not_le h_le
      have h_add_lt := o.lt_add (c := x₁) h_lt
      have h_not_add_le := not_le_of_lt h_add_lt
      rw [add_comm] at h_add_le
      conv_rhs at h_add_le => rw [add_comm]
      contradiction


-- Auxiliary `Finsupp` lemma
@[simp]
lemma Finsupp.add_sub_cancel_nat (a b : α →₀ ℕ) : a + b - b = a := by
  ext x
  simp

-- Weak version of `lead_coeff_mul` we use to prove `lead_monomial_mul`
lemma coeff_lead_monomial_mul {σ : Type _} {R : Type _} [CommRing R] [o : MonomialOrder σ]
    {p q : MvPolynomial σ R} (h₀p : p ≠ 0) (h₀q : q ≠ 0) :
    (p * q).coeff (p.lead_monomial' h₀p * q.lead_monomial' h₀q) =
    p.lead_coeff * q.lead_coeff := by
  -- Aliases
  let mp := (lead_monomial' p h₀p).toFinsupp
  let mq := (lead_monomial' q h₀q).toFinsupp
  let m := mp + mq
  
  -- It's convenient to work with `Finsupp`
  unfold Monomial at *

  -- Expand the convolution product
  rw [coeff_mul, monomial_mul_def]
  have h : ∀ x, x ∈ Finsupp.antidiagonal m → x.fst + x.snd = m :=
    λ_ => Finsupp.mem_antidiagonal.mp
  rw [←Finset.sum_subtype_of_mem _ h]

  -- Rewrite inside the sum to show that each term is either `0`
  -- or the term associated to the product of both lead monomials.
  conv_lhs =>
    arg 2
    intro x
    tactic =>
      -- If the coefficients are not the ones associated to the lead monomials,
      -- one of them is `0`, so the product is only potentially non-zero at our pair
      have h_i : p.coeff x.val.fst * q.coeff x.val.snd = if x = ⟨(mp, mq), rfl⟩ then p.coeff mp * q.coeff mq else 0 := by
        -- If the first multidegree is that of `p`, the other is that of `q`
        have eq_first : x.val.fst = mp ↔ x = ⟨(mp, mq), rfl⟩ := by
          apply Iff.intro
          . intro h_fst
            have h_snd : x.val.snd = mq := by
              have h_x := x.property
              rw [←add_right_inj x.val.fst]
              conv_rhs => rw [h_fst]
              simpa using h_x
            apply Subtype.ext
            apply Prod.ext <;> assumption
          . intro h; simp [h]
        -- If the first multidegree is less than that of `p` we are in the `0` case
        by_cases h_mp : x.val.fst < mp
        . have h_ne := eq_first.not.mp (ne_of_lt h_mp)
          simp only [Monomial.toFinsupp_def] at h_ne
          simp only [Monomial.toFinsupp_def, ne_eq, h_ne, lead_coeff_def, ite_false]
          -- The second is greater thhan that of `q`, so its coefficient is `0`
          have h_mq : mq < x.val.snd := by
            apply lt_of_not_le
            intro h_mq
            have h_lt : x.val.fst + x.val.snd < mp + mq :=
              add_comm x.val.fst x.val.snd ▸ add_comm mp mq ▸
              add_lt_add_of_le_of_lt h_mq h_mp
            have h_c := ne_of_lt h_lt
            have h_eq := x.property
            contradiction
          have h_nc :=
            coeff_gt_lead_monomial_eq_zero q h₀q h_mq
          simp [h_nc]
        -- If the first multidegree is greater than that of `p` we are also in the `0` case
        . by_cases h_mp' : mp < x.val.fst
          . have h_ne := eq_first.not.mp (ne_of_lt h_mp').symm
            simp only [Monomial.toFinsupp_def] at h_ne
            simp only [Monomial.toFinsupp_def, ne_eq, h_ne, lead_coeff_def, ite_false]
            have h_nc :=
              coeff_gt_lead_monomial_eq_zero p h₀p h_mp'
            simp [h_nc]
          -- Otherwise, both are equal and we use `eq_first`
          . have h_eq := eq_first.mp (eq_of_le_of_not_lt (le_of_not_lt h_mp') h_mp)
            simp only [Monomial.toFinsupp_def] at h_eq
            simp [h_eq]
      rw [h_i]
  
  -- Split the sum in two, now that it contains an `if ... then ... else`
  classical
    rw [Finset.sum_apply_ite (f := λ_ => coeff mp p * coeff mq q) (g := λ_ => 0) (h := λx => x)]
  -- Remove the sum of `0`s
  rw [Finset.sum_const_zero, add_zero]
  -- Extract the single term from the sum
  rw [Finset.filter_eq' (Finset.subtype (fun x => x.fst + x.snd = m) (Finsupp.antidiagonal m))]
  have h_ex : ⟨(mp, mq), rfl⟩ ∈ (Finset.subtype (fun x => x.fst + x.snd = m) (Finsupp.antidiagonal m)) := by
    simp [Finset.subtype]
  
  -- Close the proof
  simp only [Monomial.toFinsupp_def] at h_ex
  simp [h_ex]

lemma ne_zero_of_mul_ne_zero {σ : Type _} {R : Type _} [CommRing R] [IsDomain R] [o : MonomialOrder σ]
    {p q : MvPolynomial σ R} (h₀p : p ≠ 0) (h₀q : q ≠ 0) : p * q ≠ 0 := by
  intro h
  have h_c₀ : (p * q).coeff (p.lead_monomial' h₀p * q.lead_monomial' h₀q) ≠ 0 := by
    rw [coeff_lead_monomial_mul h₀p h₀q]
    simp [h₀p, h₀q] -- lead_coeff_ne_zero is applied by `simp`
  have h_c₀' : (p * q).coeff (p.lead_monomial' h₀p * q.lead_monomial' h₀q) = 0 := by
    simp [h]
  contradiction

lemma monomial_mul_mono (m x y : Monomial σ) : m * (x ⊔ y) = (m * x) ⊔ (m * y) := by
  by_cases h : x ≺ y
  . rw [sup_eq_max, sup_eq_max]
    simp [Prec.prec, monomialOrderPrec] at h
    have h' := MonomialOrder.lt_add (a := x) (b := y) (c := m) h
    -- If we specify even one parameter for `add_comm`, the type class inference
    -- messes up, and the rewrite fails, because its `HAdd.hAdd` instance doesn't
    -- match `Finsupp.add`, so we use `conv` instead
    rw [add_comm] at h'; conv_rhs at h' => rw [add_comm]
    rw [monomial_mul_def, monomial_mul_def, monomial_mul_def]
    simp only [Monomial.toFinsupp]
    rw [max_eq_right_of_lt h', max_eq_right_of_lt h]
  . rw [sup_eq_max, sup_eq_max]
    simp [Prec.prec, monomialOrderPrec] at h
    have h' := le_of_not_lt h
    have h'' := MonomialOrder.le_add (a := y) (b := x) (c := m) h'
    rw [add_comm] at h''; conv_rhs at h'' => rw [add_comm]
    rw [monomial_mul_def, monomial_mul_def, monomial_mul_def]; simp
    rw [max_eq_left h', max_eq_left h'']

/-- In an integrity domain, the lead monomial of a product is the product of lead monomials -/
@[simp]
lemma lead_monomial_mul {σ : Type _} {R : Type _} [CommRing R] [IsDomain R] [o : MonomialOrder σ]
    {p q : MvPolynomial σ R} (h₀p : p ≠ 0) (h₀q : q ≠ 0) (h₀pq : p * q ≠ 0) :
    (p * q).lead_monomial' h₀pq = p.lead_monomial' h₀p * q.lead_monomial' h₀q := by
  unfold lead_monomial'
  have h_sub := monomials_mul p q
  have h_pq_nemp := monomials_empty_iff (p * q) |>.mpr h₀pq
  have h_p_nemp := monomials_empty_iff p |>.mpr h₀p
  have h_q_nemp := monomials_empty_iff q |>.mpr h₀q

  -- The lead monomial is at most the product of the lead monomials
  have h_le := Finset.max'_subset h_pq_nemp h_sub
  
  -- Unfold the convolution product definition
  unfold Finset.max' at h_le
  rw [Finset.sup'_biUnion (s := p.monomials) (f := id) (t := λa => Finset.biUnion q.monomials λb => {a * b})
    (Hs := h_p_nemp) (Ht := λa => Finset.biUnion_nonempty (s := q.monomials) (t := λb => {a * b}).mpr (by
      use q.lead_monomial' h₀q
      simp [lead_coeff_ne_zero q h₀q]
    ))] at h_le
  
  -- The supreme of the biUnion is just the supreme with a different criteria
  conv_rhs at h_le =>
    arg 3
    intro b
    rw [Finset.sup'_biUnion (s := q.monomials) (f := id) (t := λb₁ => {b * b₁})
        (Hs := h_q_nemp) (Ht := λa => by simp)]
    arg 3
    intro b_1
    rw [Finset.sup'_singleton]
    unfold id
  
  -- The supreme of the supremes of the products between `p` and `q` is
  -- the supreme of the products of `p` with the supreme of `q`
  conv_rhs at h_le =>
    arg 3
    intro b
    tactic =>
      let g := (b * ·)
      let f := λb₁ : Monomial σ => b₁
      have h_gf : g ∘ f = λb₁ => b * b₁ := rfl
      rw [←h_gf, ←Finset.comp_sup'_eq_sup'_comp h_q_nemp (f := f) (g := g) (by
        intro x y
        simp
        exact monomial_mul_mono b x y
      )]
  
  -- Since the product is monotone we extract the product from the supreme
  have h_id : (λb₁ => b₁) = @id (Monomial σ) := rfl
  simp only [h_id, ←Finset.max'_eq_sup'] at h_le
  let g := (· * q.monomials.max' h_q_nemp)
  let f := @id (Monomial σ)
  have h_gf : g ∘ f = λx => x * q.monomials.max' h_q_nemp := rfl
  rw [←h_gf, ←Finset.comp_sup'_eq_sup'_comp h_p_nemp (f := f) (g := g) (by
    intro x y
    simp
    rw [mul_comm, mul_comm x _, mul_comm y _]
    exact monomial_mul_mono (q.lead_monomial' h₀q) x y
  )] at h_le
  -- Translate supreme of monomials back into `lead_monomial`
  simp only [←Finset.max'_eq_sup'] at h_le

  -- All that remains is to prove that the maximum is reached, using `coeff_lead_monomial_mul`,
  -- since the product of lead coefficients cannot be `0` in an integrity domain
  apply eq_of_le_of_not_lt h_le
  apply not_lt_of_le
  clear h_le g f h_gf h_id
  have h_c := coeff_lead_monomial_mul h₀p h₀q
  have h_cp := lead_coeff_ne_zero p h₀p
  have h_cq := lead_coeff_ne_zero q h₀q
  -- In an integrity domain, the product of lead coefficients cannot be `0`
  have h_c₀ : (p * q).coeff (p.lead_monomial' h₀p * q.lead_monomial' h₀q) ≠ 0 := by
    simp [h_c, h_cp, h_cq]
  apply coeff_ne_zero_le_lead_monomial <;> assumption

/-- In an integrity domain, the lead coefficient of a product is the product of lead coefficients -/
@[simp]
lemma lead_coeff_mul {σ : Type _} {R : Type _} [CommRing R] [IsDomain R] [o : MonomialOrder σ]
    {p q : MvPolynomial σ R} :
    (p * q).lead_coeff = p.lead_coeff * q.lead_coeff := by
  by_cases h₀p : p = 0
  . -- If `p = 0` the product is as well, and the result is obvious
    have h₀pq : p * q = 0 := by simp [h₀p]
    have h_cp₀ : p.lead_coeff = 0 := by simp [h₀p]
    have h_cpq₀ : (p * q).lead_coeff = 0 := by simp [h₀pq]
    simp [h_cp₀, h_cpq₀]
  . by_cases h₀q : q = 0
    . -- Likewise if `q = 0`
      have h₀pq : p * q = 0 := by simp [h₀q]
      have h_cq₀ : q.lead_coeff = 0 := by simp [h₀q]
      have h_cpq₀ : (p * q).lead_coeff = 0 := by simp [h₀pq]
      simp [h_cq₀, h_cpq₀]
    . -- Otherwise we use `lead_monomial_mul` and `ne_zero_of_mul_ne_zero`
      have h₀pq : p * q ≠ 0 := ne_zero_of_mul_ne_zero h₀p h₀q
      rw [←lead_coeff_def (p * q) h₀pq, lead_monomial_mul h₀p h₀q h₀pq]
      -- In an integrity domain, this product cannot be `0`
      apply coeff_lead_monomial_mul

@[simp]
lemma lead_term_mul {σ : Type _} {R : Type _} [CommRing R] [IsDomain R] [o : MonomialOrder σ]
    {p q : MvPolynomial σ R} (h₀p : p ≠ 0) (h₀q : q ≠ 0) (h₀pq : p * q ≠ 0) :
    (p * q).lead_term' h₀pq = ⟨p.lead_coeff * q.lead_coeff, p.lead_monomial' h₀p * q.lead_monomial' h₀q⟩ := by
  rw [lead_term'_def]
  congr
  . apply lead_coeff_mul
  . apply lead_monomial_mul

@[simp]
lemma multi_deg_neg : (-p).multi_deg = p.multi_deg := by
  simp [multi_deg, lead_monomial_neg]

-- The norm_cast tactic is really useful here
@[simp]
lemma lead_coeff_neg : (-p).lead_coeff = - p.lead_coeff := by
  simp [lead_coeff]
  match h : lead_monomial p with
  | some m => simp [h, coeff]
  | none   => simp [h]

lemma coeff_zero_ne_lead (p : MvPolynomial σ R) (m : Monomial σ) :
    p.coeff m = 0 → p.lead_monomial ≠ m := by
  intro hc hm
  have h := Finset.mem_of_max hm
  rw [monomials, support, Finsupp.mem_support_toFun] at h
  contradiction

-- Auxiliary lemma
lemma Finset.max_union [LinearOrder α] (s r : Finset α) : max s.max r.max = (s ∪ r).max := by
  simp [max, Finset.max]
  rw [Finset.sup_union]


lemma multi_deg_eq (h : p.lead_term = q.lead_term) : p.multi_deg = q.multi_deg := by
  by_cases h₀p : p = 0
  . rw [h₀p, lead_term_zero] at h
    have h₀q : q = 0 := by
      by_contra h'
      have h'' := lead_term_ne_zero q h'
      have h := h.symm
      contradiction
    rw [h₀p, h₀q]
  . by_cases h₀q : q = 0
    . rw [h₀q, lead_term_zero] at h
      have h₀p : p = 0 := by
        by_contra h'
        have h'' := lead_term_ne_zero p h'
        contradiction
      rw [h₀p, h₀q]
    . rw [lead_term_def p h₀p, lead_term_def q h₀q, Option.some_inj] at h
      -- rw [lead_term'_def p h₀p, lead_term'_def q h₀q] at h
      have ⟨_, h_m⟩ := (Term.ext_iff ..).mp h
      rw [lead_term'_monomial_def, lead_term'_monomial_def] at h_m
      rw [multi_deg, multi_deg, lead_monomial'_def p h₀p, lead_monomial'_def q h₀q, h_m]


theorem multi_deg_add_le :
    (p + q).multi_deg ≤ max p.multi_deg q.multi_deg := by
  unfold multi_deg lead_monomial
  simp [Finset.max_union]
  apply Finset.max_mono
  -- We need to pass the `DecidableEq` instance explicitly, since
  -- `instDecidableEq [LinearOrder ..]` and `Finsupp.decidableEq` are not
  -- definitionally equal, and `Finsupp.decidableEq` has a higher priority
  exact @monomials_add _ _ _ instDecidableEq p q

lemma multi_deg_sub_le :
    (p - q).multi_deg ≤ max p.multi_deg q.multi_deg := by
  rw [sub_eq_add_neg, ←multi_deg_neg q]
  apply multi_deg_add_le

theorem multi_deg_sub_lt (h₀ : p ≠ 0) (ht : p.lead_term = q.lead_term) :
    (p - q).multi_deg < max p.multi_deg q.multi_deg := by
  apply lt_of_le_of_ne
  . -- We have already proved the bound
    apply multi_deg_sub_le
  . -- All that remains is to prove that the multidegrees are not equal
    have h₀q : q ≠ 0 := by
      intro hq
      rw [hq, lead_term_zero] at ht
      have : lead_term p ≠ ⊥ := lead_term_ne_zero p h₀
      contradiction
    have ht' : lead_term' p h₀ = lead_term' q h₀q := by
      rw [lead_term', lead_term']
      simp [ht]
    have hm : lead_monomial' p h₀ = lead_monomial' q h₀q := by
      rw [←lead_term'_monomial_def]
      rw [ht']
      simp
    have hc : lead_coeff p = lead_coeff q := by
      rw [←lead_term'_coeff_def]
      rw [ht']
      simp
    let m := lead_monomial' p h₀
    have h : (p - q).coeff m = 0 := by
      rw [sub_eq_add_neg, coeff_add, coeff_neg]
      simp only
      conv in (-coeff ..) => rw [hm]
      simp [hc]
    -- Since the coefficient is `0`, it can't be the lead monomial
    have h' := coeff_zero_ne_lead (p - q) m h
    simp only [multi_deg]
    rw [lead_monomial'_def p h₀, lead_monomial'_def q h₀q, hm]
    simpa [←hm] using h'

-- Corollary, since `p.multi_deg` is equal to `q.multi_deg`
lemma multi_deg_sub_lt_left (h₀ : p ≠ 0) (ht : p.lead_term = q.lead_term) :
    (p - q).multi_deg < p.multi_deg :=
  max_eq_left (le_of_eq (multi_deg_eq p q ht).symm) ▸ multi_deg_sub_lt p q h₀ ht

-- Alternate version of `multi_deg_sub_lt` using `lead_term'`, which also requires `q ≠ 0`
lemma multi_deg_sub_lt' (h₀p : p ≠ 0) (h₀q : q ≠ 0) (ht' : p.lead_term' h₀p = q.lead_term' h₀q) :
    (p - q).multi_deg < max p.multi_deg q.multi_deg := by
  have ht : p.lead_term = q.lead_term := by
    rw [lead_term_def, lead_term_def, ht']
  apply multi_deg_sub_lt <;> assumption


@[simp]
theorem multi_deg_add_of_mul {σ : Type _} {R : Type _} [Field R] [o : MonomialOrder σ]
    {p q : MvPolynomial σ R} (h₀p : p ≠ 0) (h₀q : q ≠ 0) :
    (p * q).multi_deg = p.multi_deg + q.multi_deg := by
  have h₀pq := ne_zero_of_mul_ne_zero h₀p h₀q
  unfold multi_deg

  rw [lead_monomial'_def (p * q) h₀pq, lead_monomial'_def p h₀p, lead_monomial'_def q h₀q]
  -- norm_cast -- Unfortunately, the normal cast form for WithBot/WithTop prefers to *sink down* casts
  -- rw [←WithBot.coe_add] -- This triggers a bug in the `rw` tactic (?), which can pollute the tactic state
  rw [←WithBot.coe_add (α := σ →₀ ℕ)]
  congr
  apply lead_monomial_mul h₀p h₀q

/-- Auxiliary lemma for the mv_divide case where we need to pass the lead_monomial to the remainder. -/
lemma multi_deg_sub_lead_monomial (h₀ : p ≠ 0)
    : (p - monomial (p.lead_monomial' h₀) p.lead_coeff).multi_deg < p.multi_deg := by
  have h_eq : p.lead_term = lead_term (
      monomial (lead_monomial' p h₀) (lead_coeff p)) := by
    simp [lead_term'_def p h₀ ▸ lead_term_def p h₀,
          lead_term_monomial (p.lead_monomial' h₀) (p.lead_coeff)
            (p.lead_coeff_ne_zero h₀)]
  apply multi_deg_sub_lt_left p (
    monomial (lead_monomial' p h₀) (lead_coeff p)) h₀ h_eq

end Lead

section Order

instance polyOrderFromMonomialOrder [MonomialOrder σ] [LinearOrder R] : LinearOrder (MvPolynomial σ R) :=
  -- The priority for the `monomialOrderFinsuppLinearOrder` declared above is
  -- enough to ensure it gets inferred here
  Finsupp.Lex.linearOrder

end Order

end Monomial
end MvPolynomial