import Mathlib.Data.Nat.Basic
import MvDivide.MvPolynomial.Monomial
import MvDivide.Correctness.NonZero
import MvDivide.Correctness.CorrectResult

import MvDivide.Correctness.AlgAttr

namespace NonZero
open MvPolynomial

variable (α) {σ : Type _} {R : Type _} {F : Type _} [CommRing R] [Field F] [MonomialOrder σ]

-- Weak version of [IsDomain] for convenience
class MulPreservesNonNull [Zero α] [Mul α] where
  nz_of_mul {a b : α} : a ≠ 0 → b ≠ 0 → a * b ≠ 0
variable {α}

instance mul [Zero α] [Mul α] [inst : MulPreservesNonNull α] : Mul (NonZero α) where
  mul a b := ⟨a.val * b.val, inst.nz_of_mul a.ne_zero b.ne_zero⟩

instance mulDomain [IsDomain R] : Mul (NonZero R) where
  mul a b := ⟨a.val * b.val, by simp⟩

@[simp]
lemma ne_zero_mul_def [Zero α] [Mul α] [MulPreservesNonNull α]
    (a b : NonZero α) : (a * b).val = a.val * b.val :=
  rfl

instance fieldMulPreservesNonNull : MulPreservesNonNull F where
  nz_of_mul h₀a h₀b := by simp [h₀a, h₀b]

instance fieldPolyPreservesNonNull [MonomialOrder σ] : MulPreservesNonNull (MvPolynomial σ F) where
  nz_of_mul {p q} h₀p h₀q := by
    exact ne_zero_of_mul_ne_zero h₀p h₀q

def lead_monomial (p : NonZero (MvPolynomial σ R)) [MonomialOrder σ] : Monomial σ :=
  (p.val).lead_monomial' p.ne_zero

def lead_coeff (p : NonZero (MvPolynomial σ R)) [MonomialOrder σ] : NonZero R :=
  ⟨(p.val).lead_coeff, lead_coeff_ne_zero p.val p.ne_zero⟩

def lead_term (p : NonZero (MvPolynomial σ R)) [MonomialOrder σ] : NonZero R × Monomial σ :=
  (p.lead_coeff, p.lead_monomial)

def lead_term' (p : NonZero (MvPolynomial σ R)) [MonomialOrder σ] : Term σ R :=
  p.val.lead_term' p.ne_zero

end NonZero

noncomputable section
open Classical

namespace MvPolynomial
namespace MvDivide

variable {F : Type _} [Field F] [MonomialOrder σ] (p r : MvPolynomial σ F) (s d : NonZero (MvPolynomial σ F))
  (dd : Vector (NonZero (MvPolynomial σ F)) n)

def can_divide_lead := d.lead_monomial ∣ s.lead_monomial
def can_divide_lead' := if h : p ≠ 0 then can_divide_lead ⟨p, h⟩ d else False

def cannot_divide :=
  ∀m ∈ p.monomials, ¬(d.lead_monomial ∣ m)

def cannot_divide_lead_any :=
  if h : p ≠ 0 then ∀i : Fin n, ¬can_divide_lead ⟨p, h⟩ (dd.get i) else True
def cannot_divide_any :=
  ∀i : Fin n, cannot_divide p (dd.get i)

@[simp]
lemma cannot_divide_any_zero : cannot_divide_any 0 dd := by
  rw [cannot_divide_any]
  intro i
  rw [cannot_divide]
  rw [monomials, support_zero]
  intro m h
  contradiction

lemma cannot_divide_any_of_lead
    (h₀ : r ≠ 0) (h : cannot_divide_lead_any r dd)
    : cannot_divide_any ((monomial (r.lead_monomial' h₀)) r.lead_coeff) dd := by
  rw [cannot_divide_lead_any] at h
  simp [h₀] at h
  rw [cannot_divide_any]
  let r_lm := (monomial (r.lead_monomial' h₀)) r.lead_coeff
  by_cases h_lm₀ : r_lm = 0
  . simp only [h_lm₀]
    exact cannot_divide_any_zero dd
  . rw [←ne_eq] at h_lm₀
    simp [h_lm₀, h₀]
    intro i
    have h₂i := h i
    rw [can_divide_lead] at h₂i
    rw [cannot_divide]
    intro m
    rw [monomials_of_monomial]
    simp [h₀]
    intro h_m
    rw [h_m]
    conv at h₂i =>
      arg 1; arg 2
      rw [NonZero.lead_monomial]
    simpa using h₂i

lemma cannot_divide_any_add
    (h_p : cannot_divide_any p dd) (h_r : cannot_divide_any r dd) : cannot_divide_any (p + r) dd := by
  rw [cannot_divide_any] at h_p h_r ⊢
  by_cases h_p₀ : p = 0
  . rw [h_p₀, zero_add]; exact h_r
  . by_cases h_r₀ : r = 0
    . rw [h_r₀, add_zero]; exact h_p
    . by_cases h : p + r = 0
      . exact h ▸ cannot_divide_any_zero dd
      . intro i; rw [cannot_divide]; intro m h_m
        have h_subs := Finset.mem_of_subset (monomials_add p r) h_m
        match (@Finset.mem_union _ Finsupp.decidableEq _ _ _).mp h_subs with
        | .inl h => exact h_p i m h
        | .inr h => exact h_r i m h

def can_divide_any (p : NonZero (MvPolynomial σ F)) (d : Vector (NonZero (MvPolynomial σ F)) n) :=
  d.any (can_divide_lead p ·)
def can_divide'_any (p : MvPolynomial σ F) (d : Vector (NonZero (MvPolynomial σ F)) n) :=
  if h : p ≠ 0 then d.any (can_divide_lead ⟨p, h⟩ ·) else False


@[alg simp]
def monomial_quotient_alg (m d : Monomial σ) (h : d ∣ m) : Monomial σ
such_that d * it = m :=
  m.toFinsupp - d.toFinsupp correct_by
    rw [monomial_mul_def]
    unfold Monomial Monomial.toFinsupp at *
    ext i
    rw [Finsupp.add_apply, Finsupp.tsub_apply]
    apply add_tsub_cancel_of_le (h i)

@[alg simp]
def partial_quotient_alg (h : can_divide_lead s d) : NonZero (MvPolynomial σ F)
such_that (d * it).lead_term = s.lead_term :=
  ⟨monomial
    (monomial_quotient s.lead_monomial d.lead_monomial h)
    (s.lead_coeff.val / d.lead_coeff.val),
  by simp⟩ correct_by
    ext
    all_goals simp only [NonZero.lead_term]
    . suffices d.val.lead_coeff * (s.val.lead_coeff / d.val.lead_coeff) = s.val.lead_coeff by
        simpa [NonZero.lead_coeff]
      -- `simp_arith` doesn't seem capable to rearrange the terms to apply `mul_div_cancel`
      rw [mul_comm]
      simp_arith
    . simp [NonZero.lead_monomial] -- `monomial_quotient_spec` is applied automatically thanks to @[alg simp]

-- Created by @[alg]:
-- def partial_quotient (h : can_divide_lead p q) : NonZero (MvPolynomial σ F) :=
--   (partial_quotient_alg p q h).1
-- @[simp]
-- lemma partial_quotient_spec (h : can_divide_lead p q) : (q * (partial_quotient p q h)).lead_term = p.lead_term := by
--   rw [partial_quotient]
--   exact (partial_quotient_alg p q h).correctness

@[alg]
def divide_step_alg (h : can_divide_lead s d)
    : MvPolynomial σ F × NonZero (MvPolynomial σ F)
such_that (r, q) => s = r + d * q ∧ r.multi_deg < s.val.multi_deg := 
  (s.val - (d * partial_quotient s d h).val, partial_quotient s d h) correct_by
    constructor
    . simp
    . have hq := partial_quotient_spec s d h
      simp only [NonZero.lead_term, NonZero.lead_coeff, NonZero.lead_monomial] at hq
      have ⟨h₁, h₂⟩ := Prod.ext_iff.mp hq
      simp only [Subtype.ext_iff] at h₁ h₂
      have h' : (d * partial_quotient s d h).val.multi_deg = s.val.multi_deg := by
        simp only [multi_deg]
        rw [lead_monomial'_def (d * partial_quotient s d h).val (d * partial_quotient s d h).ne_zero]
        rw [lead_monomial'_def s.val s.ne_zero]
        rw [h₂]
      have h'' := max_eq_left (le_of_eq h')
      rw [←h'']
      apply multi_deg_sub_lt'
      ext
      . rw [lead_term'_coeff_def _ (d * partial_quotient s d h).ne_zero,
            lead_term'_coeff_def _ s.ne_zero,
            h₁]
      . rw [lead_term'_monomial_def, lead_term'_monomial_def, h₂]

instance multi_deg_well_founded [o : MonomialOrder σ] : WellFoundedRelation (WithBot (σ →₀ ℕ)) where
  rel := WithBot.preorder.toLT.lt
  wf := WithBot.wellFounded_lt o.well_founded_lt.wf

-- `h_decreases` is reported as unused because it's only used as the termination hint.
set_option linter.unusedVariables false in

@[alg]
def divide_one_alg (p : MvPolynomial σ F) (d : NonZero (MvPolynomial σ F))
    : (MvPolynomial σ F) × (MvPolynomial σ F)
such_that (q, r) => p = d * q + r ∧ ¬can_divide_lead' r d :=
  if h₀ : p ≠ 0 then
    if h_d : can_divide_lead ⟨p, h₀⟩ d then
      let ⟨(p_s, q_s), ⟨h_s_eq, h_decreases⟩⟩ := divide_step_alg ⟨p, h₀⟩ d h_d
      -- Termination hint: the `multi_deg` of the dividend decreases
      -- not needed, because `decreasingTactic` tries `assumption` and finds `h_decreases`
      -- have: p_s.multi_deg < p.multi_deg := h_decreases
      let ⟨⟨q, r⟩, ⟨h_r_eq, h_r_dvd⟩⟩ := divide_one_alg p_s d
      (q + q_s, r) correct_by
        constructor
        . simp only at h_s_eq h_r_eq h_r_dvd ⊢
          rw [h_s_eq, h_r_eq]
          ring
        . by_cases h_r₀ : r = 0
          . simp [can_divide_lead, can_divide_lead', h_r₀]
          . simpa [can_divide_lead, can_divide_lead', h_r₀] using h_r_dvd
    else (0, p) correct_by
      constructor
      . simp
      . simp [can_divide_lead, can_divide_lead', NonZero.lead_monomial, multi_deg, h₀] at h_d ⊢
        exact h_d
  else (0, p) correct_by
    constructor
    . simp
    . rw [not_ne_iff] at h₀
      simp [h₀, can_divide_lead']
-- Termination by the well founded order on the `multi_deg` of the dividend
termination_by divide_one_alg p d => p.multi_deg

-- `h_decreases` is reported as unused because it's only used as the termination hint for `decreasing_tactic`
-- but we prefer to give it a name instead of using `_` for clarity
set_option linter.unusedVariables false in

@[alg]
def mv_divide_alg {n : ℕ} (p : MvPolynomial σ F) (dd : Vector (NonZero (MvPolynomial σ F)) n)
    : Vector (MvPolynomial σ F) n × (MvPolynomial σ F)
such_that (q, r) => p = (dd.map (·.val)).dot q + r ∧ cannot_divide_any r dd :=
  if h₀ : p ≠ 0 then
    if h_i : (∃i : Fin n, can_divide_lead ⟨p, h₀⟩ (dd.get i)) then
      let i := h_i.choose
      let ⟨(p_s, q_s), ⟨h_s_eq, h_decreases⟩⟩ := divide_step_alg ⟨p, h₀⟩
        (dd.get i) (h_i.choose_spec)
      let ⟨⟨q, r⟩, ⟨h_r_eq, h_r_cannot_divide⟩⟩ := mv_divide_alg p_s dd
      (q.addAt i q_s, r) correct_by
        constructor
        . simp only at h_s_eq
          rw [h_s_eq, Vector.addAt, Vector.dot_set_right, Vector.get_map, h_r_eq]
          ring
        . exact h_r_cannot_divide
    else
      let p_lt := monomial (p.lead_monomial' h₀) p.lead_coeff
      let p' := p - p_lt
      have: p'.multi_deg < p.multi_deg := multi_deg_sub_lead_monomial p h₀
      let ⟨⟨q', r⟩, ⟨hr₁, hr₂⟩⟩ := mv_divide_alg p' dd
      (q', p_lt + r) correct_by
        constructor
        . rw [←sub_eq_of_eq_add hr₁, show p' = p - p_lt by rfl]; ring
        . apply cannot_divide_any_add p_lt r dd
          . apply cannot_divide_any_of_lead p dd h₀
            simp [cannot_divide_lead_any, h₀, not_exists.mp h_i]
          . exact hr₂
  else (0, p) correct_by
    constructor
    . simp
    . rw [ne_eq, not_not] at h₀
      simp [cannot_divide_lead_any, h₀]
termination_by mv_divide_alg p dd => p.multi_deg

theorem exists_mv_quorem (p : MvPolynomial σ F) (d : Vector (NonZero (MvPolynomial σ F)) n)
    : ∃ q : Vector (MvPolynomial σ F) n, ∃ r : MvPolynomial σ F,
        p = (d.map (·.val)).dot q + r ∧ cannot_divide_any r d := by
  use (mv_divide p d).1, (mv_divide p d).2
  exact mv_divide_spec p d

end MvDivide
end MvPolynomial
end