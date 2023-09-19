import Mathlib.Data.Vector
import Mathlib.Data.Vector.Zip

namespace Vector

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {m n : ℕ}
variable (v : Vector α n) (v₁ : Vector α n) (w : Vector α n) (w₁ : Vector α n)
  (v₂ : Vector α m) (w₂: Vector α m) (i : Fin n) (i₁ : Fin n) (i₂ : Fin n) (a : α) (a₁ : α) (a₂ : α)

section Zero

instance zeroVec [Zero α] : Zero (Vector α n) where
  zero := Vector.replicate n 0

lemma zero_def [Zero α] : (0 : Vector α n) = Vector.replicate n 0 := rfl
lemma zero_ext_iff [Zero α] : v = 0 ↔ ∀a, a ∈ v.toList → a = 0 := by
  apply Iff.intro
  . intro h a
    simp only [h, zero_def, toList, replicate, List.mem_replicate]
    exact (·.right)
  . intro h
    cases n
    . simp
    . rename_i n'
      have h_r := List.eq_replicate_of_mem h
      simp only [toList_length] at h_r
      have h_r' : v = ⟨List.replicate (Nat.succ n') 0, by simp⟩ := by
        apply toList_injective
        exact h_r
      rw [←replicate] at h_r'
      simp [h_r', zero_def]

@[simp]
lemma zero_get [Zero α] : (0 : Vector α n).get i = 0 := by
  rw [zero_def, get_replicate]

end Zero

section Sum

def sum [Zero α] [Add α] : α :=
  v.toList.sum

lemma sum_append [AddMonoid α] : (v.append w).sum = v.sum + w.sum := by
  rw [sum, sum, sum, toList_append, List.sum_append]
lemma sum_cons [AddMonoid α] : (a ::ᵥ v).sum = a + v.sum := by
  rw [sum, sum, toList_cons, List.sum_cons]

@[simp]
lemma sum_zero [AddMonoid α] : (0 : Vector α n).sum = 0 := by
  rw [sum]
  have h₀ : ∀ a : α, a ∈ (0 : Vector α n).toList → a = 0 := by
    intro a
    simp only [zero_def, replicate, toList, List.mem_replicate]
    exact (·.right)
  exact List.sum_eq_zero h₀

end Sum

lemma zipWith_set (f : α → α → β) : (v.set i a₁).zipWith f (w.set i a₂) = (v.zipWith f w).set i (f a₁ a₂) := by
  let ⟨i', ih⟩ := i
  have ih_v := v.length_val.symm ▸ ih
  have ih_w := w.length_val.symm ▸ ih
  
  simp only [get_set_eq_if, zipWith, get, set]
  -- Unfolding List.nthLe makes it so the first argument of
  -- `List.get` is inaccessible to `conv` later (?)
  conv_lhs =>
    arg 1
    rw [List.set_eq_take_cons_drop a₁ ih_v]
    rw [List.set_eq_take_cons_drop a₂ ih_w]
    tactic =>
      rw [List.zipWith_append]
      . rw [List.length_take_of_le (le_of_lt ih_v), List.length_take_of_le (le_of_lt ih_w)]
  -- `conv` is broken so we need a fresh one
  conv_lhs =>
    arg 1
    rw [List.zipWith_cons_cons]
  apply Subtype.ext
  simp only
  rw [List.set_eq_take_cons_drop]
  rw [List.zipWith_distrib_take, List.zipWith_distrib_drop]
  rw [List.length_zipWith, v.length_val, w.length_val, min_self]
  exact ih

lemma set_get_eq (v : Vector α n) (i : Fin n) : v.set i (v.get i) = v := by
  ext j
  by_cases h : i = j
  . simp [h]
  . simp [get_set_of_ne, h]

section Dot
variable [Ring α]

def dot : α :=
  v.zipWith (· * ·) w |>.sum

lemma dot_cons : (a₁ ::ᵥ v).dot (a₂ ::ᵥ w) = a₁ * a₂ + v.dot w := by
  rw [dot, dot, sum, sum, zipWith_toList, zipWith_toList,
      toList_cons, toList_cons, List.zipWith_cons_cons, List.sum_cons]

lemma dot_append : (v₁.append v₂).dot (w₁.append w₂) = v₁.dot w₁ + v₂.dot w₂ := by
  rw [dot, dot, dot, sum, sum, sum, zipWith_toList, zipWith_toList]
  rw [toList_append, toList_append, List.zipWith_append, List.sum_append]
  suffices List.length (toList v₁) = List.length (toList w₁) by simp
  all_goals simp [toList_length]

lemma dot_set : (v.set i a₁).dot (w.set i a₂) =
    v.dot w + -(v.get i * w.get i) + a₁ * a₂ := by
  rw [dot, dot, zipWith_set, sum, sum, sum_set', zipWith_get]

lemma dot_set_right : v.dot (w.set i a) =
    v.dot w + -(v.get i * w.get i) + v.get i * a := by
  conv_lhs => rw [←set_get_eq v i]
  apply dot_set

lemma dot_set_left : (v.set i a).dot w = v.dot w + -(v.get i * w.get i) + a * w.get i := by
  conv_lhs => rw [←set_get_eq w i]
  apply dot_set

@[simp]
lemma dot_zero (v : Vector α n) : v.dot 0 = 0 := by
  rw [dot]
  have h₀ : zipWith (· * ·) v 0 = 0 := by
    ext i
    simp [zipWith_get]
  simp [h₀]

@[simp]
lemma zero_dot (v : Vector α n) : (0 : Vector α n).dot v = 0 := by
  rw [dot]
  have h₀ : zipWith (· * ·) 0 v = 0 := by
    ext i
    simp [zipWith_get]
  simp [h₀]

end Dot

section Any

def any (p : α → Bool) : Bool :=
  v.toList.any p

@[simp]
lemma any_nil (v : Vector α 0) (p : α → Bool) : v.any p = false := by
  simp [any]

lemma any_cons (p : α → Bool) : (a ::ᵥ v).any p = (p a || v.any p) := by
  rw [any, any, toList_cons, List.any_cons]

def anyP (p : α → Prop) : Prop :=
  ∃i : Fin n, p (v.get i)

def findIdx (p : α → Bool) : Option (Fin n) :=
  let i := v.toList.findIdx p
  if h : i < n then some ⟨i, h⟩ else none

variable (p : α → Bool)
theorem findIdx_nil (v : Vector α 0) : v.findIdx p = none := by
  simp [findIdx]

theorem findIdx_cons (v : Vector α n) : (a ::ᵥ v).findIdx p =
    bif p a then some ⟨0, by simp⟩ else (v.findIdx p).map Fin.succ := by
  by_cases h_a : p a
  . simp [findIdx, List.findIdx_cons, h_a]
  . simp only [
      findIdx, toList_cons, List.findIdx_cons, h_a,
      cond_false, Fin.mk_zero]
    rw [Option.map]
    by_cases h' : List.findIdx p v.toList < n
    . have h'' : List.findIdx p v.toList + 1 < Nat.succ n :=
        add_lt_add_right h' 1
      simp [h', h'']
    . have h'' : ¬(List.findIdx p v.toList + 1 < Nat.succ n) :=
        not_lt_of_le (add_le_add_right (le_of_not_lt h') 1)
      simp [h', h'']

-- If we remove `{n : ℕ}` (enabling auto-bound implicits), the induction tactic
-- will capture all `variable`s declared in this context, even if unused in the
-- theorem's type, effectively breaking the induction proof by adding junk
-- parameters to the hypothesis
theorem findIdx_none {n : ℕ} (v : Vector α n) (p : α → Bool)
    : v.findIdx p = none ↔ ¬v.any p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [←cons_head_tail v, findIdx_cons, any_cons]
    by_cases h : p (head v)
    . simp [h]
    . have hh := Bool.eq_false_eq_not_eq_true _ ▸ ih (tail v)
      simpa [h, hh]

private lemma List.findIdx.go.prop_k (p : α → Bool) (k : ℕ) (n : ℕ)
    : l.length ≤ k → List.findIdx.go p l n = List.findIdx p l + n := by
  induction k generalizing l n with
  | zero =>
    intro h_le
    have h : l = [] := by
      apply List.eq_nil_of_length_eq_zero
      apply Nat.eq_zero_of_le_zero h_le
    unfold List.findIdx.go
    simp [h]
  | succ m ih =>
    intro h_le
    rw [List.findIdx]
    unfold List.findIdx.go
    match h_l : l, h_0 : 0 with
    | [], k => simp [h_l, h_0]
    | a :: ls, k =>
      simp only [h_l, h_0]
      by_cases h_pa : p a
      . simp [h_pa, h_0]
      . simp only [h_pa, cond_false, ←h_0, zero_add]
        have h : ls.length ≤ m := by
          rw [List.length_cons] at h_le
          exact Nat.le_of_succ_le_succ h_le
        rw [ih (l := ls) 1 h, add_assoc, add_comm 1 _, ih (l := ls) (n + 1) h]

@[simp]
lemma List.findIdx.go.prop (n : ℕ) (p : α → Bool) : List.findIdx.go p l n = List.findIdx p l + n := by
  apply List.findIdx.go.prop_k p (l.length) n (by simp)

theorem findIdx_apply {n : ℕ} {v : Vector α n} {p : α → Bool} {i : Fin n}
    (h : v.findIdx p = some i) : p (v.get i) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases h_i : i = 0
    . rw [h_i] at h ⊢ 
      simp only [findIdx, List.findIdx] at h
      by_cases h' : List.findIdx p v.toList < Nat.succ n
      . simp only [List.findIdx.go.prop, add_zero, h', dite_true, Option.some.injEq] at h
        rw [get_zero]
        cases h_h : p (head v)
        . have h_cons := (congrArg toList v.cons_head_tail).symm
          rw [toList_cons] at h_cons
          conv at h in toList v =>
            rw [h_cons]
          unfold List.findIdx List.findIdx.go at h
          simp only [h_h, zero_add, List.findIdx.go.prop, cond_false] at h
          have h_n := congrArg Fin.val h
          norm_cast at h_n
        . rfl
      . simp [h'] at h
    . rw [←cons_head_tail v] at h ⊢
      let i' := Fin.pred i h_i
      have h_i' : i = i'.succ := by simp [Fin.succ_pred]
      rw [h_i', get_cons_succ]
      apply ih
      rw [h_i', findIdx_cons] at h
      by_cases h_h : p (v.head)
      . have h_h' : 0 = i := by simpa [h_h] using h
        rw [h_i'] at h_h'
        have h_c := Fin.succ_ne_zero i' h_h'.symm
        contradiction
      . simp only [h_h, cond_false, Fin.succ_pred, Option.map_eq_some'] at h
        choose a' h_a' using h
        let ⟨h_a'₁, h_a'₂⟩ := h_a'
        rw [h_i', Fin.succ_inj] at h_a'₂
        simp [h_a'₁, h_a'₂]

def all (p : α → Prop) : Prop :=
  ∀i : Fin n, p (v.get i)

end Any

section Add

def add [Add α] (v w : Vector α n) :=
  v.zipWith (· + ·) w

lemma dot_add [Ring α] (v w₁ w₂ : Vector α n)
    : v.dot (w₁.add w₂) = v.dot w₁ + v.dot w₂ := by
  rw [Vector.dot, Vector.dot, Vector.dot]
  rw [Vector.sum, Vector.sum, Vector.sum]
  rw [Vector.sum_add_sum_eq_sum_zipWith]
  congr 2
  ext i
  rw [zipWith_get, zipWith_get, zipWith_get, zipWith_get]
  rw [add, zipWith_get]
  rw [left_distrib]

end Add

section SetAdd

def addAt [Add α] (v : Vector α n) (i : Fin n) (a : α) :=
  v.set i (v.get i + a)

end SetAdd

end Vector