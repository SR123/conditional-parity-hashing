import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Binary linear hashing: exact collision counts

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

A binary `k × n` matrix is stored as its `k` rows.  For distinct `z z' : 𝔽₂ⁿ`
exactly a `2^{-k}` fraction of all matrices satisfies `M z = M z'`.
This is the only algebraic input of the common-linear hashing argument.
No axioms beyond Lean/Mathlib are used.
-/

namespace ParityHashing

open Finset

/-- Binary vectors of length `n`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- Binary `k × n` matrices, stored as rows. -/
abbrev Mat (k n : ℕ) := Fin k → Vec n

/-- Binary inner product. -/
def dot {n : ℕ} (r v : Vec n) : ZMod 2 := ∑ t, r t * v t

/-- Matrix-vector product over `𝔽₂`. -/
def mulVec {k n : ℕ} (M : Mat k n) (v : Vec n) : Vec k := fun i => dot (M i) v

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

theorem zmod2_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert x; decide

theorem zmod2_eq_iff (x y : ZMod 2) : x = y ↔ x + y = 0 := by
  revert x y; decide

theorem vec_add_self {n : ℕ} (v : Vec n) : v + v = 0 := by
  funext t
  exact zmod2_add_self (v t)

theorem vec_eq_iff_add_eq_zero {n : ℕ} (v w : Vec n) : v = w ↔ v + w = 0 := by
  constructor
  · rintro rfl; exact vec_add_self v
  · intro h
    funext t
    have := congrFun h t
    exact (zmod2_eq_iff (v t) (w t)).2 this

theorem dot_add_left {n : ℕ} (r r' v : Vec n) : dot (r + r') v = dot r v + dot r' v := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_add_right {n : ℕ} (r v v' : Vec n) : dot r (v + v') = dot r v + dot r v' := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_single {n : ℕ} (t₀ : Fin n) (v : Vec n) : dot (Pi.single t₀ 1) v = v t₀ := by
  classical
  unfold dot
  rw [Finset.sum_eq_single t₀]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ t₀) h

theorem mulVec_add {k n : ℕ} (M : Mat k n) (v v' : Vec n) :
    mulVec M (v + v') = mulVec M v + mulVec M v' := by
  funext i
  exact dot_add_right (M i) v v'

theorem card_vec (n : ℕ) : Fintype.card (Vec n) = 2 ^ n := by
  simp [Vec, Fintype.card_fun, ZMod.card]

theorem card_mat (k n : ℕ) : Fintype.card (Mat k n) = (2 ^ n) ^ k := by
  simp [Mat, Vec, Fintype.card_fun, ZMod.card]

/-- A nonzero linear functional on `𝔽₂ⁿ` vanishes on exactly half of the vectors. -/
theorem two_mul_card_dot_zero {n : ℕ} {v : Vec n} (hv : v ≠ 0) :
    2 * Fintype.card {r : Vec n // dot r v = 0} = 2 ^ n := by
  classical
  obtain ⟨t₀, ht₀⟩ : ∃ t, v t ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hv1 : v t₀ = 1 := zmod2_ne_zero ht₀
  set e : Vec n := Pi.single t₀ 1 with he
  have hflip : ∀ r : Vec n, dot (r + e) v = dot r v + 1 := by
    intro r
    rw [dot_add_left, he, dot_single, hv1]
  have hee : ∀ r : Vec n, r + e + e = r := by
    intro r
    rw [add_assoc, vec_add_self, add_zero]
  -- the flip `r ↦ r + e` exchanges the two level sets
  let φ : {r : Vec n // dot r v = 0} ≃ {r : Vec n // dot r v = 1} :=
    { toFun := fun r => ⟨r.1 + e, by rw [hflip, r.2, zero_add]⟩
      invFun := fun r => ⟨r.1 + e, by rw [hflip, r.2, zmod2_add_self]⟩
      left_inv := fun r => Subtype.ext (hee r.1)
      right_inv := fun r => Subtype.ext (hee r.1) }
  have hcard01 := Fintype.card_congr φ
  -- the two level sets partition the space
  let ψ : {r : Vec n // dot r v = 0} ⊕ {r : Vec n // dot r v = 1} ≃ Vec n :=
    { toFun := fun x => Sum.elim (fun r => r.1) (fun r => r.1) x
      invFun := fun r =>
        if h : dot r v = 0 then Sum.inl ⟨r, h⟩
        else Sum.inr ⟨r, zmod2_ne_zero h⟩
      left_inv := by
        intro x
        rcases x with r | r
        · simp [r.2]
        · have h1 : dot r.1 v ≠ 0 := by rw [r.2]; decide
          simp [h1]
      right_inv := by
        intro r
        by_cases h : dot r v = 0 <;> simp [h] }
  have htot := Fintype.card_congr ψ
  rw [Fintype.card_sum, card_vec] at htot
  omega

/-- Matrices whose every row is orthogonal to `v`. -/
theorem card_mat_kernel {k n : ℕ} (v : Vec n) :
    Fintype.card {M : Mat k n // ∀ i, dot (M i) v = 0} =
      Fintype.card {r : Vec n // dot r v = 0} ^ k := by
  let e : {M : Mat k n // ∀ i, dot (M i) v = 0} ≃ (Fin k → {r : Vec n // dot r v = 0}) :=
    { toFun := fun M i => ⟨M.val i, M.property i⟩
      invFun := fun f => ⟨fun i => (f i).val, fun i => (f i).property⟩
      left_inv := fun M => Subtype.ext rfl
      right_inv := fun f => by funext i; rfl }
  rw [Fintype.card_congr e]
  simp

/-- Exact collision count for two distinct inputs. -/
theorem card_collide_mul_pow {k n : ℕ} {z z' : Vec n} (hzz : z ≠ z') :
    ((univ.filter fun M : Mat k n => mulVec M z = mulVec M z').card : ℝ) * 2 ^ k =
      (Fintype.card (Mat k n) : ℝ) := by
  classical
  have hv : z + z' ≠ 0 := by
    intro h
    exact hzz ((vec_eq_iff_add_eq_zero z z').2 h)
  have hfilter : (univ.filter fun M : Mat k n => mulVec M z = mulVec M z').card =
      Fintype.card {M : Mat k n // ∀ i, dot (M i) (z + z') = 0} := by
    rw [Fintype.card_subtype]
    congr 1
    ext M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [vec_eq_iff_add_eq_zero, ← mulVec_add]
    constructor
    · intro h i
      exact congrFun h i
    · intro h
      funext i
      exact h i
  rw [hfilter, card_mat_kernel, card_mat]
  have h2 := two_mul_card_dot_zero (n := n) hv
  set c := Fintype.card {r : Vec n // dot r (z + z') = 0}
  have h2r : (2 : ℝ) * c = 2 ^ n := by exact_mod_cast h2
  push_cast
  rw [← mul_pow, mul_comm, h2r]

/-- Collision count as a real bound valid for all pairs of inputs. -/
theorem card_collide_le {k n : ℕ} (z z' : Vec n) :
    ((univ.filter fun M : Mat k n => mulVec M z' = mulVec M z).card : ℝ) ≤
      (Fintype.card (Mat k n) : ℝ) * ((if z' = z then 1 else 0) + (2 ^ k)⁻¹) := by
  classical
  by_cases h : z' = z
  · subst h
    have hI : 0 ≤ ((2:ℝ)^k)⁻¹ := by positivity
    have hOne : (1:ℝ) ≤ 1 + ((2:ℝ)^k)⁻¹ := by linarith
    have hb := mul_le_mul_of_nonneg_left hOne (Nat.cast_nonneg (Fintype.card (Mat k n)))
    simpa using hb
  · simp only [h, ite_false, zero_add]
    have hc := card_collide_mul_pow (k := k) h
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    rw [← hc]
    field_simp
    exact le_rfl

end ParityHashing
