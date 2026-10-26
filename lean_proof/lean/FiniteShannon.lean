import FiniteInformation

/-! Shannon inequalities derived from finite masses, without research axioms. -/

namespace SharpStability
noncomputable section
open Finset
variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

theorem array_entropy_subadditive (p : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) :
    0 ≤ (∑ ab, p ab * Real.log (p ab)) +
      (∑ ab, p ab) * Real.log (∑ ab, p ab) -
      (∑ a, (∑ b, p (a,b)) * Real.log (∑ b, p (a,b))) -
      (∑ b, (∑ a, p (a,b)) * Real.log (∑ a, p (a,b))) := by
  classical
  let m := ∑ ab, p ab
  let row := fun a => ∑ b, p (a,b)
  let col := fun b => ∑ a, p (a,b)
  have hm : 0 ≤ m := sum_nonneg (fun ab _ => hp ab)
  have hrow : ∀ a, 0 ≤ row a := fun a => sum_nonneg (fun b _ => hp (a,b))
  have hcol : ∀ b, 0 ≤ col b := fun b => sum_nonneg (fun a _ => hp (a,b))
  have hpr : ∀ a b, p (a,b) ≤ row a := fun a b => single_le_sum (fun x _ => hp (a,x)) (mem_univ b)
  have hpc : ∀ a b, p (a,b) ≤ col b := fun a b => single_le_sum (fun x _ => hp (x,b)) (mem_univ a)
  have hrm : ∑ a, row a = m := by simp only [m, row, Fintype.sum_prod_type]
  have hcm : ∑ b, col b = m := by simp only [m, col, Fintype.sum_prod_type]; exact sum_comm
  by_cases hm0 : m = 0
  · have hp0 : ∀ ab, p ab = 0 := by
      intro ab
      have hpm : p ab ≤ m := single_le_sum (fun x _ => hp x) (mem_univ ab)
      exact le_antisymm (by simpa [hm0] using hpm) (hp ab)
    simp [hp0]
  have hm' : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  let q : α × β → ℝ := fun ab => row ab.1 * col ab.2 / m
  have hq : ∀ ab, 0 ≤ q ab := fun ab => div_nonneg (mul_nonneg (hrow _) (hcol _)) hm
  have hsupport : ∀ ab, 0 < p ab → 0 < q ab := by
    rintro ⟨a,b⟩ hab
    exact div_pos (mul_pos (hab.trans_le (hpr a b)) (hab.trans_le (hpc a b))) hm'
  have hqt : ∑ ab, q ab = m := by
    simp only [q, Fintype.sum_prod_type, ← sum_div, ← mul_sum, ← sum_mul, hrm, hcm]
    field_simp
  have hg := finite_gibbs hp hq hsupport
  rw [hqt] at hg
  have hterm : ∀ ab,
      p ab * Real.log (q ab / p ab) =
        p ab * Real.log (row ab.1) + p ab * Real.log (col ab.2) -
        p ab * Real.log m - p ab * Real.log (p ab) := by
    rintro ⟨a,b⟩
    by_cases hz : p (a,b) = 0
    · simp [hz]
    have hp' : 0 < p (a,b) := lt_of_le_of_ne (hp _) (Ne.symm hz)
    have hr : 0 < row a := hp'.trans_le (hpr a b)
    have hc : 0 < col b := hp'.trans_le (hpc a b)
    dsimp [q]
    rw [Real.log_div (div_ne_zero (mul_ne_zero hr.ne' hc.ne') hm0) hz,
      Real.log_div (mul_ne_zero hr.ne' hc.ne') hm0, Real.log_mul hr.ne' hc.ne']
    ring
  have hrowlog : ∑ ab : α × β, p ab * Real.log (row ab.1) = ∑ a, row a * Real.log (row a) := by
    simp only [Fintype.sum_prod_type, ← sum_mul, row]
  have hcollog : ∑ ab : α × β, p ab * Real.log (col ab.2) = ∑ b, col b * Real.log (col b) := by
    simp only [Fintype.sum_prod_type]
    rw [sum_comm]
    simp only [← sum_mul, col]
  simp only [hterm, sum_sub_distrib, sum_add_distrib, hrowlog, hcollog, ← sum_mul] at hg
  change 0 ≤ (∑ ab, p ab * Real.log (p ab)) + m * Real.log m -
    (∑ a, row a * Real.log (row a)) - (∑ b, col b * Real.log (col b))
  dsimp [m] at hg ⊢
  linarith

theorem mapEntropyNats_subadditive (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w)
    (htotal : ∑ w, p w = 1) (f : Ω → α) (g : Ω → β) :
    0 ≤ mapEntropyNats p f + mapEntropyNats p g -
      mapEntropyNats p (fun w => (f w, g w)) := by
  have h := array_entropy_subadditive (cellMass p (fun w => (f w,g w)))
    (cellMass_nonneg hp _)
  rw [cellMass_total, htotal] at h
  simp only [cellMass_pair_fst, cellMass_pair_snd, Real.log_one, mul_zero, add_zero] at h
  unfold mapEntropyNats
  linarith

theorem cellMass_triple_row (p : Ω → ℝ) (f : Ω → α) (g : Ω → β)
    (z : Ω → γ) (a : α) (c : γ) :
    ∑ b, cellMass p (fun w => (f w, (g w, z w))) (a,(b,c)) =
      cellMass p (fun w => (f w,z w)) (a,c) := by
  classical
  unfold cellMass
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  by_cases hf : f w = a
  · by_cases hz : z w = c
    · simp [Prod.mk.injEq, hf, hz, eq_comm]
    · simp [Prod.mk.injEq, hf, hz, Ne.symm hz, eq_comm]
  · by_cases hz : z w = c
    · simp [Prod.mk.injEq, hf, Ne.symm hf, hz, eq_comm]
    · simp [Prod.mk.injEq, hf, Ne.symm hf, hz, Ne.symm hz, eq_comm]

theorem cellMass_triple_col (p : Ω → ℝ) (f : Ω → α) (g : Ω → β)
    (z : Ω → γ) (b : β) (c : γ) :
    ∑ a, cellMass p (fun w => (f w, (g w, z w))) (a,(b,c)) =
      cellMass p (fun w => (g w,z w)) (b,c) := by
  classical
  unfold cellMass
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  by_cases hg : g w = b
  · by_cases hz : z w = c
    · simp [Prod.mk.injEq, hg, hz, eq_comm]
    · simp [Prod.mk.injEq, hg, hz, Ne.symm hz, eq_comm]
  · by_cases hz : z w = c
    · simp [Prod.mk.injEq, hg, Ne.symm hg, hz, eq_comm]
    · simp [Prod.mk.injEq, hg, Ne.symm hg, hz, Ne.symm hz, eq_comm]

theorem cellMass_triple_total (p : Ω → ℝ) (f : Ω → α) (g : Ω → β)
    (z : Ω → γ) (c : γ) :
    ∑ ab : α × β, cellMass p (fun w => (f w, (g w, z w))) (ab.1,(ab.2,c)) =
      cellMass p z c := by
  rw [Fintype.sum_prod_type]
  simp only [cellMass_triple_row]
  exact cellMass_pair_snd p f z c

theorem mapEntropyNats_cond_subadditive (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w)
    (f : Ω → α) (g : Ω → β) (z : Ω → γ) :
    0 ≤ mapEntropyNats p (fun w => (f w,z w)) +
      mapEntropyNats p (fun w => (g w,z w)) - mapEntropyNats p z -
      mapEntropyNats p (fun w => (f w,(g w,z w))) := by
  have h := sum_nonneg (s := (univ : Finset γ)) (fun c _ =>
    array_entropy_subadditive
      (fun ab : α × β => cellMass p (fun w => (f w,(g w,z w))) (ab.1,(ab.2,c)))
      (fun ab => cellMass_nonneg hp _ _))
  simp only [cellMass_triple_row, cellMass_triple_col, cellMass_triple_total,
    sum_sub_distrib, sum_add_distrib] at h
  have htrip : (∑ c, ∑ ab : α × β,
      cellMass p (fun w => (f w,(g w,z w))) (ab.1,(ab.2,c)) *
        Real.log (cellMass p (fun w => (f w,(g w,z w))) (ab.1,(ab.2,c)))) =
      ∑ abc : α × (β × γ), cellMass p (fun w => (f w,(g w,z w))) abc *
        Real.log (cellMass p (fun w => (f w,(g w,z w))) abc) := by
    simp only [Fintype.sum_prod_type]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    exact sum_comm
  rw [htrip] at h
  have hrow : (∑ c, ∑ a,
      cellMass p (fun w => (f w,z w)) (a,c) *
        Real.log (cellMass p (fun w => (f w,z w)) (a,c))) =
      ∑ ac : α × γ, cellMass p (fun w => (f w,z w)) ac *
        Real.log (cellMass p (fun w => (f w,z w)) ac) := by
    rw [Fintype.sum_prod_type]
    exact sum_comm
  have hcol : (∑ c, ∑ b,
      cellMass p (fun w => (g w,z w)) (b,c) *
        Real.log (cellMass p (fun w => (g w,z w)) (b,c))) =
      ∑ bc : β × γ, cellMass p (fun w => (g w,z w)) bc *
        Real.log (cellMass p (fun w => (g w,z w)) bc) := by
    rw [Fintype.sum_prod_type]
    exact sum_comm
  rw [hrow, hcol] at h
  unfold mapEntropyNats
  linarith

end
end SharpStability
