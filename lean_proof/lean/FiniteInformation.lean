import FiniteLaw
import Mathlib

/-! Elementary finite entropy and the finite log-sum inequality. -/

namespace SharpStability
noncomputable section
open Finset

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

def cellMass (p : Ω → ℝ) (f : Ω → α) (a : α) : ℝ := by
  classical
  exact ∑ w, if f w = a then p w else 0

def mapEntropyNats (p : Ω → ℝ) (f : Ω → α) : ℝ :=
  -(∑ a, cellMass p f a * Real.log (cellMass p f a))

theorem cellMass_nonneg {p : Ω → ℝ} (hp : ∀ w, 0 ≤ p w) (f : Ω → α) (a : α) :
    0 ≤ cellMass p f a := by
  classical
  unfold cellMass
  exact sum_nonneg (fun w _ => by split_ifs; exact hp w; exact le_rfl)

theorem cellMass_total (p : Ω → ℝ) (f : Ω → α) :
    ∑ a, cellMass p f a = ∑ w, p w := by
  classical
  unfold cellMass
  rw [sum_comm]
  simp [eq_comm]

theorem mass_le_cellMass {p : Ω → ℝ} (hp : ∀ w, 0 ≤ p w) (f : Ω → α) (w : Ω) :
    p w ≤ cellMass p f (f w) := by
  classical
  have h := single_le_sum (s := (univ : Finset Ω)) (f := fun v =>
      if f v = f w then p v else 0)
    (fun v _ => by split_ifs; exact hp v; exact le_rfl) (mem_univ w)
  simpa [cellMass] using h

theorem cellMass_id (p : Ω → ℝ) (w : Ω) : cellMass p id w = p w := by
  classical
  simp [cellMass, eq_comm]

theorem mapEntropyNats_atom (p : Ω → ℝ) (f : Ω → α) :
    mapEntropyNats p f = -(∑ w, p w * Real.log (cellMass p f (f w))) := by
  classical
  unfold mapEntropyNats
  congr 1
  calc
    ∑ a, cellMass p f a * Real.log (cellMass p f a) =
        ∑ a, ∑ w, (if f w = a then p w else 0) *
          Real.log (cellMass p f a) := by simp only [cellMass, sum_mul]
    _ = ∑ w, ∑ a, (if f w = a then p w else 0) *
          Real.log (cellMass p f a) := sum_comm
    _ = ∑ w, p w * Real.log (cellMass p f (f w)) := by simp [eq_comm]

theorem mapEntropyNats_same_fibers (p : Ω → ℝ) (f : Ω → α) (g : Ω → β)
    (hfg : ∀ w v, f w = f v ↔ g w = g v) :
    mapEntropyNats p f = mapEntropyNats p g := by
  classical
  rw [mapEntropyNats_atom, mapEntropyNats_atom]
  congr 1
  apply sum_congr rfl
  intro w _
  have hmass : cellMass p f (f w) = cellMass p g (g w) := by
    unfold cellMass
    simp only [hfg]
  rw [hmass]

theorem finiteEntropy_eq_mapEntropyNats {n : ℕ} (P : FiniteLaw4 n)
    (S : Finset (Fin 4)) :
    finiteEntropy P S = mapEntropyNats P.mass (fun w => fun i : S => w i) / Real.log 2 := by
  classical
  have hm : ∀ y : S → Fin n, marginalMass P S y =
      cellMass P.mass (fun w => fun i : S => w i) y := by
    intro y
    unfold marginalMass cellMass
    apply sum_congr rfl
    intro w _
    by_cases h : (fun i : S => w i) = y <;> simp [h]
  simp only [finiteEntropy, mapEntropyNats, hm]

/-- The pointwise Gibbs inequality, valid also for zero p. -/
theorem weighted_log_ratio_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsupport : 0 < p → 0 < q) :
    p * Real.log (q / p) ≤ q - p := by
  by_cases hp0 : p = 0
  · simp [hp0, hq]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' := hsupport hp'
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq' hp')) hp
  have heq : p * (q / p - 1) = q - p := by field_simp
  simpa only [heq] using h

theorem finite_gibbs {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hsupport : ∀ a, 0 < p a → 0 < q a) :
    ∑ a, p a * Real.log (q a / p a) ≤ (∑ a, q a) - ∑ a, p a := by
  calc
    _ ≤ ∑ a, (q a - p a) := sum_le_sum (fun a _ => weighted_log_ratio_le (hp a) (hq a) (hsupport a))
    _ = _ := by rw [sum_sub_distrib]

theorem cellMass_pair_fst (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (a : α) :
    ∑ b, cellMass p (fun w => (f w, g w)) (a, b) = cellMass p f a := by
  classical
  unfold cellMass
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  by_cases h : f w = a
  · simp [Prod.mk.injEq, h, eq_comm]
  · simp [Prod.mk.injEq, h, Ne.symm h, eq_comm]

theorem cellMass_pair_snd (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (b : β) :
    ∑ a, cellMass p (fun w => (f w, g w)) (a, b) = cellMass p g b := by
  classical
  unfold cellMass
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  by_cases h : g w = b
  · simp [Prod.mk.injEq, h, eq_comm]
  · simp [Prod.mk.injEq, h, Ne.symm h, eq_comm]

end
end SharpStability
