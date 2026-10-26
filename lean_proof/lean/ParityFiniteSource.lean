import FiniteInformation
import Balanced
import Mathlib

namespace ConditionalParityHashing
noncomputable section
open Finset SharpStability

/-- The published MC source, with the fixed rational parameters of the paper. -/
def sourceAtoms : Fin 24 → Fin 4 → Fin 4 :=
  ![![0,0,0,0],
    ![0,2,1,0],
    ![0,0,1,1],
    ![0,1,0,1],
    ![0,3,2,1],
    ![0,1,2,0],
    ![1,0,1,0],
    ![1,1,0,0],
    ![1,0,0,2],
    ![1,2,1,2],
    ![1,3,3,2],
    ![1,2,3,0],
    ![2,1,2,1],
    ![2,0,0,1],
    ![2,1,0,3],
    ![2,3,2,3],
    ![2,2,3,3],
    ![2,3,3,1],
    ![3,2,3,2],
    ![3,0,1,2],
    ![3,2,1,3],
    ![3,3,3,3],
    ![3,1,2,3],
    ![3,3,2,2]]

def sourceWeights (a : Fin 24) : ℚ :=
  if a.val % 3 = 0 then 74830195 / 800000000
  else if a.val % 3 = 1 then 22122546 / 800000000
  else 3047259 / 800000000

theorem sourceWeights_nonneg (a : Fin 24) : 0 ≤ sourceWeights a := by
  unfold sourceWeights
  split_ifs <;> norm_num

theorem sourceWeights_sum : ∑ a, sourceWeights a = 1 := by
  norm_num [sourceWeights, Fin.sum_univ_succ]

def sourceLaw : FiniteLaw4 4 where
  mass w := ∑ a : Fin 24, if sourceAtoms a = w then (sourceWeights a : ℝ) else 0
  mass_nonneg w := by
    apply sum_nonneg
    intro a _
    split_ifs
    · exact_mod_cast sourceWeights_nonneg a
    · exact le_rfl
  mass_sum := by
    rw [sum_comm]
    have h : ∀ a : Fin 24, (∑ w : Word4 4,
        if sourceAtoms a = w then (sourceWeights a : ℝ) else 0) = sourceWeights a := by
      intro a
      simp [eq_comm]
    simp_rw [h]
    exact_mod_cast sourceWeights_sum

def chi (x : Fin 4) : Fin 2 := if x=1 ∨ x=2 then 1 else 0

theorem source_parity (a : Fin 24) :
    ((chi (sourceAtoms a 0)).val + (chi (sourceAtoms a 1)).val +
    (chi (sourceAtoms a 2)).val + (chi (sourceAtoms a 3)).val) % 2 = 0 := by
  fin_cases a <;> norm_num [sourceAtoms, chi]

/-- Rational marginal cells; exact equality tests contain no entropy approximation. -/
def sourceCell (i j : Fin 4) (x : Fin 4) (e : Fin 2) : ℚ :=
  ∑ a : Fin 24, if sourceAtoms a i = x ∧ chi (sourceAtoms a j) = e
    then sourceWeights a else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem source_partner_uniform :
    ∀ x : Fin 4, ∀ e : Fin 2,
      sourceCell 0 1 x e = 1/8 ∧ sourceCell 1 0 x e = 1/8 ∧
      sourceCell 2 3 x e = 1/8 ∧ sourceCell 3 2 x e = 1/8 := by
  intro x e
  fin_cases x <;> fin_cases e <;>
    norm_num [sourceCell, sourceAtoms, sourceWeights, chi, Fin.sum_univ_succ]

#print axioms sourceWeights_nonneg
#print axioms sourceWeights_sum
#print axioms sourceLaw
#print axioms source_parity
#print axioms source_partner_uniform
end
end ConditionalParityHashing
