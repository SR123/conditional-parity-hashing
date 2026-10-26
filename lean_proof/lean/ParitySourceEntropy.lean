import ParityFiniteSource
import ParityScore

namespace ConditionalParityHashing
noncomputable section
open Finset SharpStability

/-- Entropy transport from the 24 atoms to the four observed coordinates. -/
theorem sourceLaw_cell {α : Type*} [Fintype α] (f : Word4 4 → α) (y : α) :
    cellMass sourceLaw.mass f y =
      cellMass (fun a : Fin 24 => (sourceWeights a : ℝ)) (fun a => f (sourceAtoms a)) y := by
  classical
  unfold cellMass
  change (∑ w : Word4 4, if f w = y then
      (∑ a : Fin 24, if sourceAtoms a = w then (sourceWeights a : ℝ) else 0) else 0) = _
  have hexp : ∀ w : Word4 4,
      (if f w = y then (∑ a : Fin 24, if sourceAtoms a = w then (sourceWeights a : ℝ) else 0) else 0) =
      ∑ a : Fin 24, if sourceAtoms a = w then (if f w = y then (sourceWeights a : ℝ) else 0) else 0 := by
    intro w
    by_cases hf : f w = y <;> simp [hf]
  simp_rw [hexp]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp [eq_comm]

theorem sourceLaw_mapEntropy {α : Type*} [Fintype α] (f : Word4 4 → α) :
    mapEntropyNats sourceLaw.mass f =
      mapEntropyNats (fun a : Fin 24 => (sourceWeights a : ℝ)) (fun a => f (sourceAtoms a)) := by
  classical
  unfold mapEntropyNats
  simp_rw [sourceLaw_cell]

theorem source_entropy_atoms (S : Finset (Fin 4)) :
    finiteEntropy sourceLaw S = mapEntropyNats (fun a : Fin 24 => (sourceWeights a : ℝ))
      (fun a => fun i : S => sourceAtoms a i) / Real.log 2 := by
  rw [finiteEntropy_eq_mapEntropyNats, sourceLaw_mapEntropy]

#print axioms sourceLaw_cell
#print axioms sourceLaw_mapEntropy
#print axioms source_entropy_atoms
end
end ConditionalParityHashing
