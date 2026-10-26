import CertifiedMain
import SixThresholdCriterion

/-!
Research direction and outline: Søren Riis.
Audit-cycle semantic bridge: actual coordinatewise finite-law approximation
and the exact masses of the rational source. Original core files unchanged.
-/
namespace ConditionalParityHashing
open SharpStability Finset
noncomputable section

/-- The closure means simultaneous approximation of all entropy coordinates
by a genuine finite law, with the ordinary absolute value on real numbers. -/
theorem almostEntropic_iff_finite_coordinate_approx (h : EntropyTable) :
    h ∈ almostEntropicProfiles ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ P : FiniteLaw4 n,
        ∀ S : Finset (Fin 4), |finiteEntropy P S - h S| < ε := by
  change h ∈ closure finiteEntropyProfiles ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro hh ε hε
    obtain ⟨v, ⟨n, P, rfl⟩, hv⟩ := hh ε hε
    refine ⟨n, P, ?_⟩
    intro S
    have hs := (dist_pi_lt_iff hε).1 hv S
    simpa only [Real.dist_eq, abs_sub_comm] using hs
  · intro hh ε hε
    obtain ⟨n, P, hP⟩ := hh ε hε
    refine ⟨finiteEntropy P, ⟨n, P, rfl⟩, ?_⟩
    apply (dist_pi_lt_iff hε).2
    intro S
    simpa only [Real.dist_eq, abs_sub_comm] using hP S

/-- Each of the twenty-four displayed atoms has exactly its displayed mass. -/
theorem sourceLaw_mass_on_atoms (a : Fin 24) :
    sourceLaw.mass (sourceAtoms a) = (sourceWeights a : ℝ) := by
  classical
  change (∑ b : Fin 24, if sourceAtoms b = sourceAtoms a then (sourceWeights b : ℝ) else 0) = _
  simp only [atoms_injective.eq_iff]
  simp

/-- Every configuration outside the displayed table has mass zero. -/
theorem sourceLaw_zero_off_atoms (w : Word4 4)
    (hw : ∀ a : Fin 24, sourceAtoms a ≠ w) : sourceLaw.mass w = 0 := by
  classical
  change (∑ a : Fin 24, if sourceAtoms a = w then (sourceWeights a : ℝ) else 0) = 0
  simp only [hw, ite_false, sum_const_zero]

#print almostEntropic_iff_finite_coordinate_approx
#print sourceLaw_mass_on_atoms
#print sourceLaw_zero_off_atoms
#print axioms almostEntropic_iff_finite_coordinate_approx
#print axioms sourceLaw_mass_on_atoms
#print axioms sourceLaw_zero_off_atoms
end
end ConditionalParityHashing
