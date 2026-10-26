import ParitySourceEntropy

namespace ConditionalParityHashing
noncomputable section
open Finset SharpStability

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem log_quarter : Real.log (1/4 : ℝ) = -2 * Real.log 2 := by
  have h : (1/4 : ℝ) = ((2:ℝ)^2)⁻¹ := by norm_num
  rw [h, Real.log_inv, Real.log_pow]
  ring

theorem log_eighth : Real.log (1/8 : ℝ) = -3 * Real.log 2 := by
  have h : (1/8 : ℝ) = ((2:ℝ)^3)⁻¹ := by norm_num
  rw [h, Real.log_inv, Real.log_pow]
  ring

theorem log_mass_P_2 : Real.log ((14966039:ℝ)/80000000) = Real.log ((14966039:ℝ)/20000000) - 2 * Real.log 2 := by
  have he : ((14966039:ℝ)/80000000) = ((14966039:ℝ)/20000000) / (2:ℝ)^2 := by norm_num
  rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem log_mass_P_3 : Real.log ((14966039:ℝ)/160000000) = Real.log ((14966039:ℝ)/20000000) - 3 * Real.log 2 := by
  have he : ((14966039:ℝ)/160000000) = ((14966039:ℝ)/20000000) / (2:ℝ)^3 := by norm_num
  rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem log_mass_Q_3 : Real.log ((11061273:ℝ)/400000000) = Real.log ((11061273:ℝ)/50000000) - 3 * Real.log 2 := by
  have he : ((11061273:ℝ)/400000000) = ((11061273:ℝ)/50000000) / (2:ℝ)^3 := by norm_num
  rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem log_mass_T_3 : Real.log ((3047259:ℝ)/800000000) = Real.log ((3047259:ℝ)/100000000) - 3 * Real.log 2 := by
  have he : ((3047259:ℝ)/800000000) = ((3047259:ℝ)/100000000) / (2:ℝ)^3 := by norm_num
  rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem log_mass_one_sub_P_3 : Real.log ((5033961:ℝ)/160000000) = Real.log ((5033961:ℝ)/20000000) - 3 * Real.log 2 := by
  have he : ((5033961:ℝ)/160000000) = ((5033961:ℝ)/20000000) / (2:ℝ)^3 := by norm_num
  rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem log_mass_one_sub_Q_3 : Real.log ((38938727:ℝ)/400000000) = Real.log ((38938727:ℝ)/50000000) - 3 * Real.log 2 := by
  have he : ((38938727:ℝ)/400000000) = ((38938727:ℝ)/50000000) / (2:ℝ)^3 := by norm_num
  rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem log_mass_one_sub_T_3 : Real.log ((96952741:ℝ)/800000000) = Real.log ((96952741:ℝ)/100000000) - 3 * Real.log 2 := by
  have he : ((96952741:ℝ)/800000000) = ((96952741:ℝ)/100000000) / (2:ℝ)^3 := by norm_num
  rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem source_entropy_empty : finiteEntropy sourceLaw ∅ = 0 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]

#print axioms source_entropy_empty

theorem source_entropy_A : finiteEntropy sourceLaw {0} = 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_quarter]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_A

theorem source_entropy_B : finiteEntropy sourceLaw {1} = 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_quarter]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_B

theorem source_entropy_AB : finiteEntropy sourceLaw {0,1} = 3 + binaryNats Q / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_Q_3, log_mass_one_sub_Q_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_AB

theorem source_entropy_C : finiteEntropy sourceLaw {2} = 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_quarter]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_C

theorem source_entropy_AC : finiteEntropy sourceLaw {0,2} = 3 - P + binaryNats P / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_P_2, log_mass_one_sub_P_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_AC

theorem source_entropy_BC : finiteEntropy sourceLaw {1,2} = 3 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_eighth]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_BC

theorem source_entropy_ABC : finiteEntropy sourceLaw {0,1,2} = 3 + sourceHNats / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_P_3, log_mass_Q_3, log_mass_T_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_ABC

theorem source_entropy_D : finiteEntropy sourceLaw {3} = 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_quarter]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_D

theorem source_entropy_AD : finiteEntropy sourceLaw {0,3} = 3 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_eighth]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_AD

theorem source_entropy_BD : finiteEntropy sourceLaw {1,3} = 3 - P + binaryNats P / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_P_2, log_mass_one_sub_P_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_BD

theorem source_entropy_ABD : finiteEntropy sourceLaw {0,1,3} = 3 + sourceHNats / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_P_3, log_mass_Q_3, log_mass_T_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_ABD

theorem source_entropy_CD : finiteEntropy sourceLaw {2,3} = 3 + binaryNats T / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_T_3, log_mass_one_sub_T_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_CD

theorem source_entropy_ACD : finiteEntropy sourceLaw {0,2,3} = 3 + sourceHNats / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_P_3, log_mass_Q_3, log_mass_T_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_ACD

theorem source_entropy_BCD : finiteEntropy sourceLaw {1,2,3} = 3 + sourceHNats / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_P_3, log_mass_Q_3, log_mass_T_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_BCD

theorem source_entropy_ABCD : finiteEntropy sourceLaw {0,1,2,3} = 3 + sourceHNats / Real.log 2 := by
  rw [source_entropy_atoms, mapEntropyNats_atom]
  norm_num [cellMass, sourceAtoms, sourceWeights, Fin.sum_univ_succ,
    funext_iff, Subtype.forall, Fin.forall_fin_succ, sourceHNats, binaryNats, P,Q,T]
  simp only [log_mass_P_3, log_mass_Q_3, log_mass_T_3]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

#print axioms source_entropy_ABCD

end
end ConditionalParityHashing
