import ParityCandidate

namespace ConditionalParityHashing
noncomputable section
open SharpStability Set
open scoped Topology

theorem continuous_paperJ : Continuous paperJ := by
  unfold paperJ tableCMI tableMI
  fun_prop

/-- Density of finite laws gives the paper's finite-alphabet corollary,
provided the remaining almost-entropic membership theorem is established. -/
theorem finite_score_of_candidate_mem
    (hmem : candidate ∈ almostEntropicProfiles) :
    ∃ n : ℕ, ∃ law : FiniteLaw4 n,
      0 < finiteEntropy law Finset.univ ∧
      paperJ (finiteEntropy law) / finiteEntropy law Finset.univ < (-9738 : ℝ)/100000 := by
  let U : Set EntropyTable := {h | 0 < h Finset.univ ∧
    paperJ h < ((-9738 : ℝ)/100000) * h Finset.univ}
  have hN : Continuous (fun h : EntropyTable => h Finset.univ) := continuous_apply _
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const hN).inter
      (isOpen_lt continuous_paperJ (continuous_const.mul hN))
  have hpoint : candidate ∈ U := by
    refine ⟨candidate_total_pos, ?_⟩
    apply (div_lt_iff₀ candidate_total_pos).1
    rw [candidate_score_formula]
    exact score_below_threshold
  change candidate ∈ closure finiteEntropyProfiles at hmem
  obtain ⟨h,hhU,hhF⟩ := (mem_closure_iff.mp hmem) U hopen hpoint
  obtain ⟨n,law,rfl⟩ := hhF
  exact ⟨n,law,hhU.1,(div_lt_iff₀ hhU.1).2 hhU.2⟩

#print axioms continuous_paperJ
#print axioms finite_score_of_candidate_mem
end
end ConditionalParityHashing
