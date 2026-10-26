import ParityClosureConsequences

namespace ConditionalParityHashing
noncomputable section
open SharpStability Set Filter
open scoped Topology

theorem criticalRate_pos : 0 < criticalRate := by
  rw [criticalRate_formula]
  apply div_pos _ (Real.log_pos (by norm_num))
  obtain ⟨hpL,hpU⟩ := log_P_enclosure
  obtain ⟨hqL,hqU⟩ := log_Q_enclosure
  obtain ⟨htL,htU⟩ := log_T_enclosure
  obtain ⟨hq1L,hq1U⟩ := log_one_sub_Q_enclosure
  norm_num [sourceHNats,binaryNats,P,Q,T] at *
  linarith

theorem criticalRate_lt_one : criticalRate < 1 := by
  rw [criticalRate_formula]
  apply (div_lt_one (Real.log_pos (by norm_num))).2
  obtain ⟨hpL,hpU⟩ := log_P_enclosure
  obtain ⟨hqL,hqU⟩ := log_Q_enclosure
  obtain ⟨htL,htU⟩ := log_T_enclosure
  obtain ⟨hq1L,hq1U⟩ := log_one_sub_Q_enclosure
  obtain ⟨h2L,h2U⟩ := log_two_enclosure
  norm_num [sourceHNats,binaryNats,P,Q,T] at *
  linarith

theorem shiftedProfile_continuous : Continuous shiftedProfile := by
  unfold shiftedProfile
  fun_prop

/-- The critical rate is handled by closedness, not by a hashing claim at equality. -/
theorem candidate_mem_of_strict_rates
    (hstrict : ∀ R : ℝ, 0 < R → R < criticalRate →
      shiftedProfile R ∈ almostEntropicProfiles) :
    candidate ∈ almostEntropicProfiles := by
  have hclosed : IsClosed almostEntropicProfiles := isClosed_closure
  have hsegment : Set.Ioo 0 criticalRate ⊆
      shiftedProfile ⁻¹' almostEntropicProfiles := by
    intro R hR
    exact hstrict R hR.1 hR.2
  have hlimit : criticalRate ∈ closure (Set.Ioo 0 criticalRate) := by
    rw [closure_Ioo (ne_of_lt criticalRate_pos)]
    exact ⟨criticalRate_pos.le,le_rfl⟩
  exact (closure_minimal hsegment (hclosed.preimage shiftedProfile_continuous)) hlimit

/-- An honest assembly theorem: the strict-rate membership proof is still an input. -/
theorem full_result_of_strict_rates
    (hstrict : ∀ R : ℝ, 0 < R → R < criticalRate →
      shiftedProfile R ∈ almostEntropicProfiles) : FullParityHashingResult := by
  have hc := candidate_mem_of_strict_rates hstrict
  refine ⟨?_, candidate_total_pos, candidate_score_interval.1,
    candidate_score_interval.2, finite_score_of_candidate_mem hc⟩
  intro R hR hRb
  by_cases hzero : R = 0
  · subst R
    have heq : shiftedProfile 0 = finiteEntropy sourceLaw := by
      ext S
      simp [shiftedProfile,sourceProfile]
    rw [heq]
    exact finite_profile_almost sourceLaw
  by_cases heq : R = criticalRate
  · subst R
    exact hc
  exact hstrict R (lt_of_le_of_ne hR (Ne.symm hzero)) (lt_of_le_of_ne hRb heq)

#print axioms criticalRate_pos
#print axioms criticalRate_lt_one
#print axioms candidate_mem_of_strict_rates
#print axioms full_result_of_strict_rates
end
end ConditionalParityHashing
