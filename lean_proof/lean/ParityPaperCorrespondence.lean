import ParityEndpoint

namespace ConditionalParityHashing
noncomputable section
open SharpStability Finset

/-- The critical rate defined from tightness equals I(C;D | AB), in bits. -/
theorem criticalRate_is_CMI :
    criticalRate = sourceProfile {0,1,2} + sourceProfile {0,1,3} -
      sourceProfile {0,1} - sourceProfile univ := by
  unfold criticalRate sourceProfile
  rw [univ_four, source_entropy_ABC, source_entropy_ABD, source_entropy_ABCD]
  ring

/-- The rank function subtracted in the paper is U_(3,4), in bit units. -/
theorem parityRank_is_U34 (S : Finset (Fin 4)) :
    parityRank S = ((min 3 S.card : ℕ) : ℝ) := by
  simp only [parityRank, Nat.cast_min, Nat.cast_ofNat]

/-- The printed eight-decimal value is the correctly rounded candidate score. -/
theorem candidate_eight_decimal_rounding :
    |paperJ candidate / candidate univ - (-9738744 : ℝ)/100000000| <
      (5 : ℝ)/1000000000 := by
  have h := candidate_score_interval
  rw [abs_lt]
  constructor <;> linarith [h.1,h.2]

#print axioms criticalRate_is_CMI
#print axioms parityRank_is_U34
#print axioms candidate_eight_decimal_rounding
end
end ConditionalParityHashing
