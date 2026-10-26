import ParityLogBounds
namespace ConditionalParityHashing
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem log_P_enclosure :
    (-2899487059924979 : ℝ)/10000000000000000 ≤ Real.log ((14966039 : ℝ)/20000000) ∧
    Real.log ((14966039 : ℝ)/20000000) ≤ (-2899487059924974 : ℝ)/10000000000000000 := by
  have h := log_enclosure ((14966039 : ℝ)/10000000) ((4031984745674476 : ℝ)/10000000000000000) ((4031984745674477 : ℝ)/10000000000000000) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := log_two_enclosure
  have he : Real.log ((14966039 : ℝ)/10000000) = Real.log ((14966039 : ℝ)/20000000) + 1 * Real.log 2 := by
    have heq : ((14966039 : ℝ)/10000000) = ((14966039 : ℝ)/20000000) * (2:ℝ)^1 := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

#print axioms log_P_enclosure

theorem log_Q_enclosure :
    (-15085729164998876 : ℝ)/10000000000000000 ≤ Real.log ((11061273 : ℝ)/50000000) ∧
    Real.log ((11061273 : ℝ)/50000000) ≤ (-15085729164998867 : ℝ)/10000000000000000 := by
  have h := log_enclosure ((11061273 : ℝ)/6250000) ((5708686251799488 : ℝ)/10000000000000000) ((5708686251799489 : ℝ)/10000000000000000) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := log_two_enclosure
  have he : Real.log ((11061273 : ℝ)/6250000) = Real.log ((11061273 : ℝ)/50000000) + 3 * Real.log 2 := by
    have heq : ((11061273 : ℝ)/6250000) = ((11061273 : ℝ)/50000000) * (2:ℝ)^3 := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

#print axioms log_Q_enclosure

theorem log_T_enclosure :
    (-34909276879559966 : ℝ)/10000000000000000 ≤ Real.log ((3047259 : ℝ)/100000000) ∧
    Real.log ((3047259 : ℝ)/100000000) ≤ (-34909276879559951 : ℝ)/10000000000000000 := by
  have h := log_enclosure ((3047259 : ℝ)/1562500) ((6679553954036760 : ℝ)/10000000000000000) ((6679553954036761 : ℝ)/10000000000000000) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := log_two_enclosure
  have he : Real.log ((3047259 : ℝ)/1562500) = Real.log ((3047259 : ℝ)/100000000) + 6 * Real.log 2 := by
    have heq : ((3047259 : ℝ)/1562500) = ((3047259 : ℝ)/100000000) * (2:ℝ)^6 := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

#print axioms log_T_enclosure

theorem log_one_sub_P_enclosure :
    (-13795251241891138 : ℝ)/10000000000000000 ≤ Real.log ((5033961 : ℝ)/20000000) ∧
    Real.log ((5033961 : ℝ)/20000000) ≤ (-13795251241891131 : ℝ)/10000000000000000 := by
  have h := log_enclosure ((5033961 : ℝ)/5000000) ((67692369307771 : ℝ)/10000000000000000) ((67692369307772 : ℝ)/10000000000000000) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := log_two_enclosure
  have he : Real.log ((5033961 : ℝ)/5000000) = Real.log ((5033961 : ℝ)/20000000) + 2 * Real.log 2 := by
    have heq : ((5033961 : ℝ)/5000000) = ((5033961 : ℝ)/20000000) * (2:ℝ)^2 := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

#print axioms log_one_sub_P_enclosure

theorem log_one_sub_Q_enclosure :
    (-2500336973384450 : ℝ)/10000000000000000 ≤ Real.log ((38938727 : ℝ)/50000000) ∧
    Real.log ((38938727 : ℝ)/50000000) ≤ (-2500336973384445 : ℝ)/10000000000000000 := by
  have h := log_enclosure ((38938727 : ℝ)/25000000) ((4431134832215005 : ℝ)/10000000000000000) ((4431134832215006 : ℝ)/10000000000000000) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := log_two_enclosure
  have he : Real.log ((38938727 : ℝ)/25000000) = Real.log ((38938727 : ℝ)/50000000) + 1 * Real.log 2 := by
    have heq : ((38938727 : ℝ)/25000000) = ((38938727 : ℝ)/50000000) * (2:ℝ)^1 := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

#print axioms log_one_sub_Q_enclosure

theorem log_one_sub_T_enclosure :
    (-309465323937729 : ℝ)/10000000000000000 ≤ Real.log ((96952741 : ℝ)/100000000) ∧
    Real.log ((96952741 : ℝ)/100000000) ≤ (-309465323937724 : ℝ)/10000000000000000 := by
  have h := log_enclosure ((96952741 : ℝ)/50000000) ((6622006481661726 : ℝ)/10000000000000000) ((6622006481661727 : ℝ)/10000000000000000) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := log_two_enclosure
  have he : Real.log ((96952741 : ℝ)/50000000) = Real.log ((96952741 : ℝ)/100000000) + 1 * Real.log 2 := by
    have heq : ((96952741 : ℝ)/50000000) = ((96952741 : ℝ)/100000000) * (2:ℝ)^1 := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

#print axioms log_one_sub_T_enclosure

end
end ConditionalParityHashing
