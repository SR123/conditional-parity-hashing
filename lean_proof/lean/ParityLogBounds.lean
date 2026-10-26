import Mathlib

namespace ConditionalParityHashing
noncomputable section
open Finset

/-- A finite, kernel-checkable atanh-series enclosure for the natural logarithm. -/
theorem log_enclosure (x l u : ℝ) (hx : 1 ≤ x)
    (hl : l ≤ 2 * ∑ i ∈ range 20,
      ((x-1)/(x+1)) ^ (2*i+1) / (2*i+1))
    (hu : 2 * ((∑ i ∈ range 20,
      ((x-1)/(x+1)) ^ (2*i+1) / (2*i+1)) +
      ((x-1)/(x+1)) ^ 41 / (1-((x-1)/(x+1))^2)) ≤ u) :
    l ≤ Real.log x ∧ Real.log x ≤ u := by
  have hxpos : 0 < x := by linarith
  have hd : 0 < x+1 := by linarith
  have hy0 : 0 ≤ (x-1)/(x+1) := div_nonneg (by linarith) hd.le
  have hy1 : (x-1)/(x+1) < 1 := (div_lt_one hd).2 (by linarith)
  have hid : (1+(x-1)/(x+1))/(1-(x-1)/(x+1)) = x := by
    field_simp
    <;> ring
  have hlow := Real.sum_range_le_log_div hy0 hy1 20
  have hhigh := Real.log_div_le_sum_range_add hy0 hy1 20
  rw [hid] at hlow hhigh
  constructor <;> linarith

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem log_two_enclosure :
    (6931471805599453 : ℝ)/10000000000000000 ≤ Real.log 2 ∧
    Real.log 2 ≤ (6931471805599454 : ℝ)/10000000000000000 := by
  apply log_enclosure
  · norm_num
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

#print axioms log_enclosure
#print axioms log_two_enclosure
end
end ConditionalParityHashing
