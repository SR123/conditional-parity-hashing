import ParityConcreteLogs

namespace ConditionalParityHashing
noncomputable section

def P : ℝ := 74830195 / 100000000
def Q : ℝ := 22122546 / 100000000
def T : ℝ := 3047259 / 100000000

def binaryNats (p : ℝ) : ℝ := -p * Real.log p - (1-p) * Real.log (1-p)
def sourceHNats : ℝ := -P * Real.log P - Q * Real.log Q - T * Real.log T

def scoreNumeratorNats : ℝ :=
  (2-2*P) * Real.log 2 + 2 * binaryNats P + binaryNats T -
  2 * sourceHNats - binaryNats Q

def scoreDenominatorNats : ℝ :=
  3 * Real.log 2 - 2 * sourceHNats + 3 * binaryNats Q

def scoreFormula : ℝ := scoreNumeratorNats / scoreDenominatorNats

theorem score_denominator_pos : 0 < scoreDenominatorNats := by
  obtain ⟨hpL,hpU⟩ := log_P_enclosure
  obtain ⟨hqL,hqU⟩ := log_Q_enclosure
  obtain ⟨htL,htU⟩ := log_T_enclosure
  obtain ⟨hp1L,hp1U⟩ := log_one_sub_P_enclosure
  obtain ⟨hq1L,hq1U⟩ := log_one_sub_Q_enclosure
  obtain ⟨ht1L,ht1U⟩ := log_one_sub_T_enclosure
  obtain ⟨h2L,h2U⟩ := log_two_enclosure
  norm_num [scoreDenominatorNats, sourceHNats, binaryNats, P,Q,T] at *
  linarith

/-- The exact decimal interval printed in the manuscript, not a floating-point check. -/
theorem score_interval :
    (-97387436923 : ℝ) / 1000000000000 ≤ scoreFormula ∧
    scoreFormula ≤ (-97387436922 : ℝ) / 1000000000000 := by
  have hd := score_denominator_pos
  obtain ⟨hpL,hpU⟩ := log_P_enclosure
  obtain ⟨hqL,hqU⟩ := log_Q_enclosure
  obtain ⟨htL,htU⟩ := log_T_enclosure
  obtain ⟨hp1L,hp1U⟩ := log_one_sub_P_enclosure
  obtain ⟨hq1L,hq1U⟩ := log_one_sub_Q_enclosure
  obtain ⟨ht1L,ht1U⟩ := log_one_sub_T_enclosure
  obtain ⟨h2L,h2U⟩ := log_two_enclosure
  unfold scoreFormula
  constructor
  · apply (le_div_iff₀ hd).2
    norm_num [scoreNumeratorNats, scoreDenominatorNats, sourceHNats, binaryNats, P,Q,T] at *
    linarith
  · apply (div_le_iff₀ hd).2
    norm_num [scoreNumeratorNats, scoreDenominatorNats, sourceHNats, binaryNats, P,Q,T] at *
    linarith

theorem score_below_threshold : scoreFormula < (-9738 : ℝ)/100000 := by
  have h := score_interval.2
  linarith

/-- Cancellation of the change from nats to bits in the manuscript's score. -/
theorem score_nats_bits :
    (scoreNumeratorNats / Real.log 2) / (scoreDenominatorNats / Real.log 2) =
      scoreFormula := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp [scoreFormula, div_div_div_cancel_right₀ h2]

#print axioms score_denominator_pos
#print axioms score_interval
#print axioms score_below_threshold
#print axioms score_nats_bits
end
end ConditionalParityHashing
