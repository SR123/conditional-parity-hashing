import ParitySourceCoordinates
import AlmostEntropicClosure

namespace ConditionalParityHashing
noncomputable section
open SharpStability Finset

def sourceProfile : EntropyTable := finiteEntropy sourceLaw

def parityRank (S : Finset (Fin 4)) : ℝ := min 3 S.card

def criticalRate : ℝ := sourceProfile univ - sourceProfile {0,1}

def shiftedProfile (R : ℝ) : EntropyTable :=
  fun S => sourceProfile S - R * parityRank S

def candidate : EntropyTable := shiftedProfile criticalRate

/-- The orientation used in the paper: the violated pair is C,D. -/
def paperJ (h : EntropyTable) : ℝ :=
  tableCMI h 2 3 0 + tableCMI h 2 3 1 + tableMI h 0 1 - tableMI h 2 3

theorem paperJ_rank : paperJ parityRank = 0 := by
  norm_num [paperJ, tableCMI, tableMI, parityRank]

theorem paperJ_shift (R : ℝ) : paperJ (shiftedProfile R) = paperJ sourceProfile := by
  norm_num [paperJ, tableCMI, tableMI, shiftedProfile, parityRank]
  ring

theorem univ_four : (univ : Finset (Fin 4)) = {0,1,2,3} := by decide

theorem criticalRate_formula :
    criticalRate = (sourceHNats - binaryNats Q) / Real.log 2 := by
  unfold criticalRate sourceProfile
  rw [univ_four, source_entropy_ABCD, source_entropy_AB]
  ring

theorem paperJ_source_formula : paperJ sourceProfile = scoreNumeratorNats / Real.log 2 := by
  unfold paperJ tableCMI tableMI sourceProfile
  have hAC : ({2,0} : Finset (Fin 4)) = {0,2} := by decide
  have hAD : ({3,0} : Finset (Fin 4)) = {0,3} := by decide
  have hBC : ({2,1} : Finset (Fin 4)) = {1,2} := by decide
  have hBD : ({3,1} : Finset (Fin 4)) = {1,3} := by decide
  have hACD : ({2,3,0} : Finset (Fin 4)) = {0,2,3} := by decide
  have hBCD : ({2,3,1} : Finset (Fin 4)) = {1,2,3} := by decide
  rw [hACD,hBCD,hAC,hAD,hBC,hBD, source_entropy_AC, source_entropy_AD,
    source_entropy_BC, source_entropy_BD, source_entropy_ACD, source_entropy_BCD,
    source_entropy_A, source_entropy_B, source_entropy_C, source_entropy_D,
    source_entropy_AB, source_entropy_CD]
  unfold scoreNumeratorNats
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  <;> ring

theorem candidate_total_formula : candidate univ = scoreDenominatorNats / Real.log 2 := by
  unfold candidate shiftedProfile
  rw [criticalRate_formula]
  have hR : parityRank univ = 3 := by norm_num [parityRank]
  rw [hR]
  unfold sourceProfile
  rw [univ_four, source_entropy_ABCD]
  unfold scoreDenominatorNats
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  <;> ring

theorem candidate_total_pos : 0 < candidate univ := by
  rw [candidate_total_formula]
  exact div_pos score_denominator_pos (Real.log_pos (by norm_num))

theorem candidate_score_formula : paperJ candidate / candidate univ = scoreFormula := by
  change paperJ (shiftedProfile criticalRate) / candidate univ = _
  rw [paperJ_shift, paperJ_source_formula, candidate_total_formula, score_nats_bits]

/-- An unconditional kernel certificate for the candidate's exact score.
This theorem by itself does not assert almost-entropic membership. -/
theorem candidate_score_interval :
    (-97387436923 : ℝ) / 1000000000000 ≤ paperJ candidate / candidate univ ∧
    paperJ candidate / candidate univ ≤ (-97387436922 : ℝ) / 1000000000000 := by
  rw [candidate_score_formula]
  exact score_interval

/-- The full target: the genuine closure, with an explicitly stated finite-law source.
This is a proposition specifying the remaining goal, not an assertion that it is proved. -/
def FullParityHashingResult : Prop :=
  (∀ R : ℝ, 0 ≤ R → R ≤ criticalRate → shiftedProfile R ∈ almostEntropicProfiles) ∧
  0 < candidate univ ∧
  (-97387436923 : ℝ)/1000000000000 ≤ paperJ candidate / candidate univ ∧
  paperJ candidate / candidate univ ≤ (-97387436922 : ℝ)/1000000000000 ∧
  ∃ n : ℕ, ∃ law : FiniteLaw4 n,
    0 < finiteEntropy law univ ∧
    paperJ (finiteEntropy law) / finiteEntropy law univ < (-9738 : ℝ)/100000

#print axioms candidate_score_interval
#print axioms candidate_total_pos
#print FullParityHashingResult
end
end ConditionalParityHashing
