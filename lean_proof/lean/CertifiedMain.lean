import PHSourceBridge
import ParityPaperCorrespondence

namespace ConditionalParityHashing
noncomputable section
open SharpStability Finset

/-- The complete main theorem, with the target conjunction exposed. -/
theorem certified_main :
  (∀ R : ℝ, 0 ≤ R → R ≤ criticalRate → shiftedProfile R ∈ almostEntropicProfiles) ∧
  0 < candidate univ ∧
  (-97387436923 : ℝ)/1000000000000 ≤ paperJ candidate / candidate univ ∧
  paperJ candidate / candidate univ ≤ (-97387436922 : ℝ)/1000000000000 ∧
  ∃ n : ℕ, ∃ law : FiniteLaw4 n,
    0 < finiteEntropy law univ ∧
    paperJ (finiteEntropy law) / finiteEntropy law univ < (-9738 : ℝ)/100000 :=
  full_parity_hashing_result

#print certified_main
#print axioms certified_main
end
end ConditionalParityHashing
