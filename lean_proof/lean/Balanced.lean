import FiniteLaw
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace SharpStability

abbrev EntropyTable := Finset (Fin 4) → ℝ

def tableMI (h : EntropyTable) (i j : Fin 4) : ℝ :=
  h {i} + h {j} - h {i, j}
def tableCMI (h : EntropyTable) (i j k : Fin 4) : ℝ :=
  h {i, k} + h {j, k} - h {k} - h {i, j, k}
def tableU (h : EntropyTable) : ℝ := tableMI h 0 1
def tableR (h : EntropyTable) : ℝ := tableCMI h 0 2 1 + tableCMI h 1 2 0
def tableJ (h : EntropyTable) : ℝ :=
  tableCMI h 0 1 2 + tableCMI h 0 1 3 + tableMI h 2 3 - tableMI h 0 1

def quantizationShift (h : EntropyTable) (q : ℝ) : EntropyTable :=
  fun S => h S + (S.card : ℝ) * q

theorem finiteU_as_table {n : ℕ} (P : FiniteLaw4 n) :
    finiteU P = tableU (finiteEntropy P) := rfl
theorem finiteR_as_table {n : ℕ} (P : FiniteLaw4 n) :
    finiteR P = tableR (finiteEntropy P) := rfl
theorem finiteJ_as_table {n : ℕ} (P : FiniteLaw4 n) :
    finiteJ P = tableJ (finiteEntropy P) := rfl

theorem balancedU (h : EntropyTable) (q : ℝ) :
    tableU (quantizationShift h q) = tableU h := by
  norm_num [tableU, tableMI, quantizationShift]
  ring

theorem balancedR (h : EntropyTable) (q : ℝ) :
    tableR (quantizationShift h q) = tableR h := by
  norm_num [tableR, tableCMI, quantizationShift]
  ring

theorem balancedJ (h : EntropyTable) (q : ℝ) :
    tableJ (quantizationShift h q) = tableJ h := by
  norm_num [tableJ, tableMI, tableCMI, quantizationShift]
  ring

#print axioms finiteU_as_table
#print axioms finiteR_as_table
#print axioms finiteJ_as_table
#print axioms balancedU
#print axioms balancedR
#print axioms balancedJ

end SharpStability
