import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
Concrete finite probability and Shannon entropy definitions for the intended target.
This module does not assert the Gaussian realization or the stability theorem.
-/

namespace SharpStability

abbrev Word4 (n : ℕ) := Fin 4 → Fin n

structure FiniteLaw4 (n : ℕ) where
  mass : Word4 n → ℝ
  mass_nonneg : ∀ w, 0 ≤ mass w
  mass_sum : ∑ w, mass w = 1

noncomputable def marginalMass {n : ℕ} (P : FiniteLaw4 n)
    (S : Finset (Fin 4)) (y : S → Fin n) : ℝ := by
  classical
  exact ∑ w : Word4 n, if (fun i : S => w i) = y then P.mass w else 0

theorem marginalMass_nonneg {n : ℕ} (P : FiniteLaw4 n)
    (S : Finset (Fin 4)) (y : S → Fin n) : 0 ≤ marginalMass P S y := by
  classical
  unfold marginalMass
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact P.mass_nonneg w
  · exact le_refl 0

theorem marginalMass_sum {n : ℕ} (P : FiniteLaw4 n)
    (S : Finset (Fin 4)) : ∑ y : S → Fin n, marginalMass P S y = 1 := by
  classical
  unfold marginalMass
  rw [Finset.sum_comm]
  simpa using P.mass_sum

/-- Shannon entropy in bits, with `Real.log 0 = 0` handling zero masses. -/
noncomputable def finiteEntropy {n : ℕ} (P : FiniteLaw4 n)
    (S : Finset (Fin 4)) : ℝ :=
  -(∑ y : S → Fin n, marginalMass P S y * Real.log (marginalMass P S y)) /
    Real.log 2

noncomputable def finiteMI {n : ℕ} (P : FiniteLaw4 n) (i j : Fin 4) : ℝ :=
  finiteEntropy P {i} + finiteEntropy P {j} - finiteEntropy P {i, j}

noncomputable def finiteCMI {n : ℕ} (P : FiniteLaw4 n)
    (i j k : Fin 4) : ℝ :=
  finiteEntropy P {i, k} + finiteEntropy P {j, k} -
    finiteEntropy P {k} - finiteEntropy P {i, j, k}

noncomputable def finiteU {n : ℕ} (P : FiniteLaw4 n) : ℝ := finiteMI P 0 1
noncomputable def finiteR {n : ℕ} (P : FiniteLaw4 n) : ℝ :=
  finiteCMI P 0 2 1 + finiteCMI P 1 2 0
noncomputable def finiteJ {n : ℕ} (P : FiniteLaw4 n) : ℝ :=
  finiteCMI P 0 1 2 + finiteCMI P 0 1 3 + finiteMI P 2 3 - finiteMI P 0 1

#print axioms marginalMass_nonneg
#print axioms marginalMass_sum

end SharpStability
