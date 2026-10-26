import PHMain

/-!
Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

Six full-pair thresholds imply the four singleton partner thresholds in
the existing generic parity-subtraction theorem. No uniformity is needed.
This file is an audit-cycle extension; the circulated sources are unchanged.
-/
namespace ParityHashing
open Finset SharpStability
noncomputable section

variable {Ω : Type*} {m : ℕ}

theorem sideInfo_single_label (X : Fin 4 → Ω → Fin m)
    (π : Fin 4 → Fin m → ZMod 2) {S : Finset (Fin 4)} {i : Fin 4}
    (hi : i ∈ S) {a b : Ω} (h : sideInfo X S a = sideInfo X S b) :
    parity X π i a = parity X π i b := by
  have h' : some (X i a) = some (X i b) := by
    simpa only [sideInfo, hi, ite_true] using congrFun h i
  exact congrArg (π i) (Option.some.inj h')

theorem sideInfo_coarsen (X : Fin 4 → Ω → Fin m)
    {S T : Finset (Fin 4)} (hST : S ⊆ T) {a b : Ω}
    (h : sideInfo X T a = sideInfo X T b) : sideInfo X S a = sideInfo X S b := by
  funext i
  by_cases hi : i ∈ S
  · have hT := hST hi
    have h' : some (X i a) = some (X i b) := by
      simpa only [sideInfo, hT, ite_true] using congrFun h i
    simpa only [sideInfo, hi, ite_true] using h'
  · simp only [sideInfo, hi, ite_false]

variable [Fintype Ω]

theorem partner_C_given_AC (p : Ω → ℝ) (X : Fin 4 → Ω → Fin m)
    (π : Fin 4 → Fin m → ZMod 2)
    (hx : ∀ a, parity X π 0 a + parity X π 1 a + parity X π 2 a + parity X π 3 a = 0) :
    condEnt p (parity X π 3) (sideInfo X {0,2}) =
    condEnt p (parity X π 1) (sideInfo X {0,2}) := by
  apply condEnt_congr_left
  intro a b h
  have h0 := sideInfo_single_label X π (by decide : (0 : Fin 4) ∈ ({0,2} : Finset (Fin 4))) h
  have h2 := sideInfo_single_label X π (by decide : (2 : Fin 4) ∈ ({0,2} : Finset (Fin 4))) h
  have ha := hx a
  have hb := hx b
  constructor <;> intro hh <;> linear_combination ha - hb - h0 - h2 - hh

theorem partner_D_given_BD (p : Ω → ℝ) (X : Fin 4 → Ω → Fin m)
    (π : Fin 4 → Fin m → ZMod 2)
    (hx : ∀ a, parity X π 0 a + parity X π 1 a + parity X π 2 a + parity X π 3 a = 0) :
    condEnt p (parity X π 2) (sideInfo X {1,3}) =
    condEnt p (parity X π 0) (sideInfo X {1,3}) := by
  apply condEnt_congr_left
  intro a b h
  have h1 := sideInfo_single_label X π (by decide : (1 : Fin 4) ∈ ({1,3} : Finset (Fin 4))) h
  have h3 := sideInfo_single_label X π (by decide : (3 : Fin 4) ∈ ({1,3} : Finset (Fin 4))) h
  have ha := hx a
  have hb := hx b
  constructor <;> intro hh <;> linear_combination ha - hb - h1 - h3 - hh

theorem six_thresholds_imply_ten {p : Ω → ℝ} (hp : ∀ a, 0 ≤ p a)
    (X : Fin 4 → Ω → Fin m) (π : Fin 4 → Fin m → ZMod 2)
    (hx : ∀ a, parity X π 0 a + parity X π 1 a + parity X π 2 a + parity X π 3 a = 0)
    {c : ℝ} (hc : ∀ j : Fin 10, j.val < 6 →
      c * Real.log 2 ≤ condEnt p (pairZ X π j) (pairS X j)) :
    ∀ j : Fin 10, c * Real.log 2 ≤ condEnt p (pairZ X π j) (pairS X j) := by
  intro j
  fin_cases j
  · exact hc 0 (by decide)
  · exact hc 1 (by decide)
  · exact hc 2 (by decide)
  · exact hc 3 (by decide)
  · exact hc 4 (by decide)
  · exact hc 5 (by decide)
  · have h := hc 1 (by decide)
    change c * Real.log 2 ≤ condEnt p (parity X π 1) (sideInfo X {0,2}) at h
    change c * Real.log 2 ≤ condEnt p (parity X π 1) (sideInfo X {0})
    exact h.trans (condEnt_mono_of_determined p hp _ _ _
      (fun a b hab => sideInfo_coarsen X (by decide : ({0} : Finset (Fin 4)) ⊆ {0,2}) hab))
  · have h := hc 3 (by decide)
    change c * Real.log 2 ≤ condEnt p (parity X π 0) (sideInfo X {1,2}) at h
    change c * Real.log 2 ≤ condEnt p (parity X π 0) (sideInfo X {1})
    exact h.trans (condEnt_mono_of_determined p hp _ _ _
      (fun a b hab => sideInfo_coarsen X (by decide : ({1} : Finset (Fin 4)) ⊆ {1,2}) hab))
  · have h := hc 1 (by decide)
    change c * Real.log 2 ≤ condEnt p (parity X π 1) (sideInfo X {0,2}) at h
    rw [← partner_C_given_AC p X π hx] at h
    change c * Real.log 2 ≤ condEnt p (parity X π 3) (sideInfo X {2})
    exact h.trans (condEnt_mono_of_determined p hp _ _ _
      (fun a b hab => sideInfo_coarsen X (by decide : ({2} : Finset (Fin 4)) ⊆ {0,2}) hab))
  · have h := hc 4 (by decide)
    change c * Real.log 2 ≤ condEnt p (parity X π 0) (sideInfo X {1,3}) at h
    rw [← partner_D_given_BD p X π hx] at h
    change c * Real.log 2 ≤ condEnt p (parity X π 2) (sideInfo X {3})
    exact h.trans (condEnt_mono_of_determined p hp _ _ _
      (fun a b hab => sideInfo_coarsen X (by decide : ({3} : Finset (Fin 4)) ⊆ {1,3}) hab))

theorem parity_hashing_six_conditions {p : Ω → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (X : Fin 4 → Ω → Fin m)
    (π : Fin 4 → Fin m → ZMod 2)
    (hx : ∀ a, parity X π 0 a + parity X π 1 a + parity X π 2 a + parity X π 3 a = 0)
    {c : ℝ} (hc : ∀ j : Fin 10, j.val < 6 →
      c * Real.log 2 ≤ condEnt p (pairZ X π j) (pairS X j))
    {R : ℝ} (hR : 0 ≤ R) (hRc : R ≤ c) :
    sourceTable p X - R • u34 ∈ aeTables :=
  parity_hashing_mem_ae hp hp1 X π hx (six_thresholds_imply_ten hp X π hx hc) hR hRc

#print parity_hashing_six_conditions
#print axioms sideInfo_single_label
#print axioms sideInfo_coarsen
#print axioms partner_C_given_AC
#print axioms partner_D_given_BD
#print axioms six_thresholds_imply_ten
#print axioms parity_hashing_six_conditions
end
end ParityHashing
