import PHCone

/-!
# Conditional entropy profiles are almost entropic

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

`H(F | W) = ∑_w P(W = w) H(F | W = w)`, and each conditional law is a finite
probability space.  Encoding block values into a single finite alphabet turns
each conditional law into a `FiniteLaw4`, so the conditional profile is a
nonnegative combination of finite entropy tables and lies in the closure.
-/

namespace ParityHashing

open Finset SharpStability

noncomputable section

section Decomposition

variable {Ω α γ : Type*} [Fintype Ω] [Fintype α] [Fintype γ] [DecidableEq γ]

theorem cellMass_eq_sum_ite [DecidableEq α] (p : Ω → ℝ) (f : Ω → α) (a : α) :
    cellMass p f a = ∑ w, if f w = a then p w else 0 := by
  unfold cellMass
  apply Finset.sum_congr rfl
  intro w _
  congr 1

/-- Conditional mass given `W = w`; on null events it falls back to `p`. -/
def condMass (p : Ω → ℝ) (W : Ω → γ) (w : γ) (ω : Ω) : ℝ :=
  if 0 < cellMass p W w then (if W ω = w then p ω / cellMass p W w else 0) else p ω

theorem condMass_nonneg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (W : Ω → γ) (w : γ) (ω : Ω) :
    0 ≤ condMass p W w ω := by
  unfold condMass
  split_ifs with h1 h2
  · exact div_nonneg (hp ω) h1.le
  · exact le_rfl
  · exact hp ω

theorem condMass_sum {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (W : Ω → γ) (w : γ) :
    ∑ ω, condMass p W w ω = 1 := by
  unfold condMass
  by_cases h : 0 < cellMass p W w
  · simp only [h, if_true]
    have : ∑ ω, (if W ω = w then p ω / cellMass p W w else 0) =
        (∑ ω, if W ω = w then p ω else 0) / cellMass p W w := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp
    rw [this, ← cellMass_eq_sum_ite, div_self h.ne']
  · simp only [h, if_false]
    exact hp1

/-- Cell masses of the conditional law. -/
theorem cellMass_condMass {p : Ω → ℝ} (W : Ω → γ) (w : γ) (hw : 0 < cellMass p W w)
    (F : Ω → α) (a : α) :
    cellMass (condMass p W w) F a = cellMass p (fun ω => (F ω, W ω)) (a, w) / cellMass p W w := by
  classical
  rw [cellMass_eq_sum_ite, cellMass_eq_sum_ite, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  unfold condMass
  simp only [hw, if_true, Prod.mk.injEq]
  by_cases h1 : F ω = a <;> by_cases h2 : W ω = w <;> simp [h1, h2]

/-- **Decomposition of conditional entropy over the values of `W`.** -/
theorem condEnt_decomp {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (F : Ω → α) (W : Ω → γ) :
    condEnt p F W = ∑ w, cellMass p W w * mapEntropyNats (condMass p W w) F := by
  classical
  -- each term, written over atoms
  have hterm : ∀ w, cellMass p W w * mapEntropyNats (condMass p W w) F =
      -∑ ω, (if W ω = w then p ω * Real.log
        (cellMass p (fun v => (F v, W v)) (F ω, w) / cellMass p W w) else 0) := by
    intro w
    by_cases hw : 0 < cellMass p W w
    · rw [mapEntropyNats_atom, mul_neg, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      rw [cellMass_condMass W w hw]
      unfold condMass
      simp only [hw, if_true]
      split_ifs with h
      · field_simp
      · simp
    · have hzero : cellMass p W w = 0 :=
        le_antisymm (not_lt.1 hw) (cellMass_nonneg hp W w)
      have hpw : ∀ ω, W ω = w → p ω = 0 := by
        intro ω hω
        have := mass_le_cellMass hp W ω
        rw [hω, hzero] at this
        exact le_antisymm this (hp ω)
      rw [hzero, zero_mul]
      symm
      rw [neg_eq_zero]
      apply Finset.sum_eq_zero
      intro ω _
      split_ifs with h
      · rw [hpw ω h, zero_mul]
      · rfl
  simp only [hterm]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [condEnt_atom, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h0 : p ω = 0
  · simp [h0]
  · have hpos : 0 < p ω := lt_of_le_of_ne (hp ω) (Ne.symm h0)
    have hc1 : 0 < cellMass p W (W ω) := hpos.trans_le (mass_le_cellMass hp W ω)
    have hc2 : 0 < cellMass p (fun v => (F v, W v)) (F ω, W ω) :=
      hpos.trans_le (mass_le_cellMass hp (fun v => (F v, W v)) ω)
    rw [Real.log_div hc2.ne' hc1.ne']
    ring

end Decomposition

section BlockTables

variable {Ω₁ : Type*} [Fintype Ω₁] {m : ℕ}

/-- Encoded block coordinates, valued in a single finite alphabet. -/
def blockCode (X : Fin 4 → Ω₁ → Fin m) {n : ℕ} (i : Fin 4) (ω : Fin n → Ω₁) : Fin (m ^ n) :=
  finFunctionFinEquiv (fun t => X i (ω t))

/-- The conditional law of the encoded blocks given `W = w`, as a finite law. -/
def condLaw4 {γ : Type*} [Fintype γ] [DecidableEq γ] {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x)
    (hp1 : ∑ x, p₁ x = 1) (X : Fin 4 → Ω₁ → Fin m) {n : ℕ} (W : (Fin n → Ω₁) → γ) (w : γ) :
    FiniteLaw4 (m ^ n) :=
  pushLaw4 (condMass (prodMass p₁ n) W w) (condMass_nonneg (prodMass_nonneg hp n) W w)
    (condMass_sum (prodMass_sum hp1 n) W w) (fun i ω => blockCode X i ω)

theorem finiteEntropy_condLaw4 {γ : Type*} [Fintype γ] [DecidableEq γ] {p₁ : Ω₁ → ℝ}
    (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1) (X : Fin 4 → Ω₁ → Fin m) {n : ℕ}
    (W : (Fin n → Ω₁) → γ) (w : γ) (S : Finset (Fin 4)) :
    finiteEntropy (condLaw4 hp hp1 X W w) S * Real.log 2 =
      mapEntropyNats (condMass (prodMass p₁ n) W w) (blockSide X S) := by
  rw [condLaw4, finiteEntropy_pushLaw4]
  apply mapEntropyNats_same_fibers
  intro a b
  constructor
  · intro h
    funext t i
    have hS := fun i : S => congrFun h i
    simp only [blockSide, blockS, sideInfo]
    by_cases hi : i ∈ S
    · have h1 := hS ⟨i, hi⟩
      simp only [blockCode] at h1
      have h2 := congrFun (finFunctionFinEquiv.injective h1) t
      simp only [hi, if_true, h2]
    · simp [hi]
  · intro h
    funext i
    simp only [blockCode]
    congr 1
    funext t
    have h1 := congrFun (congrFun h t) i
    simp only [blockSide, blockS, sideInfo, i.2, if_true] at h1
    exact Option.some.inj h1

/-- The conditional block table in bits. -/
def condTable {γ : Type*} [Fintype γ] (p₁ : Ω₁ → ℝ) (X : Fin 4 → Ω₁ → Fin m) {n : ℕ}
    (W : (Fin n → Ω₁) → γ) : EntropyTable :=
  fun S => condEnt (prodMass p₁ n) (blockSide X S) W / Real.log 2

theorem condTable_eq_sum {γ : Type*} [Fintype γ] [DecidableEq γ] {p₁ : Ω₁ → ℝ}
    (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1) (X : Fin 4 → Ω₁ → Fin m) {n : ℕ}
    (W : (Fin n → Ω₁) → γ) :
    condTable p₁ X W =
      ∑ w, cellMass (prodMass p₁ n) W w • finiteEntropy (condLaw4 hp hp1 X W w) := by
  funext S
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  simp only [condTable, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [condEnt_decomp (prodMass_nonneg hp n), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  rw [← finiteEntropy_condLaw4 hp hp1 X W w S]
  field_simp

/-- **Conditional block tables are almost entropic.** -/
theorem condTable_mem_ae {γ : Type*} [Fintype γ] [DecidableEq γ] {p₁ : Ω₁ → ℝ}
    (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1) (X : Fin 4 → Ω₁ → Fin m) {n : ℕ}
    (W : (Fin n → Ω₁) → γ) : condTable p₁ X W ∈ aeTables := by
  rw [condTable_eq_sum hp hp1 X W]
  exact ae_sum _ _ _ (fun w _ => cellMass_nonneg (prodMass_nonneg hp n) W w)
    (fun w _ => subset_closure (pushLaw4_mem _ _ _ _))

end BlockTables

end
end ParityHashing
