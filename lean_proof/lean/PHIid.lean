import PHFiniteHash

/-!
# Independent blocks: product masses, entropy additivity and Chebyshev

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

For a finite probability mass `p₁` on `Ω₁`, `prodMass p₁ n` is the law of `n`
independent copies on `Fin n → Ω₁`.  We prove the coordinatewise expectation
formula, the product formula for cell masses, additivity of entropy, and a
Chebyshev bound for sums of coordinate functions.  These are the only
probabilistic facts used by the asymptotic hashing step.
-/

namespace ParityHashing

open Finset SharpStability

noncomputable section

variable {Ω₁ α : Type*} [Fintype Ω₁] [Fintype α]

/-- Product mass of `n` independent copies. -/
def prodMass (p₁ : Ω₁ → ℝ) (n : ℕ) (ω : Fin n → Ω₁) : ℝ := ∏ t, p₁ (ω t)

theorem prodMass_nonneg {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (n : ℕ) (ω : Fin n → Ω₁) :
    0 ≤ prodMass p₁ n ω :=
  Finset.prod_nonneg (fun t _ => hp (ω t))

/-- Sum over all words of a product of coordinate functions. -/
theorem sum_prod_coord (n : ℕ) (g : Fin n → Ω₁ → ℝ) :
    ∑ ω : Fin n → Ω₁, ∏ t, g t (ω t) = ∏ t, ∑ x, g t x := by
  classical
  have h := Finset.sum_prod_piFinset (ι := Fin n) (univ : Finset Ω₁) g
  rw [Fintype.piFinset_univ] at h
  exact h

/-- Expectation of a coordinatewise product under the product mass. -/
theorem expect_prod_coord (p₁ : Ω₁ → ℝ) (n : ℕ) (F : Fin n → Ω₁ → ℝ) :
    ∑ ω : Fin n → Ω₁, prodMass p₁ n ω * ∏ t, F t (ω t) = ∏ t, ∑ x, p₁ x * F t x := by
  rw [← sum_prod_coord n (fun t x => p₁ x * F t x)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [prodMass, ← Finset.prod_mul_distrib]

theorem prodMass_sum {p₁ : Ω₁ → ℝ} (hp1 : ∑ x, p₁ x = 1) (n : ℕ) :
    ∑ ω : Fin n → Ω₁, prodMass p₁ n ω = 1 := by
  have h := expect_prod_coord p₁ n (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at h
  rw [h, hp1, Finset.prod_const_one]

/-- One-coordinate expectation. -/
theorem expect_coord {p₁ : Ω₁ → ℝ} (hp1 : ∑ x, p₁ x = 1) (n : ℕ) (t₀ : Fin n)
    (G : Ω₁ → ℝ) :
    ∑ ω : Fin n → Ω₁, prodMass p₁ n ω * G (ω t₀) = ∑ x, p₁ x * G x := by
  classical
  have h := expect_prod_coord p₁ n (fun t x => if t = t₀ then G x else 1)
  have hl : ∀ ω : Fin n → Ω₁, ∏ t, (if t = t₀ then G (ω t) else 1) = G (ω t₀) := by
    intro ω
    rw [Finset.prod_ite_eq']
    simp
  simp only [hl] at h
  rw [h]
  have hr : ∀ t, ∑ x, p₁ x * (if t = t₀ then G x else 1) =
      if t = t₀ then ∑ x, p₁ x * G x else 1 := by
    intro t
    by_cases ht : t = t₀
    · simp [ht]
    · simp [ht, hp1]
  simp only [hr]
  rw [Finset.prod_ite_eq']
  simp

/-- Two distinct coordinates are independent. -/
theorem expect_two_coord {p₁ : Ω₁ → ℝ} (hp1 : ∑ x, p₁ x = 1) (n : ℕ) {t₀ s₀ : Fin n}
    (hts : t₀ ≠ s₀) (G H : Ω₁ → ℝ) :
    ∑ ω : Fin n → Ω₁, prodMass p₁ n ω * (G (ω t₀) * H (ω s₀)) =
      (∑ x, p₁ x * G x) * ∑ x, p₁ x * H x := by
  classical
  let F : Fin n → Ω₁ → ℝ := fun t x => if t = t₀ then G x else if t = s₀ then H x else 1
  have h := expect_prod_coord p₁ n F
  have hl : ∀ ω : Fin n → Ω₁, ∏ t, F t (ω t) = G (ω t₀) * H (ω s₀) := by
    intro ω
    rw [Fintype.prod_eq_mul t₀ s₀ hts]
    · simp [F, hts.symm]
    · intro x hx
      simp [F, hx.1, hx.2]
  simp only [hl] at h
  rw [h, Fintype.prod_eq_mul t₀ s₀ hts]
  · simp [F, hts.symm]
  · intro x hx
    simp [F, hx.1, hx.2, hp1]

/-- Second moment of a centred coordinate sum. -/
theorem expect_sq_sum_coord {p₁ : Ω₁ → ℝ} (hp1 : ∑ x, p₁ x = 1) (n : ℕ) (g : Ω₁ → ℝ)
    (hg : ∑ x, p₁ x * g x = 0) :
    ∑ ω : Fin n → Ω₁, prodMass p₁ n ω * (∑ t, g (ω t)) ^ 2 = n * ∑ x, p₁ x * g x ^ 2 := by
  classical
  have hexp : ∀ ω : Fin n → Ω₁, prodMass p₁ n ω * (∑ t, g (ω t)) ^ 2 =
      ∑ t, ∑ s, prodMass p₁ n ω * (g (ω t) * g (ω s)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  simp only [hexp]
  rw [Finset.sum_comm]
  have hinner : ∀ t : Fin n, ∑ ω : Fin n → Ω₁, ∑ s, prodMass p₁ n ω * (g (ω t) * g (ω s)) =
      ∑ x, p₁ x * g x ^ 2 := by
    intro t
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single t]
    · have := expect_coord hp1 n t (fun x => g x ^ 2)
      simp only [sq] at this ⊢
      exact this
    · intro s _ hst
      rw [expect_two_coord hp1 n (Ne.symm hst) g g, hg, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ t) h
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Chebyshev's inequality for centred coordinate sums. -/
theorem chebyshev_coord {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1) {n : ℕ}
    (hn : 0 < n) (g : Ω₁ → ℝ) (hg : ∑ x, p₁ x * g x = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∑ ω ∈ univ.filter (fun ω : Fin n → Ω₁ => ∑ t, g (ω t) ≤ -(n * δ)), prodMass p₁ n ω ≤
      (∑ x, p₁ x * g x ^ 2) / (n * δ ^ 2) := by
  classical
  have hnδ : 0 < (n : ℝ) * δ := mul_pos (by exact_mod_cast hn) hδ
  have hbound : ∀ ω ∈ univ.filter (fun ω : Fin n → Ω₁ => ∑ t, g (ω t) ≤ -(n * δ)),
      prodMass p₁ n ω ≤ prodMass p₁ n ω * (∑ t, g (ω t)) ^ 2 / ((n : ℝ) * δ) ^ 2 := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    have hsq : ((n : ℝ) * δ) ^ 2 ≤ (∑ t, g (ω t)) ^ 2 := by nlinarith
    have hm := prodMass_nonneg hp n ω
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc _ ≤ ∑ ω ∈ univ.filter (fun ω : Fin n → Ω₁ => ∑ t, g (ω t) ≤ -(n * δ)),
          prodMass p₁ n ω * (∑ t, g (ω t)) ^ 2 / ((n : ℝ) * δ) ^ 2 := Finset.sum_le_sum hbound
    _ ≤ ∑ ω : Fin n → Ω₁, prodMass p₁ n ω * (∑ t, g (ω t)) ^ 2 / ((n : ℝ) * δ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ω _ _
        exact div_nonneg (mul_nonneg (prodMass_nonneg hp n ω) (sq_nonneg _)) (sq_nonneg _)
    _ = (n * ∑ x, p₁ x * g x ^ 2) / ((n : ℝ) * δ) ^ 2 := by
        rw [← Finset.sum_div, expect_sq_sum_coord hp1 n g hg]
    _ = (∑ x, p₁ x * g x ^ 2) / (n * δ ^ 2) := by
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp

/-- Cell masses of coordinatewise maps factorise. -/
theorem cellMass_prod_coord (p₁ : Ω₁ → ℝ) (n : ℕ) (f : Ω₁ → α) (y : Fin n → α) :
    cellMass (prodMass p₁ n) (fun ω t => f (ω t)) y = ∏ t, cellMass p₁ f (y t) := by
  classical
  have hterm : ∀ ω : Fin n → Ω₁,
      (if (fun t => f (ω t)) = y then prodMass p₁ n ω else 0) =
        ∏ t, (if f (ω t) = y t then p₁ (ω t) else 0) := by
    intro ω
    by_cases h : ∀ t, f (ω t) = y t
    · have h' : (fun t => f (ω t)) = y := funext h
      rw [if_pos h', prodMass]
      apply Finset.prod_congr rfl
      intro t _
      rw [if_pos (h t)]
    · push Not at h
      obtain ⟨t, ht⟩ := h
      have h' : ¬ (fun t => f (ω t)) = y := fun h'' => ht (congrFun h'' t)
      rw [if_neg h']
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      rw [if_neg ht]
  simp_rw [cellMass_explicit]
  simp only [hterm]
  rw [sum_prod_coord n (fun t x => if f x = y t then p₁ x else 0)]

/-- Entropy is additive over independent blocks. -/
theorem mapEntropyNats_prod_coord {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
    (n : ℕ) (f : Ω₁ → α) :
    mapEntropyNats (prodMass p₁ n) (fun ω t => f (ω t)) = n * mapEntropyNats p₁ f := by
  classical
  rw [mapEntropyNats_atom, mapEntropyNats_atom]
  simp only [cellMass_prod_coord]
  have hterm : ∀ ω : Fin n → Ω₁,
      prodMass p₁ n ω * Real.log (∏ t, cellMass p₁ f (f (ω t))) =
        ∑ t, prodMass p₁ n ω * Real.log (cellMass p₁ f (f (ω t))) := by
    intro ω
    by_cases h0 : prodMass p₁ n ω = 0
    · simp [h0]
    · have hall : ∀ t, p₁ (ω t) ≠ 0 := by
        intro t ht
        apply h0
        exact Finset.prod_eq_zero (Finset.mem_univ t) ht
      rw [Real.log_prod]
      · rw [Finset.mul_sum]
      · intro t _
        have hpos : 0 < p₁ (ω t) := lt_of_le_of_ne (hp _) (Ne.symm (hall t))
        exact (hpos.trans_le (mass_le_cellMass hp f (ω t))).ne'
  simp only [hterm]
  rw [Finset.sum_comm]
  simp only [expect_coord hp1 n _ (fun x => Real.log (cellMass p₁ f (f x)))]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end
end ParityHashing
