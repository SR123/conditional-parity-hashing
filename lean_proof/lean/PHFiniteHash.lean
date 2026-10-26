import PHCollision
import FiniteShannon

/-!
# A finite, non-asymptotic linear hashing inequality

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

Let `p` be a finite probability mass on `Ω`, let `Z : Ω → 𝔽₂ⁿ` be a source and
`S : Ω → β` side information.  Fix a threshold `c > 0` and call `w` typical if
`p w > 0` and `P(Z = Z w, S = S w) ≤ c · P(S = S w)`, i.e. the conditional
probability of `Z w` given `S w` is at most `c`.  If `A` is the typical mass then,
averaged over all binary `k × n` matrices `M`,

  `avg_M H(M Z | S) ≥ A · k log 2 - 2^k c`      (natural logarithms).

Equivalently the average entropy deficit `k log 2 - H(MZ | S)` is at most
`(1 - A) k log 2 + 2^k c`.  The proof uses only the exact collision count of
`PHCollision`, the elementary inequality `log x ≤ x - 1` (Jensen), and the
atom form of entropy from the reference library.  No smoothing lemma, Fano
inequality or continuity estimate is required.
-/

namespace ParityHashing

open Finset SharpStability

noncomputable section

variable {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]

/-- Conditional entropy `H(f | g)` in nats. -/
def condEnt (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) : ℝ :=
  mapEntropyNats p (fun w => (f w, g w)) - mapEntropyNats p g

theorem cellMass_explicit [DecidableEq α] (p : Ω → ℝ) (f : Ω → α) (a : α) :
    cellMass p f a = ∑ w, if f w = a then p w else 0 := by
  classical
  unfold cellMass
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : f w = a <;> simp [h]

/-- Jensen's inequality for the logarithm, from `log x ≤ x - 1`. -/
theorem jensen_log {ι : Type*} (s : Finset ι) (wt x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ wt i) (hw1 : ∑ i ∈ s, wt i = 1) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, wt i * Real.log (x i) ≤ Real.log (∑ i ∈ s, wt i * x i) ∧
      0 < ∑ i ∈ s, wt i * x i := by
  set m := ∑ i ∈ s, wt i * x i with hm_def
  have hm : 0 < m := by
    obtain ⟨j, hj, hwj⟩ : ∃ j ∈ s, 0 < wt j := by
      by_contra h
      push Not at h
      have : ∑ i ∈ s, wt i ≤ 0 := Finset.sum_nonpos h
      linarith
    have hle := Finset.single_le_sum (f := fun i => wt i * x i)
      (fun i hi => mul_nonneg (hw i hi) (hx i hi).le) hj
    have : 0 < wt j * x j := mul_pos hwj (hx j hj)
    linarith
  refine ⟨?_, hm⟩
  have key : ∀ i ∈ s, wt i * Real.log (x i) ≤
      wt i * Real.log m + (wt i * x i / m - wt i) := by
    intro i hi
    have h1 : Real.log (x i / m) ≤ x i / m - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hx i hi) hm)
    rw [Real.log_div (hx i hi).ne' hm.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hw i hi)
    have h3 : wt i * (x i / m - 1) = wt i * x i / m - wt i := by ring
    nlinarith
  calc ∑ i ∈ s, wt i * Real.log (x i)
      ≤ ∑ i ∈ s, (wt i * Real.log m + (wt i * x i / m - wt i)) := Finset.sum_le_sum key
    _ = (∑ i ∈ s, wt i) * Real.log m + ((∑ i ∈ s, wt i * x i) / m - ∑ i ∈ s, wt i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div]
    _ = Real.log m := by
        rw [hw1, ← hm_def, div_self hm.ne']
        ring

/-- Masses at a point agree for maps with the same fibres. -/
theorem cellMass_at_eq_of_fibers (p : Ω → ℝ) (f : Ω → α) (g : Ω → β)
    (hfg : ∀ w v, f w = f v ↔ g w = g v) (w : Ω) :
    cellMass p f (f w) = cellMass p g (g w) := by
  classical
  unfold cellMass
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : f v = f w
  · have h' : g v = g w := (hfg v w).1 h
    simp [h, h']
  · have h' : ¬ g v = g w := fun h'' => h ((hfg v w).2 h'')
    simp [h, h']

/-- The pair cell is contained in the side-information cell. -/
theorem cellMass_pair_le (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (f : Ω → α) (g : Ω → β)
    (a : α) (b : β) :
    cellMass p (fun w => (f w, g w)) (a, b) ≤ cellMass p g b := by
  classical
  unfold cellMass
  apply Finset.sum_le_sum
  intro v _
  by_cases hf : f v = a <;> by_cases hg : g v = b <;> simp [hf,hg,hp v]

/-- Atom form of conditional entropy. -/
theorem condEnt_atom (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) :
    condEnt p f g = ∑ w, p w * (Real.log (cellMass p g (g w)) -
      Real.log (cellMass p (fun v => (f v, g v)) (f w, g w))) := by
  classical
  unfold condEnt
  rw [mapEntropyNats_atom, mapEntropyNats_atom]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Every atom of the conditional-entropy sum is nonnegative. -/
theorem condEnt_term_nonneg (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (f : Ω → α) (g : Ω → β)
    (w : Ω) :
    0 ≤ p w * (Real.log (cellMass p g (g w)) -
      Real.log (cellMass p (fun v => (f v, g v)) (f w, g w))) := by
  classical
  rcases (hp w).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · apply mul_nonneg hpos.le
    have hpair : p w ≤ cellMass p (fun v => (f v, g v)) (f w, g w) :=
      mass_le_cellMass hp (fun v => (f v, g v)) w
    have hle := cellMass_pair_le p hp f g (f w) (g w)
    have hpos' : 0 < cellMass p (fun v => (f v, g v)) (f w, g w) := hpos.trans_le hpair
    have := Real.log_le_log hpos' hle
    linarith

/-- Dropping atoms lowers the conditional entropy. -/
theorem condEnt_ge_subset (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (f : Ω → α) (g : Ω → β)
    (T : Finset Ω) :
    ∑ w ∈ T, p w * (Real.log (cellMass p g (g w)) -
      Real.log (cellMass p (fun v => (f v, g v)) (f w, g w))) ≤ condEnt p f g := by
  rw [condEnt_atom]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun w _ _ => condEnt_term_nonneg p hp f g w)

theorem condEnt_nonneg (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (f : Ω → α) (g : Ω → β) :
    0 ≤ condEnt p f g := by
  have := condEnt_ge_subset p hp f g ∅
  simpa using this

variable [DecidableEq β]

/-- Typical atoms: positive mass and conditional probability at most `c`. -/
def typicalSet {n : ℕ} (p : Ω → ℝ) (Z : Ω → Vec n) (S : Ω → β) (c : ℝ) : Finset Ω :=
  univ.filter fun w => 0 < p w ∧
    cellMass p (fun v => (Z v, S v)) (Z w, S w) ≤ c * cellMass p S (S w)

/-- Mass of the typical atoms. -/
def typicalMass {n : ℕ} (p : Ω → ℝ) (Z : Ω → Vec n) (S : Ω → β) (c : ℝ) : ℝ :=
  ∑ w ∈ typicalSet p Z S c, p w

theorem typicalMass_nonneg {n : ℕ} (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (Z : Ω → Vec n)
    (S : Ω → β) (c : ℝ) : 0 ≤ typicalMass p Z S c :=
  Finset.sum_nonneg (fun w _ => hp w)

theorem typicalMass_le_one {n : ℕ} (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1)
    (Z : Ω → Vec n) (S : Ω → β) (c : ℝ) : typicalMass p Z S c ≤ 1 := by
  rw [← hp1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => hp w)

/-- Averaging the hashed cell masses over all matrices. -/
theorem sum_hashed_cell_le {k n : ℕ} (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (Z : Ω → Vec n)
    (S : Ω → β) (w : Ω) :
    ∑ M : Mat k n, cellMass p (fun v => (mulVec M (Z v), S v)) (mulVec M (Z w), S w) ≤
      (Fintype.card (Mat k n) : ℝ) *
        (cellMass p (fun v => (Z v, S v)) (Z w, S w) + (2 ^ k)⁻¹ * cellMass p S (S w)) := by
  classical
  set N : ℝ := (Fintype.card (Mat k n) : ℝ)
  set t : ℝ := (2 ^ k)⁻¹
  simp_rw [cellMass_explicit]
  rw [Finset.sum_comm]
  have hterm : ∀ v : Ω,
      (∑ M : Mat k n, if (mulVec M (Z v), S v) = (mulVec M (Z w), S w) then p v else 0) =
        if S v = S w then p v *
          ((univ.filter fun M : Mat k n => mulVec M (Z v) = mulVec M (Z w)).card : ℝ)
        else 0 := by
    intro v
    by_cases hs : S v = S w
    · simp only [hs, ite_true, Prod.mk.injEq, and_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    · simp [hs]
  rw [Finset.sum_congr rfl (fun v _ => hterm v)]
  have hbound : ∀ v : Ω,
      (if S v = S w then p v *
          ((univ.filter fun M : Mat k n => mulVec M (Z v) = mulVec M (Z w)).card : ℝ)
        else 0) ≤
      N * (if (Z v, S v) = (Z w, S w) then p v else 0) + N * t * (if S v = S w then p v else 0) := by
    intro v
    have hc := card_collide_le (k := k) (Z w) (Z v)
    have hb := mul_le_mul_of_nonneg_left hc (hp v)
    by_cases hs : S v = S w
    · by_cases hz : Z v = Z w
      · simpa [hs,hz,Prod.mk.injEq,N,t,mul_add,mul_assoc,mul_comm,mul_left_comm] using hb
      · simpa [hs,hz,Prod.mk.injEq,N,t,mul_add,mul_assoc,mul_comm,mul_left_comm] using hb
    · simp [hs,Prod.mk.injEq]
  calc _ ≤ ∑ v : Ω, (N * (if (Z v, S v) = (Z w, S w) then p v else 0) +
          N * t * (if S v = S w then p v else 0)) := Finset.sum_le_sum (fun v _ => hbound v)
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- **Finite hashing inequality.**  Averaged over all binary matrices, the hashed
conditional entropy is at least `-A log (c + 2^{-k})`, where `A` is the typical mass. -/
theorem sum_condEnt_hash_ge {k n : ℕ} (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (Z : Ω → Vec n)
    (S : Ω → β) {c : ℝ} (hc : 0 < c) :
    -((Fintype.card (Mat k n) : ℝ) * typicalMass p Z S c) * Real.log (c + (2 ^ k)⁻¹) ≤
      ∑ M : Mat k n, condEnt p (fun w => mulVec M (Z w)) S := by
  classical
  set N : ℝ := (Fintype.card (Mat k n) : ℝ) with hN
  set T := typicalSet p Z S c with hT
  set A := typicalMass p Z S c with hA
  have hNpos : 0 < N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  have hA0 : 0 ≤ A := typicalMass_nonneg p hp Z S c
  have hsumnonneg : 0 ≤ ∑ M : Mat k n, condEnt p (fun w => mulVec M (Z w)) S :=
    Finset.sum_nonneg (fun M _ => condEnt_nonneg p hp _ _)
  rcases hA0.eq_or_lt with hA00 | hApos
  · rw [← hA00]; simpa using hsumnonneg
  -- notation for the three cell masses
  set cg : Ω → ℝ := fun w => cellMass p S (S w) with hcg
  set cz : Ω → ℝ := fun w => cellMass p (fun v => (Z v, S v)) (Z w, S w) with hcz
  set cq : Mat k n → Ω → ℝ := fun M w =>
    cellMass p (fun v => (mulVec M (Z v), S v)) (mulVec M (Z w), S w) with hcq
  have hmemT : ∀ w ∈ T, 0 < p w ∧ cz w ≤ c * cg w := by
    intro w hw
    simpa [hT, typicalSet] using hw
  have hcg_pos : ∀ w ∈ T, 0 < cg w := by
    intro w hw
    exact (hmemT w hw).1.trans_le (mass_le_cellMass hp S w)
  have hcq_pos : ∀ M, ∀ w ∈ T, 0 < cq M w := by
    intro M w hw
    exact (hmemT w hw).1.trans_le (mass_le_cellMass hp (fun v => (mulVec M (Z v), S v)) w)
  -- step 1: drop atypical atoms
  have step1 : ∑ M : Mat k n, ∑ w ∈ T, p w * (Real.log (cg w) - Real.log (cq M w)) ≤
      ∑ M : Mat k n, condEnt p (fun w => mulVec M (Z w)) S :=
    Finset.sum_le_sum (fun M _ => condEnt_ge_subset p hp (fun w => mulVec M (Z w)) S T)
  -- step 2: Jensen on `univ ×ˢ T`
  set s : Finset (Mat k n × Ω) := (univ : Finset (Mat k n)) ×ˢ T with hs
  set wt : Mat k n × Ω → ℝ := fun Mw => p Mw.2 / (N * A) with hwt
  set x : Mat k n × Ω → ℝ := fun Mw => cq Mw.1 Mw.2 / cg Mw.2 with hx
  have hNA : 0 < N * A := mul_pos hNpos hApos
  have hwt_nonneg : ∀ i ∈ s, 0 ≤ wt i := by
    intro i _
    exact div_nonneg (hp _) hNA.le
  have hwt_sum : ∑ i ∈ s, wt i = 1 := by
    rw [hs, Finset.sum_product]
    simp only [hwt]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
    rw [← hN]
    change N * ((∑ w ∈ T, p w) / (N * A)) = 1
    rw [show (∑ w ∈ T, p w) = A from rfl]
    field_simp
  have hx_pos : ∀ i ∈ s, 0 < x i := by
    intro i hi
    rw [hs, Finset.mem_product] at hi
    exact div_pos (hcq_pos i.1 i.2 hi.2) (hcg_pos i.2 hi.2)
  obtain ⟨hjensen, hmpos⟩ := jensen_log s wt x hwt_nonneg hwt_sum hx_pos
  -- rewrite the step-1 sum through the Jensen variables
  have hrewrite : ∑ M : Mat k n, ∑ w ∈ T, p w * (Real.log (cg w) - Real.log (cq M w)) =
      -(N * A) * ∑ i ∈ s, wt i * Real.log (x i) := by
    rw [hs, Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [hwt, hx]
    rw [Real.log_div (hcq_pos M w hw).ne' (hcg_pos w hw).ne']
    field_simp
    ring
  -- step 3: the collision bound
  have hcoll : ∑ i ∈ s, wt i * x i ≤ c + (2 ^ k)⁻¹ := by
    have hinner : ∀ w ∈ T, ∑ M : Mat k n, p w * cq M w / cg w ≤
        N * p w * (c + (2 ^ k)⁻¹) := by
      intro w hw
      have hcgw := hcg_pos w hw
      have hsum := sum_hashed_cell_le (k := k) p hp Z S w
      have hrw : ∑ M : Mat k n, p w * cq M w / cg w =
          p w / cg w * ∑ M : Mat k n, cq M w := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro M _
        ring
      rw [hrw]
      have hczle : cz w ≤ c * cg w := (hmemT w hw).2
      have hpw : 0 ≤ p w / cg w := div_nonneg (hp w) hcgw.le
      calc p w / cg w * ∑ M : Mat k n, cq M w
          ≤ p w / cg w * (N * (cz w + (2 ^ k)⁻¹ * cg w)) :=
            mul_le_mul_of_nonneg_left hsum hpw
        _ ≤ p w / cg w * (N * (c * cg w + (2 ^ k)⁻¹ * cg w)) := by
            apply mul_le_mul_of_nonneg_left _ hpw
            apply mul_le_mul_of_nonneg_left _ hNpos.le
            linarith
        _ = N * p w * (c + (2 ^ k)⁻¹) := by
            field_simp
    have hdouble : ∑ i ∈ s, wt i * x i =
        (∑ w ∈ T, ∑ M : Mat k n, p w * cq M w / cg w) / (N * A) := by
      rw [hs, Finset.sum_product, Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro M _
      simp only [hwt, hx]
      field_simp
    rw [hdouble, div_le_iff₀ hNA]
    calc ∑ w ∈ T, ∑ M : Mat k n, p w * cq M w / cg w
        ≤ ∑ w ∈ T, N * p w * (c + (2 ^ k)⁻¹) := Finset.sum_le_sum hinner
      _ = (c + (2 ^ k)⁻¹) * (N * A) := by
          have hAeq : ∑ w ∈ T, p w = A := rfl
          rw [← Finset.sum_mul, ← Finset.mul_sum, hAeq]
          ring
  -- assemble
  have hlog : Real.log (∑ i ∈ s, wt i * x i) ≤ Real.log (c + (2 ^ k)⁻¹) :=
    Real.log_le_log hmpos hcoll
  calc -(N * A) * Real.log (c + (2 ^ k)⁻¹)
      ≤ -(N * A) * Real.log (∑ i ∈ s, wt i * x i) := by
        have := mul_le_mul_of_nonneg_left hlog hNA.le
        linarith
    _ ≤ -(N * A) * ∑ i ∈ s, wt i * Real.log (x i) := by
        have := mul_le_mul_of_nonneg_left hjensen hNA.le
        linarith
    _ = ∑ M : Mat k n, ∑ w ∈ T, p w * (Real.log (cg w) - Real.log (cq M w)) := hrewrite.symm
    _ ≤ _ := step1

/-- `log (c + 2^{-k}) ≤ -k log 2 + 2^k c`. -/
theorem log_threshold_le (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Real.log (c + (2 ^ k)⁻¹) ≤ -(k * Real.log 2) + 2 ^ k * c := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hfac : c + (2 ^ k)⁻¹ = (2 ^ k)⁻¹ * (1 + 2 ^ k * c) := by
    field_simp
    <;> ring
  have hpos : 0 < 1 + 2 ^ k * c := by positivity
  rw [hfac, Real.log_mul (inv_pos.2 h2k).ne' hpos.ne', Real.log_inv, Real.log_pow]
  have := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **Average deficit form of the finite hashing inequality.** -/
theorem avg_deficit_le {k n : ℕ} (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1)
    (Z : Ω → Vec n) (S : Ω → β) {c : ℝ} (hc : 0 < c) :
    ∑ M : Mat k n, (k * Real.log 2 - condEnt p (fun w => mulVec M (Z w)) S) ≤
      (Fintype.card (Mat k n) : ℝ) *
        ((1 - typicalMass p Z S c) * (k * Real.log 2) + 2 ^ k * c) := by
  set N : ℝ := (Fintype.card (Mat k n) : ℝ) with hN
  set A := typicalMass p Z S c
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hA0 : 0 ≤ A := typicalMass_nonneg p hp Z S c
  have hA1 : A ≤ 1 := typicalMass_le_one p hp hp1 Z S c
  have hmain := sum_condEnt_hash_ge (k := k) p hp Z S hc
  have hlog := log_threshold_le k hc.le
  have hk : (0 : ℝ) ≤ k * Real.log 2 := mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg one_le_two)
  have h2kc : 0 ≤ (2 : ℝ) ^ k * c := by positivity
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
  have h1 : -(N * A) * Real.log (c + (2 ^ k)⁻¹) ≥
      -(N * A) * (-(k * Real.log 2) + 2 ^ k * c) := by
    have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hNpos.le hA0)
    linarith
  have h2 : N * A * (2 ^ k * c) ≤ N * (2 ^ k * c) := by
    have := mul_le_mul_of_nonneg_right hA1 h2kc
    nlinarith
  nlinarith

end
end ParityHashing
