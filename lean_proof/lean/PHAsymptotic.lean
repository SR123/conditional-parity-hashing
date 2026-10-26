import PHIid

/-!
# Simultaneous common-linear hashing for independent blocks

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

Let `(Zⱼ, Sⱼ)`, `j ∈ ι`, be finitely many binary sources with side information,
all defined on one finite probability space `Ω₁`, and let `R ≥ 0` satisfy
`R log 2 < H(Zⱼ | Sⱼ)` for every `j`.  For `n` independent blocks put
`k = ⌊n R⌋`.  Then there is a constant `C` such that for every `n ≥ 1` some single
binary `k × n` matrix `M` satisfies

  `∑ⱼ (k log 2 - H(M Zⱼⁿ | Sⱼⁿ)) ≤ C`.

All deficits are nonnegative, so each is at most `C`; in particular they are
`o(n)`, which is all that the almost-entropic limit requires.  The same matrix is
used for every `j`; this is what preserves linear relations between the sources.
-/

namespace ParityHashing

open Finset SharpStability

noncomputable section

variable {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]

/-- Entropy is at most the logarithm of the alphabet size. -/
theorem mapEntropyNats_le_log_card (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1)
    (f : Ω → α) : mapEntropyNats p f ≤ Real.log (Fintype.card α) := by
  classical
  set c : α → ℝ := cellMass p f with hc
  have hc0 : ∀ a, 0 ≤ c a := fun a => cellMass_nonneg hp f a
  have hct : ∑ a, c a = 1 := by rw [hc, cellMass_total, hp1]
  set s := univ.filter (fun a => 0 < c a) with hs
  have hsum_s : ∑ a ∈ s, c a = 1 := by
    rw [← hct, hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs with h
    · rfl
    · exact (le_antisymm (not_lt.1 h) (hc0 a)).symm
  have hH : mapEntropyNats p f = ∑ a ∈ s, c a * Real.log (1 / c a) := by
    unfold mapEntropyNats
    rw [← hc, hs, Finset.sum_filter, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs with h
    · rw [one_div, Real.log_inv]; ring
    · have : c a = 0 := le_antisymm (not_lt.1 h) (hc0 a)
      simp [this]
  obtain ⟨hj, _⟩ := jensen_log s c (fun a => 1 / c a) (fun a _ => hc0 a) hsum_s
    (fun a ha => by
      have : 0 < c a := by simpa [hs] using ha
      exact one_div_pos.2 this)
  rw [hH]
  refine hj.trans ?_
  have hsimp : ∑ a ∈ s, c a * (1 / c a) = (s.card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have : 0 < c a := by simpa [hs] using ha
    field_simp
    simp
  rw [hsimp]
  have hcard_pos : (0 : ℝ) < s.card := by
    have : 0 < ∑ a ∈ s, c a := by rw [hsum_s]; exact one_pos
    have hne : s.Nonempty := Finset.nonempty_of_sum_ne_zero this.ne'
    exact_mod_cast hne.card_pos
  apply Real.log_le_log hcard_pos
  exact_mod_cast (Finset.card_le_univ s)

/-- Conditional entropy is at most unconditional entropy. -/
theorem condEnt_le_entropy (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1)
    (f : Ω → α) (g : Ω → β) : condEnt p f g ≤ mapEntropyNats p f := by
  have := mapEntropyNats_subadditive p hp hp1 f g
  unfold condEnt
  linarith

theorem condEnt_le_log_card (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1)
    (f : Ω → α) (g : Ω → β) : condEnt p f g ≤ Real.log (Fintype.card α) :=
  (condEnt_le_entropy p hp hp1 f g).trans (mapEntropyNats_le_log_card p hp hp1 f)

theorem condEnt_vec_le {k : ℕ} (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1)
    (f : Ω → Vec k) (g : Ω → β) : condEnt p f g ≤ k * Real.log 2 := by
  have h := condEnt_le_log_card p hp hp1 f g
  rw [card_vec, Nat.cast_pow, Real.log_pow] at h
  push_cast at h
  exact h

/-- Hashed deficits are nonnegative. -/
theorem hash_deficit_nonneg {k n : ℕ} (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1)
    (M : Mat k n) (Z : Ω → Vec n) (g : Ω → β) :
    0 ≤ (k : ℝ) * Real.log 2 - condEnt p (fun w => mulVec M (Z w)) g := by
  have := condEnt_vec_le p hp hp1 (fun w => mulVec M (Z w)) g
  linarith

section Typical

variable {Ω₁ σ : Type*} [Fintype Ω₁] [Fintype σ] [DecidableEq σ]

/-- Single-letter conditional self-information `-log P(z | s)`. -/
def selfInfo (p₁ : Ω₁ → ℝ) (Z₁ : Ω₁ → ZMod 2) (S₁ : Ω₁ → σ) (x : Ω₁) : ℝ :=
  Real.log (cellMass p₁ S₁ (S₁ x)) - Real.log (cellMass p₁ (fun v => (Z₁ v, S₁ v)) (Z₁ x, S₁ x))

theorem expect_selfInfo (p₁ : Ω₁ → ℝ) (Z₁ : Ω₁ → ZMod 2) (S₁ : Ω₁ → σ) :
    ∑ x, p₁ x * selfInfo p₁ Z₁ S₁ x = condEnt p₁ Z₁ S₁ := by
  rw [condEnt_atom]
  rfl

/-- Variance of the single-letter self-information. -/
def selfInfoVar (p₁ : Ω₁ → ℝ) (Z₁ : Ω₁ → ZMod 2) (S₁ : Ω₁ → σ) : ℝ :=
  ∑ x, p₁ x * (selfInfo p₁ Z₁ S₁ x - condEnt p₁ Z₁ S₁) ^ 2

/-- The block source and side information. -/
def blockZ {n : ℕ} (Z₁ : Ω₁ → ZMod 2) (ω : Fin n → Ω₁) : Vec n := fun t => Z₁ (ω t)

def blockS {n : ℕ} (S₁ : Ω₁ → σ) (ω : Fin n → Ω₁) : Fin n → σ := fun t => S₁ (ω t)

/-- Atypical mass of independent blocks is `O(1/n)`. -/
theorem one_sub_typicalMass_le {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
    (Z₁ : Ω₁ → ZMod 2) (S₁ : Ω₁ → σ) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    1 - typicalMass (prodMass p₁ n) (blockZ Z₁) (blockS S₁)
        (Real.exp (-(n * (condEnt p₁ Z₁ S₁ - δ)))) ≤
      selfInfoVar p₁ Z₁ S₁ / (n * δ ^ 2) := by
  classical
  set μ := prodMass p₁ n with hμ
  set H := condEnt p₁ Z₁ S₁ with hH
  set c := Real.exp (-(n * (H - δ))) with hc
  set Y := selfInfo p₁ Z₁ S₁ with hY
  set g : Ω₁ → ℝ := fun x => Y x - H with hg
  set T := typicalSet μ (blockZ Z₁) (blockS S₁) c with hT
  have hμ1 : ∑ ω, μ ω = 1 := prodMass_sum hp1 n
  have hμ0 : ∀ ω, 0 ≤ μ ω := prodMass_nonneg hp n
  have hEg : ∑ x, p₁ x * g x = 0 := by
    simp only [hg, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
    rw [hY, expect_selfInfo]
    ring
  -- product form of the two cell masses at a block
  have hcz : ∀ ω : Fin n → Ω₁,
      cellMass μ (fun v => (blockZ Z₁ v, blockS S₁ v)) (blockZ Z₁ ω, blockS S₁ ω) =
        ∏ t, cellMass p₁ (fun v => (Z₁ v, S₁ v)) (Z₁ (ω t), S₁ (ω t)) := by
    intro ω
    rw [cellMass_at_eq_of_fibers μ (fun v => (blockZ Z₁ v, blockS S₁ v))
      (fun v t => (Z₁ (v t), S₁ (v t)))]
    · exact cellMass_prod_coord p₁ n (fun v => (Z₁ v, S₁ v)) _
    · intro w v
      constructor
      · intro h
        funext t
        have h1 := congrFun (Prod.mk.inj h).1 t
        have h2 := congrFun (Prod.mk.inj h).2 t
        simp only [blockZ, blockS] at h1 h2
        rw [h1, h2]
      · intro h
        have h' := fun t => congrFun h t
        simp only [Prod.mk.injEq] at h'
        refine Prod.ext ?_ ?_
        · funext t; exact (h' t).1
        · funext t; exact (h' t).2
  have hcg : ∀ ω : Fin n → Ω₁,
      cellMass μ (blockS S₁) (blockS S₁ ω) = ∏ t, cellMass p₁ S₁ (S₁ (ω t)) := by
    intro ω
    exact cellMass_prod_coord p₁ n S₁ _
  -- an atypical atom of positive mass has a small self-information sum
  have hkey : ∀ ω : Fin n → Ω₁, 0 < μ ω →
      ¬ (cellMass μ (fun v => (blockZ Z₁ v, blockS S₁ v)) (blockZ Z₁ ω, blockS S₁ ω) ≤
        c * cellMass μ (blockS S₁) (blockS S₁ ω)) →
      ∑ t, g (ω t) ≤ -(n * δ) := by
    intro ω hpos hnot
    push Not at hnot
    rw [hcz, hcg] at hnot
    have hall : ∀ t, 0 < p₁ (ω t) := by
      intro t
      refine lt_of_le_of_ne (hp _) ?_
      intro h0
      apply hpos.ne'
      rw [hμ, prodMass]
      exact Finset.prod_eq_zero (Finset.mem_univ t) h0.symm
    have hzpos : ∀ t, 0 < cellMass p₁ (fun v => (Z₁ v, S₁ v)) (Z₁ (ω t), S₁ (ω t)) :=
      fun t => (hall t).trans_le (mass_le_cellMass hp (fun v => (Z₁ v, S₁ v)) (ω t))
    have hspos : ∀ t, 0 < cellMass p₁ S₁ (S₁ (ω t)) :=
      fun t => (hall t).trans_le (mass_le_cellMass hp S₁ (ω t))
    have hprodS : 0 < ∏ t, cellMass p₁ S₁ (S₁ (ω t)) :=
      Finset.prod_pos (fun t _ => hspos t)
    have hlt := Real.log_lt_log (mul_pos (Real.exp_pos _) hprodS) hnot
    rw [Real.log_mul (Real.exp_pos _).ne' hprodS.ne', Real.log_exp,
      Real.log_prod (fun t _ => (hspos t).ne'), Real.log_prod (fun t _ => (hzpos t).ne')] at hlt
    have hsumY : ∑ t, Y (ω t) = ∑ t, Real.log (cellMass p₁ S₁ (S₁ (ω t))) -
        ∑ t, Real.log (cellMass p₁ (fun v => (Z₁ v, S₁ v)) (Z₁ (ω t), S₁ (ω t))) := by
      rw [← Finset.sum_sub_distrib]
      rfl
    have hsumg : ∑ t, g (ω t) = ∑ t, Y (ω t) - n * H := by
      simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hsumg, hsumY]
    linarith
  -- compare the atypical mass with the Chebyshev event
  have hsplit : 1 - typicalMass μ (blockZ Z₁) (blockS S₁) c =
      ∑ ω, if ω ∈ T then 0 else μ ω := by
    rw [← hμ1, typicalMass, ← hT, ← Finset.sum_filter_add_sum_filter_not univ (· ∈ T)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.sum_filter]
    simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    ring_nf
  have hle : ∀ ω : Fin n → Ω₁, (if ω ∈ T then 0 else μ ω) ≤
      if ∑ t, g (ω t) ≤ -(n * δ) then μ ω else 0 := by
    intro ω
    by_cases hω : ω ∈ T
    · simp only [hω, ite_true]
      split_ifs <;> simp [hμ0 ω]
    · simp only [hω, ite_false]
      rcases (hμ0 ω).eq_or_lt with h0 | hpos
      · rw [← h0]; split_ifs <;> simp
      · have hnot : ¬ (cellMass μ (fun v => (blockZ Z₁ v, blockS S₁ v))
            (blockZ Z₁ ω, blockS S₁ ω) ≤ c * cellMass μ (blockS S₁) (blockS S₁ ω)) := by
          intro h
          apply hω
          rw [hT, typicalSet, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hpos, h⟩
        rw [if_pos (hkey ω hpos hnot)]
  rw [hsplit]
  calc ∑ ω, (if ω ∈ T then 0 else μ ω)
      ≤ ∑ ω, (if ∑ t, g (ω t) ≤ -(n * δ) then μ ω else 0) := Finset.sum_le_sum (fun ω _ => hle ω)
    _ = ∑ ω ∈ univ.filter (fun ω : Fin n → Ω₁ => ∑ t, g (ω t) ≤ -(n * δ)), μ ω := by
        rw [Finset.sum_filter]
    _ ≤ (∑ x, p₁ x * g x ^ 2) / (n * δ ^ 2) := chebyshev_coord hp hp1 hn g hEg hδ
    _ = selfInfoVar p₁ Z₁ S₁ / (n * δ ^ 2) := rfl

end Typical

/-- From an average bound to a single good choice. -/
theorem exists_le_of_sum_le_card {γ : Type*} [Fintype γ] [Nonempty γ] (F : γ → ℝ) (C : ℝ)
    (h : ∑ x, F x ≤ (Fintype.card γ : ℝ) * C) : ∃ x, F x ≤ C := by
  by_contra hne
  push Not at hne
  have hlt : ∑ _x : γ, C < ∑ x, F x :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ => hne x)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  linarith

section Main

variable {Ω₁ ι σ : Type*} [Fintype Ω₁] [Fintype ι] [Fintype σ] [DecidableEq σ]

/-- **Simultaneous common-linear hashing with uniformly bounded deficits.** -/
theorem uniform_deficit_bound {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
    (Z : ι → Ω₁ → ZMod 2) (S : ι → Ω₁ → σ) {R : ℝ} (hR : 0 ≤ R)
    (hthr : ∀ j, R * Real.log 2 < condEnt p₁ (Z j) (S j)) :
    ∃ C : ℝ, ∀ n : ℕ, 0 < n → ∃ M : Mat (⌊n * R⌋₊) n,
      ∑ j, ((⌊n * R⌋₊ : ℝ) * Real.log 2 -
        condEnt (prodMass p₁ n) (fun ω => mulVec M (blockZ (Z j) ω)) (blockS (S j))) ≤ C := by
  classical
  set δ : ι → ℝ := fun j => (condEnt p₁ (Z j) (S j) - R * Real.log 2) / 2 with hδ
  have hδpos : ∀ j, 0 < δ j := fun j => by
    have := hthr j
    simp only [hδ]
    linarith
  refine ⟨∑ j, (selfInfoVar p₁ (Z j) (S j) * (R * Real.log 2) / δ j ^ 2 + 1), ?_⟩
  intro n hn
  set k := ⌊n * R⌋₊ with hk
  have hkle : (k : ℝ) ≤ n * R := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hR)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set μ := prodMass p₁ n
  have hμ0 : ∀ ω, 0 ≤ μ ω := prodMass_nonneg hp n
  have hμ1 : ∑ ω, μ ω = 1 := prodMass_sum hp1 n
  set c : ι → ℝ := fun j => Real.exp (-(n * (condEnt p₁ (Z j) (S j) - δ j))) with hc
  -- per-source bound on the averaged deficit
  have hper : ∀ j, (1 - typicalMass μ (blockZ (Z j)) (blockS (S j)) (c j)) *
      (k * Real.log 2) + 2 ^ k * c j ≤
      selfInfoVar p₁ (Z j) (S j) * (R * Real.log 2) / δ j ^ 2 + 1 := by
    intro j
    have hA := one_sub_typicalMass_le hp hp1 (Z j) (S j) hn (hδpos j)
    have hA0 : 0 ≤ 1 - typicalMass μ (blockZ (Z j)) (blockS (S j)) (c j) := by
      have := typicalMass_le_one μ hμ0 hμ1 (blockZ (Z j)) (blockS (S j)) (c j)
      linarith
    have hk0 : 0 ≤ (k : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg k) hlog2.le
    have hfirst : (1 - typicalMass μ (blockZ (Z j)) (blockS (S j)) (c j)) * (k * Real.log 2) ≤
        selfInfoVar p₁ (Z j) (S j) / (n * δ j ^ 2) * (n * R * Real.log 2) := by
      apply mul_le_mul hA _ hk0
      · exact le_trans hA0 hA
      · exact mul_le_mul_of_nonneg_right hkle hlog2.le
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hfirst' : selfInfoVar p₁ (Z j) (S j) / (n * δ j ^ 2) * (n * R * Real.log 2) =
        selfInfoVar p₁ (Z j) (S j) * (R * Real.log 2) / δ j ^ 2 := by
      have := (hδpos j).ne'
      field_simp
    have hsecond : (2 : ℝ) ^ k * c j ≤ 1 := by
      have h2k : (2 : ℝ) ^ k = Real.exp (k * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log two_pos]
      rw [h2k, hc, ← Real.exp_add]
      apply Real.exp_le_one_iff.2
      have hdj : δ j = (condEnt p₁ (Z j) (S j) - R * Real.log 2) / 2 := rfl
      have hnd : 0 ≤ (n : ℝ) * δ j := mul_nonneg hnpos.le (hδpos j).le
      nlinarith [mul_le_mul_of_nonneg_right hkle hlog2.le]
    linarith
  -- average over all matrices and select one
  have havg : ∑ M : Mat k n, ∑ j, ((k : ℝ) * Real.log 2 -
      condEnt μ (fun ω => mulVec M (blockZ (Z j) ω)) (blockS (S j))) ≤
      (Fintype.card (Mat k n) : ℝ) *
        ∑ j, (selfInfoVar p₁ (Z j) (S j) * (R * Real.log 2) / δ j ^ 2 + 1) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hcj : 0 < c j := Real.exp_pos _
    have h := avg_deficit_le (k := k) μ hμ0 hμ1 (blockZ (Z j)) (blockS (S j)) hcj
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left (hper j)
    exact Nat.cast_nonneg _
  exact exists_le_of_sum_le_card _ _ havg

end Main

end
end ParityHashing
