import PHConditional

/-!
# Conditional parity hashing: almost-entropic membership

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

Main generic theorem.  Let `p₁` be a finite probability mass on atoms `Ω₁`,
`X i : Ω₁ → Fin m` four variables and `π i` parity labels with
`χ_A + χ_B + χ_C + χ_D = 0` on every atom.  Suppose the ten single-letter
conditional entropies `H(Zⱼ | Sⱼ)` of `pairZ`/`pairS` are at least `b log 2`.
Then for every `0 ≤ R ≤ b` the table `h - R · U₃,₄` lies in the actual closure of
finite four-variable entropy tables, where `h` is the entropy table of the source.

The source-specific facts for the Matúš–Csirmaz 24-atom law (parity relation,
the ten threshold inequalities with `b = I(C;D|AB)`, and the score interval) are
separate obligations; see `DEVELOPMENT_STATUS.txt`.
-/

namespace ParityHashing

open Finset SharpStability Filter Topology

noncomputable section

/-- Rank function of the uniform matroid `U₃,₄`. -/
def u34 : EntropyTable := fun S => ((min 3 S.card : ℕ) : ℝ)

variable {Ω₁ : Type*} [Fintype Ω₁] {m : ℕ}

/-- Source entropy table in bits. -/
def sourceTable (p₁ : Ω₁ → ℝ) (X : Fin 4 → Ω₁ → Fin m) : EntropyTable :=
  fun S => mapEntropyNats p₁ (sideInfo X S) / Real.log 2

theorem sourceTable_eq_finiteEntropy {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
    (X : Fin 4 → Ω₁ → Fin m) : sourceTable p₁ X = finiteEntropy (pushLaw4 p₁ hp hp1 X) := by
  funext S
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have h := finiteEntropy_pushLaw4 p₁ hp hp1 X S
  rw [sourceTable, div_eq_iff hlog, h]
  symm
  apply mapEntropyNats_same_fibers
  intro a b
  constructor
  · intro hab
    funext i
    by_cases hi : i ∈ S
    · have := congrFun hab ⟨i, hi⟩
      simp only [sideInfo, hi, ite_true, this]
    · simp [sideInfo, hi]
  · intro hab
    funext i
    have := congrFun hab i
    simp only [sideInfo, i.2, ite_true] at this
    exact Option.some.inj this

theorem sourceTable_mem_ae {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
    (X : Fin 4 → Ω₁ → Fin m) : sourceTable p₁ X ∈ aeTables := by
  rw [sourceTable_eq_finiteEntropy hp hp1 X]
  exact subset_closure (pushLaw4_mem _ _ _ _)

theorem floor_div_close {R : ℝ} (hR : 0 ≤ R) {N : ℕ} (hN : 0 < N) :
    |(⌊(N : ℝ) * R⌋₊ : ℝ) / N - R| ≤ 1 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (⌊(N : ℝ) * R⌋₊ : ℝ) ≤ N * R := Nat.floor_le (mul_nonneg hNpos.le hR)
  have h2 : (N : ℝ) * R < ⌊(N : ℝ) * R⌋₊ + 1 := Nat.lt_floor_add_one _
  have h3 : |(⌊(N : ℝ) * R⌋₊ : ℝ) - N * R| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have h4 : (⌊(N : ℝ) * R⌋₊ : ℝ) / N - R = ((⌊(N : ℝ) * R⌋₊ : ℝ) - N * R) / N := by
    field_simp
  rw [h4, abs_div, abs_of_pos hNpos]
  exact div_le_div_of_nonneg_right h3 hNpos.le

/-- **Strict version.** -/
theorem parity_hashing_strict {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
    (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2)
    (hxor : ∀ x, parity X π 0 x + parity X π 1 x + parity X π 2 x + parity X π 3 x = 0)
    {R : ℝ} (hR : 0 ≤ R)
    (hthr : ∀ j : Fin 10, R * Real.log 2 < condEnt p₁ (pairZ X π j) (pairS X j)) :
    sourceTable p₁ X - R • u34 ∈ aeTables := by
  obtain ⟨C, hC⟩ := uniform_deficit_bound hp hp1 (pairZ X π) (pairS X) hR hthr
  choose M hM using hC
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the approximating sequence, indexed by `N = n + 1`
  set v : ℕ → EntropyTable := fun n =>
    (1 / ((n : ℝ) + 1)) • condTable p₁ X (auxW X π (M (n + 1) (Nat.succ_pos n))) with hv
  have hvmem : ∀ n, v n ∈ aeTables := by
    intro n
    exact ae_smul (condTable_mem_ae hp hp1 X _) (by positivity)
  have hC0 : 0 ≤ C := by
    have h := hM 1 Nat.one_pos
    have hnn : ∀ j : Fin 10, 0 ≤ deficit p₁ X π (M 1 Nat.one_pos) j :=
      deficit_nonneg hp hp1 X π (M 1 Nat.one_pos)
    exact le_trans (Finset.sum_nonneg (fun j _ => hnn j)) h
  have hconv : ∀ S : Finset (Fin 4), Tendsto (fun n => v n S) atTop
      (𝓝 ((sourceTable p₁ X - R • u34) S)) := by
    intro S
    set K : ℝ := C / Real.log 2 + 3 with hK
    have hbound : ∀ n : ℕ, dist (v n S) ((sourceTable p₁ X - R • u34) S) ≤ K / ((n : ℝ) + 1) := by
      intro n
      set N := n + 1 with hN
      have hNpos : (0 : ℝ) < N := by positivity
      have hNcast : (N : ℝ) = (n : ℝ) + 1 := by rw [hN]; push_cast; ring
      set k := ⌊(N : ℝ) * R⌋₊ with hk
      have hprof := block_profile_bound hp hp1 X π hxor (M N (Nat.succ_pos n)) S
      have hdef : ∑ j, deficit p₁ X π (M N (Nat.succ_pos n)) j ≤ C := hM N (Nat.succ_pos n)
      have hfl := floor_div_close (N:=N) hR (show 0 < N from Nat.succ_pos n)
      have hu : ((min 3 S.card : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.min_le_left 3 S.card
      have hu0 : (0 : ℝ) ≤ ((min 3 S.card : ℕ) : ℝ) := Nat.cast_nonneg _
      -- normalise
      set c := condEnt (prodMass p₁ N) (blockSide X S) (auxW X π (M N (Nat.succ_pos n)))
      set h := mapEntropyNats p₁ (sideInfo X S)
      set u := ((min 3 S.card : ℕ) : ℝ)
      have hvS : v n S = c / (N * Real.log 2) := by
        simp only [hv, Pi.smul_apply, smul_eq_mul, condTable]
        rw [← hNcast]
        field_simp
        rfl
      have htS : (sourceTable p₁ X - R • u34) S = h / Real.log 2 - R * u := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sourceTable, u34]
        rfl
      rw [Real.dist_eq, hvS, htS]
      have hc : |c - (N * h - k * u * Real.log 2)| ≤ C := hprof.trans hdef
      have key : c / (N * Real.log 2) - (h / Real.log 2 - R * u) =
          (c - (N * h - k * u * Real.log 2)) / (N * Real.log 2) +
            (R - (k : ℝ) / N) * u := by
        field_simp
        ring
      rw [key, ← hNcast]
      calc |(c - (N * h - k * u * Real.log 2)) / (N * Real.log 2) + (R - (k : ℝ) / N) * u|
          ≤ |(c - (N * h - k * u * Real.log 2)) / (N * Real.log 2)| +
              |(R - (k : ℝ) / N) * u| := abs_add_le _ _
        _ ≤ C / (N * Real.log 2) + 1 / N * 3 := by
            gcongr
            · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N * Real.log 2)]
              exact div_le_div_of_nonneg_right hc (by positivity)
            · rw [abs_mul, abs_of_nonneg hu0, abs_sub_comm]
              exact mul_le_mul hfl hu hu0 (by positivity)
        _ = K / N := by
            rw [hK]
            field_simp
            <;> ring
    have hK : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun j : ℕ => 1 / ((j:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := hbase.const_mul K
      simpa only [div_eq_mul_inv,one_mul,mul_zero] using h2
    exact tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero (fun n => dist_nonneg) hbound hK)
  have hlim : Tendsto v atTop (𝓝 (sourceTable p₁ X - R • u34)) := tendsto_pi_nhds.2 hconv
  exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall hvmem)

/-- **Main generic theorem: the closed range `0 ≤ R ≤ b`.** -/
theorem parity_hashing_mem_ae {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
    (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2)
    (hxor : ∀ x, parity X π 0 x + parity X π 1 x + parity X π 2 x + parity X π 3 x = 0)
    {b : ℝ} (hthr : ∀ j : Fin 10, b * Real.log 2 ≤ condEnt p₁ (pairZ X π j) (pairS X j))
    {R : ℝ} (hR0 : 0 ≤ R) (hRb : R ≤ b) :
    sourceTable p₁ X - R • u34 ∈ aeTables := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases hRb.lt_or_eq with hlt | heq
  · exact parity_hashing_strict hp hp1 X π hxor hR0
      (fun j => lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt hlog) (hthr j))
  · subst heq
    rcases hR0.eq_or_lt with h0 | hpos
    · rw [← h0, zero_smul, sub_zero]
      exact sourceTable_mem_ae hp hp1 X
    · -- approach `R` from below
      set Rj : ℕ → ℝ := fun j => R * (1 - 1 / ((j : ℝ) + 2)) with hRj
      have hRj0 : ∀ j, 0 ≤ Rj j := by
        intro j
        apply mul_nonneg hR0
        rw [sub_nonneg, div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have hRjlt : ∀ j, Rj j < R := by
        intro j
        have : 0 < 1 / ((j : ℝ) + 2) := by positivity
        simp only [hRj]
        nlinarith
      have hmem : ∀ j, sourceTable p₁ X - Rj j • u34 ∈ aeTables := by
        intro j
        exact parity_hashing_strict hp hp1 X π hxor (hRj0 j)
          (fun i => lt_of_lt_of_le (mul_lt_mul_of_pos_right (hRjlt j) hlog) (hthr i))
      have hRlim : Tendsto Rj atTop (𝓝 R) := by
        have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
          have hbase : Tendsto (fun j : ℕ => 1 / ((j:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          apply squeeze_zero (fun j => by positivity) (fun j => ?_) hbase
          apply one_div_le_one_div_of_le (by positivity)
          linarith
        have h2 := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub h1).const_mul R
        simpa [hRj] using h2
      have hlim : Tendsto (fun j => sourceTable p₁ X - Rj j • u34) atTop
          (𝓝 (sourceTable p₁ X - R • u34)) :=
        tendsto_const_nhds.sub (hRlim.smul_const u34)
      exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall hmem)

/-- Ingleton functional with `A,B,C,D = 0,1,2,3`:
`I(C;D|A) + I(C;D|B) + I(A;B) - I(C;D)`. -/
def ingletonJ (h : EntropyTable) : ℝ :=
  tableCMI h 2 3 0 + tableCMI h 2 3 1 + tableMI h 0 1 - tableMI h 2 3

theorem continuous_ingletonJ : Continuous ingletonJ := by
  unfold ingletonJ tableCMI tableMI
  fun_prop

/-- **Finite witnesses.**  If an almost-entropic table has positive total entropy
and score below `s`, then some finite law has score below `s`. -/
theorem finite_witness_of_ae {z : EntropyTable} (hz : z ∈ aeTables)
    (hpos : 0 < z Finset.univ) {s : ℝ} (hs : ingletonJ z < s * z Finset.univ) :
    ∃ (N : ℕ) (P : FiniteLaw4 N), 0 < finiteEntropy P Finset.univ ∧
      ingletonJ (finiteEntropy P) < s * finiteEntropy P Finset.univ := by
  set U : Set EntropyTable := {h | 0 < h Finset.univ ∧ ingletonJ h < s * h Finset.univ}
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const (continuous_apply _)
    · exact isOpen_lt continuous_ingletonJ (continuous_const.mul (continuous_apply _))
  have hzU : z ∈ U := ⟨hpos, hs⟩
  obtain ⟨h, ⟨hU', hfin⟩⟩ := mem_closure_iff.1 hz U hU hzU
  obtain ⟨N, P, rfl⟩ := hfin
  exact ⟨N, P, hU'.1, hU'.2⟩

end
end ParityHashing
