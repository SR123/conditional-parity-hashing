import PHMain
import ParityEndpoint

/-!
# Source instantiation of the generic parity-hashing theorem

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

We instantiate `ParityHashing.parity_hashing_mem_ae` with the published
Matúš–Csirmaz 24-atom source of `ParityFiniteSource`:

* atoms `Fin 24`, masses `sourceWeights` (cast to `ℝ`);
* variables `X i a = sourceAtoms a i`;
* parity labels `π i x = (chi x).val` in `ZMod 2`.

We prove the parity relation on every atom, the ten threshold inequalities with
`b = criticalRate`, identify `sourceTable - R • u34` with Astra's
`shiftedProfile R`, identify `aeTables` with `almostEntropicProfiles` (rfl), and
obtain `FullParityHashingResult`.

Threshold values (nats), with `H = sourceHNats`, `h₂ = binaryNats`:
  AB/E   : H - h₂(Q)            (equal to `criticalRate * log 2`)
  AC/V   : H + P log 2 - h₂(P)
  AD/V   : h₂(P)
  BC/U   : h₂(P)
  BD/U   : H + P log 2 - h₂(P)
  CD/U   : H - h₂(T)
  partner bits (four) : log 2
The joint entropies are obtained from injectivity on atoms (four cases), from a
24-atom finite-mass computation (two cases) and from the exact partner
uniformity `source_partner_uniform` (four cases).  The side-information
entropies are Astra's compiled `source_entropy_*` formulas.
-/

namespace ConditionalParityHashing

noncomputable section

open Finset SharpStability

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Atom masses as reals. -/
abbrev srcP : Fin 24 → ℝ := fun a => (sourceWeights a : ℝ)

/-- The four observed coordinates. -/
abbrev srcX : Fin 4 → Fin 24 → Fin 4 := fun i a => sourceAtoms a i

/-- Parity label `χ = (0,1,1,0)`, as an element of `ZMod 2`. -/
abbrev srcPi : Fin 4 → Fin 4 → ZMod 2 := fun _ x => ((chi x).val : ZMod 2)

theorem srcP_nonneg : ∀ a, 0 ≤ srcP a := by
  intro a
  exact_mod_cast sourceWeights_nonneg a

theorem srcP_sum : ∑ a, srcP a = 1 := by
  have h := sourceWeights_sum
  simp only [srcP]
  exact_mod_cast h

theorem log2_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-! ## The parity relation -/

theorem src_xor : ∀ a : Fin 24,
    ParityHashing.parity srcX srcPi 0 a + ParityHashing.parity srcX srcPi 1 a +
      ParityHashing.parity srcX srcPi 2 a + ParityHashing.parity srcX srcPi 3 a = 0 := by
  decide

/-! ## Fibre lemmas -/

theorem zcast_inj (x y : Fin 2) : ((x.val : ℕ) : ZMod 2) = ((y.val : ℕ) : ZMod 2) ↔ x = y := by
  revert x y
  decide

theorem sideInfo_eq_iff (S : Finset (Fin 4)) (a b : Fin 24) :
    ParityHashing.sideInfo srcX S a = ParityHashing.sideInfo srcX S b ↔
      ∀ i ∈ S, sourceAtoms a i = sourceAtoms b i := by
  constructor
  · intro h i hi
    have h1 := congrFun h i
    simp only [ParityHashing.sideInfo, srcX, hi, ite_true] at h1
    exact Option.some.inj h1
  · intro h
    funext i
    simp only [ParityHashing.sideInfo, srcX]
    split_ifs with hi
    · rw [h i hi]
    · rfl

/-- Side-information entropies are Astra's source entropies. -/
theorem side_entropy (S : Finset (Fin 4)) :
    mapEntropyNats srcP (ParityHashing.sideInfo srcX S) =
      finiteEntropy sourceLaw S * Real.log 2 := by
  rw [source_entropy_atoms, div_mul_cancel₀ _ log2_pos'.ne']
  apply mapEntropyNats_same_fibers
  intro a b
  rw [sideInfo_eq_iff]
  constructor
  · intro h
    funext i
    exact h i.1 i.2
  · intro h i hi
    exact congrFun h ⟨i, hi⟩

/-! ## Joint entropies of the injective pairs -/

theorem atoms_injective : Function.Injective sourceAtoms := by
  decide

theorem full_entropy :
    mapEntropyNats srcP (fun a => fun i : ({0, 1, 2, 3} : Finset (Fin 4)) => sourceAtoms a i) =
      sourceHNats + 3 * Real.log 2 := by
  have h := source_entropy_atoms {0, 1, 2, 3}
  rw [source_entropy_ABCD, eq_div_iff log2_pos'.ne'] at h
  -- h : (3 + sourceHNats / log 2) * log 2 = mapEntropyNats (fun a => ↑(sourceWeights a)) _
  rw [show srcP = (fun a : Fin 24 => (sourceWeights a : ℝ)) from rfl, ← h,
    add_mul, div_mul_cancel₀ _ log2_pos'.ne']
  ring

theorem entropy_of_injective {α : Type*} [Fintype α] {f : Fin 24 → α}
    (hf : Function.Injective f) : mapEntropyNats srcP f = sourceHNats + 3 * Real.log 2 := by
  rw [← full_entropy]
  apply mapEntropyNats_same_fibers
  intro a b
  constructor
  · intro h
    rw [hf h]
  · intro h
    apply congrArg f
    apply atoms_injective
    funext i
    have hi : i ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by fin_cases i <;> decide
    exact congrFun h ⟨i, hi⟩

theorem inj0 : Function.Injective
    (fun a => (ParityHashing.pairZ srcX srcPi 0 a, ParityHashing.pairS srcX 0 a)) := by
  decide

theorem inj1 : Function.Injective
    (fun a => (ParityHashing.pairZ srcX srcPi 1 a, ParityHashing.pairS srcX 1 a)) := by
  decide

theorem inj4 : Function.Injective
    (fun a => (ParityHashing.pairZ srcX srcPi 4 a, ParityHashing.pairS srcX 4 a)) := by
  decide

theorem inj5 : Function.Injective
    (fun a => (ParityHashing.pairZ srcX srcPi 5 a, ParityHashing.pairS srcX 5 a)) := by
  decide

/-! ## The two non-injective pair cases: an exact 24-atom mass computation -/

theorem joint_AD_V :
    mapEntropyNats srcP (fun a => (sourceAtoms a 0, sourceAtoms a 3, chi (sourceAtoms a 1))) =
      3 * Real.log 2 + binaryNats P := by
  rw [mapEntropyNats_atom]
  norm_num [srcP, cellMass, sourceAtoms, sourceWeights, chi, Fin.sum_univ_succ, Prod.mk.injEq,
    binaryNats, P]
  simp only [log_mass_P_3, log_mass_one_sub_P_3]
  ring

theorem joint_BC_U :
    mapEntropyNats srcP (fun a => (sourceAtoms a 1, sourceAtoms a 2, chi (sourceAtoms a 0))) =
      3 * Real.log 2 + binaryNats P := by
  rw [mapEntropyNats_atom]
  norm_num [srcP, cellMass, sourceAtoms, sourceWeights, chi, Fin.sum_univ_succ, Prod.mk.injEq,
    binaryNats, P]
  simp only [log_mass_P_3, log_mass_one_sub_P_3]
  ring

/-! ## The four partner bits: exact uniformity -/

theorem cellMass_partner (i j : Fin 4) (x : Fin 4) (e : Fin 2) :
    cellMass srcP (fun a => (sourceAtoms a i, chi (sourceAtoms a j))) (x, e) =
      (sourceCell i j x e : ℝ) := by
  classical
  unfold cellMass sourceCell
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  by_cases h1 : sourceAtoms a i = x <;> by_cases h2 : chi (sourceAtoms a j) = e <;>
    simp [h1, h2]

theorem partner_entropy (i j : Fin 4)
    (huni : ∀ x : Fin 4, ∀ e : Fin 2, sourceCell i j x e = 1 / 8) :
    mapEntropyNats srcP (fun a => (sourceAtoms a i, chi (sourceAtoms a j))) =
      3 * Real.log 2 := by
  rw [mapEntropyNats_atom]
  have hcell : ∀ a : Fin 24, cellMass srcP (fun a => (sourceAtoms a i, chi (sourceAtoms a j)))
      (sourceAtoms a i, chi (sourceAtoms a j)) = 1 / 8 := by
    intro a
    rw [cellMass_partner, huni]
    norm_num
  simp only [hcell, log_eighth]
  rw [← Finset.sum_mul, srcP_sum]
  ring

/-! ## The ten conditional entropies -/

theorem crit_log : criticalRate * Real.log 2 = sourceHNats - binaryNats Q := by
  rw [criticalRate_formula, div_mul_cancel₀ _ log2_pos'.ne']

theorem side_pair_entropy_AB :
    mapEntropyNats srcP (ParityHashing.pairS srcX 0) = 3 * Real.log 2 + binaryNats Q := by
  show mapEntropyNats srcP (ParityHashing.sideInfo srcX {0, 1}) = _
  rw [side_entropy, source_entropy_AB, add_mul, div_mul_cancel₀ _ log2_pos'.ne']

/-- Numeric facts used below, from the compiled logarithm enclosures. -/
theorem numeric_facts :
    sourceHNats - binaryNats Q ≤ sourceHNats + P * Real.log 2 - binaryNats P ∧
    sourceHNats - binaryNats Q ≤ binaryNats P ∧
    sourceHNats - binaryNats Q ≤ sourceHNats - binaryNats T := by
  obtain ⟨hpL, hpU⟩ := log_P_enclosure
  obtain ⟨hqL, hqU⟩ := log_Q_enclosure
  obtain ⟨htL, htU⟩ := log_T_enclosure
  obtain ⟨hp1L, hp1U⟩ := log_one_sub_P_enclosure
  obtain ⟨hq1L, hq1U⟩ := log_one_sub_Q_enclosure
  obtain ⟨ht1L, ht1U⟩ := log_one_sub_T_enclosure
  obtain ⟨h2L, h2U⟩ := log_two_enclosure
  refine ⟨?_, ?_, ?_⟩ <;>
  · norm_num [sourceHNats, binaryNats, P, Q, T] at *
    linarith

theorem thr0 : criticalRate * Real.log 2 ≤
    ParityHashing.condEnt srcP (ParityHashing.pairZ srcX srcPi 0) (ParityHashing.pairS srcX 0) := by
  unfold ParityHashing.condEnt
  rw [entropy_of_injective inj0, side_pair_entropy_AB, crit_log]
  linarith

theorem thr1 : criticalRate * Real.log 2 ≤
    ParityHashing.condEnt srcP (ParityHashing.pairZ srcX srcPi 1) (ParityHashing.pairS srcX 1) := by
  unfold ParityHashing.condEnt
  have hs : mapEntropyNats srcP (ParityHashing.pairS srcX 1) =
      (3 - P) * Real.log 2 + binaryNats P := by
    show mapEntropyNats srcP (ParityHashing.sideInfo srcX {0, 2}) = _
    rw [side_entropy, source_entropy_AC, add_mul, div_mul_cancel₀ _ log2_pos'.ne']
  rw [entropy_of_injective inj1, hs, crit_log]
  linarith [numeric_facts.1]

theorem thr4 : criticalRate * Real.log 2 ≤
    ParityHashing.condEnt srcP (ParityHashing.pairZ srcX srcPi 4) (ParityHashing.pairS srcX 4) := by
  unfold ParityHashing.condEnt
  have hs : mapEntropyNats srcP (ParityHashing.pairS srcX 4) =
      (3 - P) * Real.log 2 + binaryNats P := by
    show mapEntropyNats srcP (ParityHashing.sideInfo srcX {1, 3}) = _
    rw [side_entropy, source_entropy_BD, add_mul, div_mul_cancel₀ _ log2_pos'.ne']
  rw [entropy_of_injective inj4, hs, crit_log]
  linarith [numeric_facts.1]

theorem thr5 : criticalRate * Real.log 2 ≤
    ParityHashing.condEnt srcP (ParityHashing.pairZ srcX srcPi 5) (ParityHashing.pairS srcX 5) := by
  unfold ParityHashing.condEnt
  have hs : mapEntropyNats srcP (ParityHashing.pairS srcX 5) =
      3 * Real.log 2 + binaryNats T := by
    show mapEntropyNats srcP (ParityHashing.sideInfo srcX {2, 3}) = _
    rw [side_entropy, source_entropy_CD, add_mul, div_mul_cancel₀ _ log2_pos'.ne']
  rw [entropy_of_injective inj5, hs, crit_log]
  linarith [numeric_facts.2.2]

theorem thr2 : criticalRate * Real.log 2 ≤
    ParityHashing.condEnt srcP (ParityHashing.pairZ srcX srcPi 2) (ParityHashing.pairS srcX 2) := by
  unfold ParityHashing.condEnt
  have hj : mapEntropyNats srcP
      (fun a => (ParityHashing.pairZ srcX srcPi 2 a, ParityHashing.pairS srcX 2 a)) =
      3 * Real.log 2 + binaryNats P := by
    rw [← joint_AD_V]
    apply mapEntropyNats_same_fibers
    intro a b
    show (srcPi 1 (srcX 1 a), ParityHashing.sideInfo srcX {0, 3} a) =
        (srcPi 1 (srcX 1 b), ParityHashing.sideInfo srcX {0, 3} b) ↔ _
    rw [Prod.mk.injEq, sideInfo_eq_iff]
    simp only [srcPi, srcX, zcast_inj, Prod.mk.injEq, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    tauto
  have hs : mapEntropyNats srcP (ParityHashing.pairS srcX 2) = 3 * Real.log 2 := by
    show mapEntropyNats srcP (ParityHashing.sideInfo srcX {0, 3}) = _
    rw [side_entropy, source_entropy_AD]
  rw [hj, hs, crit_log]
  linarith [numeric_facts.2.1]

theorem thr3 : criticalRate * Real.log 2 ≤
    ParityHashing.condEnt srcP (ParityHashing.pairZ srcX srcPi 3) (ParityHashing.pairS srcX 3) := by
  unfold ParityHashing.condEnt
  have hj : mapEntropyNats srcP
      (fun a => (ParityHashing.pairZ srcX srcPi 3 a, ParityHashing.pairS srcX 3 a)) =
      3 * Real.log 2 + binaryNats P := by
    rw [← joint_BC_U]
    apply mapEntropyNats_same_fibers
    intro a b
    show (srcPi 0 (srcX 0 a), ParityHashing.sideInfo srcX {1, 2} a) =
        (srcPi 0 (srcX 0 b), ParityHashing.sideInfo srcX {1, 2} b) ↔ _
    rw [Prod.mk.injEq, sideInfo_eq_iff]
    simp only [srcPi, srcX, zcast_inj, Prod.mk.injEq, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    tauto
  have hs : mapEntropyNats srcP (ParityHashing.pairS srcX 3) = 3 * Real.log 2 := by
    show mapEntropyNats srcP (ParityHashing.sideInfo srcX {1, 2}) = _
    rw [side_entropy, source_entropy_BC]
  rw [hj, hs, crit_log]
  linarith [numeric_facts.2.1]

/-- Partner case: `H(χ_j | X_i) = log 2 ≥ criticalRate · log 2`. -/
theorem thr_partner (jj : Fin 10) (i j : Fin 4)
    (hZ : ParityHashing.pairZ srcX srcPi jj = fun a => srcPi j (srcX j a))
    (hS : ParityHashing.pairSet jj = {i})
    (huni : ∀ x : Fin 4, ∀ e : Fin 2, sourceCell i j x e = 1 / 8)
    (hside : finiteEntropy sourceLaw {i} = 2) :
    criticalRate * Real.log 2 ≤
      ParityHashing.condEnt srcP (ParityHashing.pairZ srcX srcPi jj) (ParityHashing.pairS srcX jj) := by
  unfold ParityHashing.condEnt
  have hj : mapEntropyNats srcP
      (fun a => (ParityHashing.pairZ srcX srcPi jj a, ParityHashing.pairS srcX jj a)) =
      3 * Real.log 2 := by
    rw [← partner_entropy i j huni]
    apply mapEntropyNats_same_fibers
    intro a b
    rw [hZ]
    show (srcPi j (srcX j a), ParityHashing.sideInfo srcX (ParityHashing.pairSet jj) a) =
        (srcPi j (srcX j b), ParityHashing.sideInfo srcX (ParityHashing.pairSet jj) b) ↔ _
    rw [hS, Prod.mk.injEq, sideInfo_eq_iff]
    simp only [srcPi, srcX, zcast_inj, Prod.mk.injEq, Finset.mem_singleton, forall_eq]
    tauto
  have hs : mapEntropyNats srcP (ParityHashing.pairS srcX jj) = 2 * Real.log 2 := by
    show mapEntropyNats srcP (ParityHashing.sideInfo srcX (ParityHashing.pairSet jj)) = _
    rw [hS, side_entropy, hside]
  rw [hj, hs]
  have h1 := criticalRate_lt_one
  have h2 := log2_pos'
  nlinarith

theorem src_thresholds : ∀ j : Fin 10, criticalRate * Real.log 2 ≤
    ParityHashing.condEnt srcP (ParityHashing.pairZ srcX srcPi j) (ParityHashing.pairS srcX j) := by
  intro j
  fin_cases j
  · exact thr0
  · exact thr1
  · exact thr2
  · exact thr3
  · exact thr4
  · exact thr5
  · exact thr_partner 6 0 1 rfl rfl (fun x e => (source_partner_uniform x e).1) source_entropy_A
  · exact thr_partner 7 1 0 rfl rfl (fun x e => (source_partner_uniform x e).2.1)
      source_entropy_B
  · exact thr_partner 8 2 3 rfl rfl (fun x e => (source_partner_uniform x e).2.2.1)
      source_entropy_C
  · exact thr_partner 9 3 2 rfl rfl (fun x e => (source_partner_uniform x e).2.2.2)
      source_entropy_D

/-! ## Identification with Astra's statement -/

theorem src_sourceTable : ParityHashing.sourceTable srcP srcX = sourceProfile := by
  funext S
  unfold ParityHashing.sourceTable sourceProfile
  rw [side_entropy, mul_div_cancel_right₀ _ log2_pos'.ne']

theorem src_u34 : ParityHashing.u34 = parityRank := by
  funext S
  simp [ParityHashing.u34, parityRank, Nat.cast_min]

theorem src_shifted (R : ℝ) :
    shiftedProfile R = ParityHashing.sourceTable srcP srcX - R • ParityHashing.u34 := by
  funext S
  rw [src_sourceTable, src_u34]
  simp [shiftedProfile]

theorem aeTables_eq_almost : ParityHashing.aeTables = almostEntropicProfiles := rfl

/-- **Strict-rate membership for the actual source.** -/
theorem src_strict_rates : ∀ R : ℝ, 0 < R → R < criticalRate →
    shiftedProfile R ∈ almostEntropicProfiles := by
  intro R hR0 hRb
  rw [src_shifted, ← aeTables_eq_almost]
  exact ParityHashing.parity_hashing_mem_ae srcP_nonneg srcP_sum srcX srcPi src_xor
    src_thresholds hR0.le hRb.le

/-- **The full conditional parity-hashing result**, assembled with Astra's
`full_result_of_strict_rates`. -/
theorem full_parity_hashing_result : FullParityHashingResult :=
  full_result_of_strict_rates src_strict_rates

#print axioms src_xor
#print axioms src_thresholds
#print axioms src_strict_rates
#print axioms full_parity_hashing_result

end
end ConditionalParityHashing
