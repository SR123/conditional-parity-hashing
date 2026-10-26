import PHConstruction
import Balanced

/-!
# The actual closure of finite entropy tables is a convex cone

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

We work with the reference library's concrete objects: `FiniteLaw4 N`,
`finiteEntropy` (bits) and the topological closure of the set of finite
entropy tables.  We prove
* push-forwards of finite probability spaces give finite laws, with the
  expected entropies;
* independent products add entropy tables;
* the rare-flag construction scales a table by `α ∈ (0,1)` up to a vanishing
  flag term;
* hence the closure is closed under addition and nonnegative scaling;
* conditional entropy profiles are nonnegative combinations of finite tables.
-/

namespace ParityHashing

open Finset SharpStability Filter Topology

noncomputable section

/-- The set of finite four-variable entropy tables (identical to the reference
library's `finiteEntropyProfiles`). -/
def finiteTables : Set EntropyTable := {h | ∃ (n : ℕ) (P : FiniteLaw4 n), h = finiteEntropy P}

/-- The actual almost-entropic closure (identical to `almostEntropicProfiles`). -/
def aeTables : Set EntropyTable := closure finiteTables

section Push

variable {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]

theorem cellMass_comp (p : Ω → ℝ) (F : Ω → α) (G : α → β) (y : β) :
    cellMass (cellMass p F) G y = cellMass p (fun x => G (F x)) y := by
  classical
  unfold cellMass
  have h : ∀ a : α, (if G a = y then ∑ x, (if F x = a then p x else 0) else 0) =
      ∑ x, (if F x = a then (if G a = y then p x else 0) else 0) := by
    intro a
    by_cases hG : G a = y
    · simp only [hG, ite_true]
    · simp only [hG, ite_false, ite_self, Finset.sum_const_zero]
  simp only [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [eq_comm]

theorem mapEntropyNats_comp (p : Ω → ℝ) (F : Ω → α) (G : α → β) :
    mapEntropyNats (cellMass p F) G = mapEntropyNats p (fun x => G (F x)) := by
  unfold mapEntropyNats
  simp only [cellMass_comp]

/-- A finite law from a finite probability space and four coordinates. -/
def pushLaw4 (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1) {N : ℕ}
    (Y : Fin 4 → Ω → Fin N) : FiniteLaw4 N where
  mass := cellMass p (fun x i => Y i x)
  mass_nonneg := cellMass_nonneg hp _
  mass_sum := by rw [cellMass_total, hp1]

theorem finiteEntropy_pushLaw4 (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1) {N : ℕ}
    (Y : Fin 4 → Ω → Fin N) (S : Finset (Fin 4)) :
    finiteEntropy (pushLaw4 p hp hp1 Y) S * Real.log 2 =
      mapEntropyNats p (fun x => fun i : S => Y i x) := by
  rw [finiteEntropy_eq_mapEntropyNats]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [div_mul_cancel₀ _ hlog]
  exact mapEntropyNats_comp p (fun x i => Y i x) (fun w => fun i : S => w i)

theorem pushLaw4_mem (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1) {N : ℕ}
    (Y : Fin 4 → Ω → Fin N) : finiteEntropy (pushLaw4 p hp hp1 Y) ∈ finiteTables :=
  ⟨N, _, rfl⟩


end Push

section Independence

variable {Ω Ω' α β : Type*} [Fintype Ω] [Fintype Ω'] [Fintype α] [Fintype β]

theorem cellMass_indep (p : Ω → ℝ) (q : Ω' → ℝ) (f : Ω → α) (g : Ω' → β) (a : α) (b : β) :
    cellMass (fun xy : Ω × Ω' => p xy.1 * q xy.2) (fun xy => (f xy.1, g xy.2)) (a, b) =
      cellMass p f a * cellMass q g b := by
  classical
  unfold cellMass
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hf : f x = a <;> by_cases hg : g y = b <;> simp [hf, hg]

/-- Entropy of independent coordinates adds. -/
theorem mapEntropyNats_indep {p : Ω → ℝ} {q : Ω' → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ y, q y = 1) (f : Ω → α) (g : Ω' → β) :
    mapEntropyNats (fun xy : Ω × Ω' => p xy.1 * q xy.2) (fun xy => (f xy.1, g xy.2)) =
      mapEntropyNats p f + mapEntropyNats q g := by
  classical
  rw [mapEntropyNats_atom, mapEntropyNats_atom, mapEntropyNats_atom]
  simp only [cellMass_indep]
  have hterm : ∀ xy : Ω × Ω', p xy.1 * q xy.2 *
      Real.log (cellMass p f (f xy.1) * cellMass q g (g xy.2)) =
      q xy.2 * (p xy.1 * Real.log (cellMass p f (f xy.1))) +
        p xy.1 * (q xy.2 * Real.log (cellMass q g (g xy.2))) := by
    rintro ⟨x, y⟩
    by_cases h0 : p x * q y = 0
    · rcases mul_eq_zero.1 h0 with h | h <;> simp [h]
    · have hpx : 0 < p x := lt_of_le_of_ne (hp x) (fun h => h0 (by rw [← h]; ring))
      have hqy : 0 < q y := lt_of_le_of_ne (hq y) (fun h => h0 (by rw [← h]; ring))
      have hc1 : 0 < cellMass p f (f x) := hpx.trans_le (mass_le_cellMass hp f x)
      have hc2 : 0 < cellMass q g (g y) := hqy.trans_le (mass_le_cellMass hq g y)
      simp only
      rw [Real.log_mul hc1.ne' hc2.ne']
      ring
  simp only [hterm, Fintype.sum_prod_type, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => q y * (p x * Real.log (cellMass p f (f x))))]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hp1, hq1, one_mul]
  ring

end Independence

section ConeOps

/-- Independent product of two finite laws. -/
def prodLaw4 {a b : ℕ} (P : FiniteLaw4 a) (Q : FiniteLaw4 b) : FiniteLaw4 (a * b) :=
  pushLaw4 (fun xy : Word4 a × Word4 b => P.mass xy.1 * Q.mass xy.2)
    (fun xy => mul_nonneg (P.mass_nonneg _) (Q.mass_nonneg _))
    (by rw [Fintype.sum_prod_type]; simp [← Finset.mul_sum, ← Finset.sum_mul, P.mass_sum,
      Q.mass_sum])
    (fun i xy => finProdFinEquiv (xy.1 i, xy.2 i))

theorem finiteEntropy_prodLaw4 {a b : ℕ} (P : FiniteLaw4 a) (Q : FiniteLaw4 b) :
    finiteEntropy (prodLaw4 P Q) = finiteEntropy P + finiteEntropy Q := by
  funext S
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  apply mul_right_cancel₀ hlog
  rw [Pi.add_apply, add_mul, prodLaw4, finiteEntropy_pushLaw4]
  rw [finiteEntropy_eq_mapEntropyNats, finiteEntropy_eq_mapEntropyNats,
    div_mul_cancel₀ _ hlog, div_mul_cancel₀ _ hlog]
  rw [← mapEntropyNats_indep P.mass_nonneg Q.mass_nonneg P.mass_sum Q.mass_sum]
  apply mapEntropyNats_same_fibers
  intro w v
  constructor
  · intro h
    have h' : ∀ i : S, (w.1 i, w.2 i) = (v.1 i, v.2 i) := by
      intro i
      have := congrFun h i
      exact finProdFinEquiv.injective this
    refine Prod.ext ?_ ?_
    · funext i; exact (Prod.mk.inj (h' i)).1
    · funext i; exact (Prod.mk.inj (h' i)).2
  · intro h
    funext i
    have h1 := congrFun (Prod.mk.inj h).1 i
    have h2 := congrFun (Prod.mk.inj h).2 i
    rw [h1, h2]

theorem finiteTables_add {f g : EntropyTable} (hf : f ∈ finiteTables) (hg : g ∈ finiteTables) :
    f + g ∈ finiteTables := by
  obtain ⟨a, P, rfl⟩ := hf
  obtain ⟨b, Q, rfl⟩ := hg
  exact ⟨a * b, prodLaw4 P Q, (finiteEntropy_prodLaw4 P Q).symm⟩

theorem finiteTables_nsmul {f : EntropyTable} (hf : f ∈ finiteTables) :
    ∀ j : ℕ, 0 < j → (j : ℝ) • f ∈ finiteTables := by
  intro j hj
  induction j with
  | zero => exact absurd hj (lt_irrefl 0)
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simpa using hf
    · have := finiteTables_add (ih hpos) hf
      have heq : ((j + 1 : ℕ) : ℝ) • f = (j : ℝ) • f + f := by
        push_cast; rw [add_smul, one_smul]
      rw [heq]; exact this

/-- The binary entropy function in bits. -/
def hbBits (α : ℝ) : ℝ := (Real.negMulLog α + Real.negMulLog (1 - α)) / Real.log 2

/-- The flag indicator table: one bit of flag entropy on every nonempty set. -/
def flagTable : EntropyTable := fun S => if S = ∅ then 0 else 1

/-- Rare-flag law: with probability `α` reveal a sample of `P`, otherwise a constant. -/
def flagLaw4 {a : ℕ} (P : FiniteLaw4 a) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    FiniteLaw4 (a + 1) :=
  pushLaw4 (fun o : Option (Word4 a) => o.elim (1 - α) (fun x => α * P.mass x))
    (fun o => by
      cases o with
      | none => simp only [Option.elim_none]; linarith
      | some x => simp only [Option.elim_some]; exact mul_nonneg hα0 (P.mass_nonneg x))
    (by
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some]
      rw [← Finset.mul_sum, P.mass_sum]
      ring)
    (fun i o => o.elim (Fin.last a) (fun x => Fin.castSucc (x i)))

theorem mapEntropyNats_restrict_empty {Ω γ : Type*} [Fintype Ω] [Fintype γ] (p : Ω → ℝ)
    (hp1 : ∑ w, p w = 1) (F : Ω → Fin 4 → γ) :
    mapEntropyNats p (fun x => fun i : (∅ : Finset (Fin 4)) => F x i) = 0 := by
  have hconst : (fun x => fun i : (∅ : Finset (Fin 4)) => F x i) =
      fun _ => fun i : (∅ : Finset (Fin 4)) => absurd i.2 (Finset.notMem_empty _) := by
    funext x i
    exact absurd i.2 (Finset.notMem_empty _)
  rw [hconst]
  exact mapEntropyNats_const p hp1 _

theorem finiteEntropy_flagLaw4 {a : ℕ} (P : FiniteLaw4 a) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    finiteEntropy (flagLaw4 P hα0.le hα1.le) = hbBits α • flagTable + α • finiteEntropy P := by
  classical
  funext S
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  apply mul_right_cancel₀ hlog
  rw [flagLaw4, finiteEntropy_pushLaw4]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, flagTable, hbBits]
  rw [finiteEntropy_eq_mapEntropyNats]
  set p : Option (Word4 a) → ℝ := fun o => o.elim (1 - α) (fun x => α * P.mass x) with hp
  have hp1 : ∑ o, p o = 1 := by
    rw [Fintype.sum_option]
    simp only [hp, Option.elim_none, Option.elim_some]
    rw [← Finset.mul_sum, P.mass_sum]
    ring
  by_cases hS : S = ∅
  · subst hS
    rw [mapEntropyNats_restrict_empty p hp1 (fun o i => o.elim (Fin.last a) (fun x => Fin.castSucc (x i))),
      mapEntropyNats_restrict_empty P.mass P.mass_sum (fun w i => w i)]
    simp
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.2 hS
    simp only [hS, ite_false, mul_one]
    set F : Option (Word4 a) → (S → Fin (a + 1)) := fun o => fun i : S =>
        o.elim (Fin.last a) (fun x => Fin.castSucc (x i)) with hF
    set G : Word4 a → (S → Fin a) := fun w => fun i : S => w i with hG
    have hnone_ne : ∀ x : Word4 a, F (some x) ≠ F none := by
      intro x h
      have := congrFun h ⟨i₀, hi₀⟩
      simp only [hF, Option.elim_none, Option.elim_some] at this
      exact (Fin.castSucc_lt_last (x i₀)).ne this
    have hsome_eq : ∀ x y : Word4 a, F (some x) = F (some y) ↔ G x = G y := by
      intro x y
      constructor
      · intro h; funext i
        have := congrFun h i
        simp only [hF, Option.elim_some] at this
        exact Fin.castSucc_injective _ this
      · intro h; funext i
        have := congrFun h i
        simp only [hF, hG, Option.elim_some] at this ⊢
        rw [this]
    have hcell_none : cellMass p F (F none) = 1 - α := by
      rw [cellMass_explicit, Fintype.sum_option]
      simp [hnone_ne,hp]
    have hcell_some : ∀ x : Word4 a,
        cellMass p F (F (some x)) = α * cellMass P.mass G (G x) := by
      intro x
      unfold cellMass
      rw [Fintype.sum_option, Finset.mul_sum]
      have hn : ¬ F none = F (some x) := fun h => hnone_ne x h.symm
      simp only [hn, ite_false, zero_add]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : G y = G x
      · simp [(hsome_eq y x).2 hy, hy, hp]
      · have hy' : ¬ F (some y) = F (some x) := fun h => hy ((hsome_eq y x).1 h)
        simp [hy', hy]
    rw [mapEntropyNats_atom, mapEntropyNats_atom, Fintype.sum_option]
    simp only [hcell_none, hcell_some]
    have hterm : ∀ x : Word4 a, p (some x) * Real.log (α * cellMass P.mass G (G x)) =
        α * P.mass x * Real.log α + α * (P.mass x * Real.log (cellMass P.mass G (G x))) := by
      intro x
      simp only [hp, Option.elim_some]
      by_cases h0 : P.mass x = 0
      · simp [h0]
      · have hpos : 0 < P.mass x := lt_of_le_of_ne (P.mass_nonneg x) (Ne.symm h0)
        have hc : 0 < cellMass P.mass G (G x) :=
          hpos.trans_le (mass_le_cellMass P.mass_nonneg G x)
        rw [Real.log_mul hα0.ne' hc.ne']
        ring
    simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, P.mass_sum]
    simp only [hp, Option.elim_none, Real.negMulLog]
    field_simp
    <;> ring

theorem tendsto_hbBits_zero : Tendsto hbBits (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun α : ℝ => (Real.negMulLog α + Real.negMulLog (1 - α)) / Real.log 2) := by
    have h1 := Real.continuous_negMulLog
    exact ((h1.add (h1.comp (continuous_const.sub continuous_id)))).div_const _
  have hcont : Continuous hbBits := hc
  have hzero : hbBits 0 = 0 := by simp [hbBits,Real.negMulLog]
  have ht := hcont.tendsto 0
  rw [hzero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

theorem zero_mem_finiteTables : (0 : EntropyTable) ∈ finiteTables := by
  have hsum : ∑ _w : Word4 1, (1 : ℝ) = 1 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
  refine ⟨1, ⟨fun _ => 1, fun _ => zero_le_one, hsum⟩, ?_⟩
  funext S
  rw [finiteEntropy_eq_mapEntropyNats]
  have hconst : (fun w : Word4 1 => fun i : S => w i) = fun _ => fun _ : S => (0 : Fin 1) := by
    funext w i
    exact Subsingleton.elim _ _
  rw [hconst, mapEntropyNats_const _ hsum]
  simp

/-- Nonnegative multiples of finite tables are almost entropic. -/
theorem smul_finite_mem_ae {f : EntropyTable} (hf : f ∈ finiteTables) {t : ℝ} (ht : 0 ≤ t) :
    t • f ∈ aeTables := by
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    rw [zero_smul]
    exact subset_closure zero_mem_finiteTables
  set g : ℕ → EntropyTable := fun j =>
    hbBits (t / ((j : ℝ) + t)) • flagTable + (t / ((j : ℝ) + t)) • ((j : ℝ) • f) with hg
  have hmem : ∀ j : ℕ, 1 ≤ j → g j ∈ finiteTables := by
    intro j hj
    obtain ⟨N, Q, hQ⟩ := finiteTables_nsmul hf j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hα0 : 0 < t / ((j : ℝ) + t) := by positivity
    have hα1 : t / ((j : ℝ) + t) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    refine ⟨N + 1, flagLaw4 Q hα0.le hα1.le, ?_⟩
    rw [finiteEntropy_flagLaw4 Q hα0 hα1, ← hQ]
  have hden : Tendsto (fun j : ℕ => (j : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_right _ t tendsto_natCast_atTop_atTop
  have hα : Tendsto (fun j : ℕ => t / ((j : ℝ) + t)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨tendsto_const_nhds.div_atTop hden, Eventually.of_forall (fun j => ?_)⟩
    simp only [Set.mem_Ioi]
    positivity
  have h1 : Tendsto (fun j : ℕ => hbBits (t / ((j : ℝ) + t)) • flagTable) atTop
      (𝓝 ((0 : ℝ) • flagTable)) :=
    (tendsto_hbBits_zero.comp hα).smul_const flagTable
  have h2 : Tendsto (fun j : ℕ => (t / ((j : ℝ) + t)) • ((j : ℝ) • f)) atTop (𝓝 (t • f)) := by
    have hrw : (fun j : ℕ => (t / ((j : ℝ) + t)) • ((j : ℝ) • f)) =
        fun j : ℕ => (t * ((j : ℝ) / ((j : ℝ) + t))) • f := by
      funext j
      rw [smul_smul]
      congr 1
      ring
    rw [hrw]
    have h3 := ((tendsto_natCast_div_add_atTop t).const_mul t).smul_const f
    simpa using h3
  have hlim : Tendsto g atTop (𝓝 (t • f)) := by
    have := h1.add h2
    simpa [hg] using this
  exact mem_closure_of_tendsto hlim (eventually_atTop.2 ⟨1, hmem⟩)

theorem ae_add {f g : EntropyTable} (hf : f ∈ aeTables) (hg : g ∈ aeTables) :
    f + g ∈ aeTables :=
  map_mem_closure₂ continuous_add hf hg (fun a ha b hb => finiteTables_add ha hb)

theorem ae_smul {f : EntropyTable} (hf : f ∈ aeTables) {t : ℝ} (ht : 0 ≤ t) :
    t • f ∈ aeTables := by
  have h := map_mem_closure (continuous_const_smul t) hf
    (fun x hx => smul_finite_mem_ae hx ht)
  rwa [aeTables, closure_closure] at h

theorem ae_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → EntropyTable)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hf : ∀ i ∈ s, f i ∈ aeTables) :
    ∑ i ∈ s, c i • f i ∈ aeTables := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (0 : EntropyTable) ∈ closure finiteTables
    exact subset_closure zero_mem_finiteTables
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ae_add (ae_smul (hf a (Finset.mem_insert_self a s)) (hc a (Finset.mem_insert_self a s)))
      (ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end ConeOps

end
end ParityHashing
