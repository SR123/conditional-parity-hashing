import PHAsymptotic

/-!
# The conditional parity-hashing construction: all fifteen coordinates

Research direction and outline: Søren Riis.
Mathematical development and verification: Astra/Codex and Claude.

Generic setting.  `Ω₁` is a finite atom space with probability mass `p₁`, the
four variables are `X i : Ω₁ → Fin m`, and `π i : Fin m → 𝔽₂` labels a parity bit
of each variable.  We assume the exact relation `χ_A + χ_B + χ_C + χ_D = 0` on
every atom.  For a binary `k × n` matrix `M` put `K_i = M χ_iⁿ` and
`W = (K_A, K_B, K_C)`.  With the ten hashing deficits `Δ_j` of `PHAsymptotic`
(six missing parity forms given a pair, four partner bits given a singleton),
we prove for every subset `S` of the four variables

  `| H(X_Sⁿ | W) - (n h(S) - k min(3,|S|) log 2) | ≤ ∑ⱼ Δⱼ`.

No probabilistic assumption beyond the parity relation is used here; the
thresholds enter only through the size of the deficits.
-/

namespace ParityHashing

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Finset SharpStability

noncomputable section

section EntropyTools

variable {Ω α α' β β' γ : Type*} [Fintype Ω] [Fintype α] [Fintype α'] [Fintype β]
  [Fintype β'] [Fintype γ]

theorem condEnt_congr_left (p : Ω → ℝ) (f : Ω → α) (f' : Ω → α') (g : Ω → β)
    (h : ∀ w v, g w = g v → (f w = f v ↔ f' w = f' v)) :
    condEnt p f g = condEnt p f' g := by
  unfold condEnt
  rw [mapEntropyNats_same_fibers p (fun w => (f w, g w)) (fun w => (f' w, g w))]
  intro w v
  constructor
  · intro hh
    obtain ⟨h1, h2⟩ := Prod.mk.inj hh
    exact Prod.ext ((h w v h2).1 h1) h2
  · intro hh
    obtain ⟨h1, h2⟩ := Prod.mk.inj hh
    exact Prod.ext ((h w v h2).2 h1) h2

theorem condEnt_congr_right (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) (g' : Ω → β')
    (h : ∀ w v, g w = g v ↔ g' w = g' v) :
    condEnt p f g = condEnt p f g' := by
  unfold condEnt
  rw [mapEntropyNats_same_fibers p g g' h,
    mapEntropyNats_same_fibers p (fun w => (f w, g w)) (fun w => (f w, g' w))]
  intro w v
  constructor
  · intro hh
    obtain ⟨h1, h2⟩ := Prod.mk.inj hh
    exact Prod.ext h1 ((h w v).1 h2)
  · intro hh
    obtain ⟨h1, h2⟩ := Prod.mk.inj hh
    exact Prod.ext h1 ((h w v).2 h2)

theorem condEnt_eq_zero_of_determined (p : Ω → ℝ) (f : Ω → α) (g : Ω → β)
    (hdet : ∀ w v, g w = g v → f w = f v) : condEnt p f g = 0 := by
  unfold condEnt
  rw [mapEntropyNats_same_fibers p (fun w => (f w, g w)) g]
  · ring
  · intro w v
    constructor
    · intro hh; exact (Prod.mk.inj hh).2
    · intro hh; exact Prod.ext (hdet w v hh) hh

/-- Conditioning on a coarser variable can only increase conditional entropy. -/
theorem condEnt_mono_of_determined (p : Ω → ℝ) (hp : ∀ w, 0 ≤ p w) (f : Ω → α)
    (g : Ω → β) (g' : Ω → β') (hdet : ∀ w v, g w = g v → g' w = g' v) :
    condEnt p f g ≤ condEnt p f g' := by
  have h := mapEntropyNats_cond_subadditive p hp f g g'
  have h1 : mapEntropyNats p (fun w => (g w, g' w)) = mapEntropyNats p g := by
    apply mapEntropyNats_same_fibers
    intro w v
    constructor
    · intro hh; exact (Prod.mk.inj hh).1
    · intro hh; exact Prod.ext hh (hdet w v hh)
  have h2 : mapEntropyNats p (fun w => (f w, (g w, g' w))) =
      mapEntropyNats p (fun w => (f w, g w)) := by
    apply mapEntropyNats_same_fibers
    intro w v
    constructor
    · intro hh
      obtain ⟨h1, h2⟩ := Prod.mk.inj hh
      exact Prod.ext h1 (Prod.mk.inj h2).1
    · intro hh
      obtain ⟨h1, h2⟩ := Prod.mk.inj hh
      exact Prod.ext h1 (Prod.ext h2 (hdet w v h2))
  unfold condEnt
  linarith

/-- Chain rule for a pair. -/
theorem condEnt_pair (p : Ω → ℝ) (a : Ω → α) (b : Ω → β) (x : Ω → γ) :
    condEnt p (fun w => (a w, b w)) x = condEnt p a x + condEnt p b (fun w => (a w, x w)) := by
  unfold condEnt
  have h : mapEntropyNats p (fun w => ((a w, b w), x w)) =
      mapEntropyNats p (fun w => (b w, (a w, x w))) := by
    apply mapEntropyNats_same_fibers
    intro w v
    constructor
    · intro hh
      obtain ⟨h1, h2⟩ := Prod.mk.inj hh
      obtain ⟨h3, h4⟩ := Prod.mk.inj h1
      exact Prod.ext h4 (Prod.ext h3 h2)
    · intro hh
      obtain ⟨h1, h2⟩ := Prod.mk.inj hh
      obtain ⟨h3, h4⟩ := Prod.mk.inj h2
      exact Prod.ext (Prod.ext h3 h1) h4
  rw [h]
  ring

/-- Chain rule for a triple. -/
theorem entropy_triple_chain (p : Ω → ℝ) (a : Ω → α) (b : Ω → β) (c : Ω → γ) :
    mapEntropyNats p (fun w => (a w, b w, c w)) =
      mapEntropyNats p a + condEnt p b a + condEnt p c (fun w => (b w, a w)) := by
  unfold condEnt
  have h : mapEntropyNats p (fun w => (a w, b w, c w)) =
      mapEntropyNats p (fun w => (c w, (b w, a w))) := by
    apply mapEntropyNats_same_fibers
    intro w v
    constructor
    · intro hh
      obtain ⟨h1, h2⟩ := Prod.mk.inj hh
      obtain ⟨h3, h4⟩ := Prod.mk.inj h2
      exact Prod.ext h4 (Prod.ext h3 h1)
    · intro hh
      obtain ⟨h1, h2⟩ := Prod.mk.inj hh
      obtain ⟨h3, h4⟩ := Prod.mk.inj h2
      exact Prod.ext h4 (Prod.ext h3 h1)
  rw [h]
  ring

/-- `H(f | g) = H(f) + H(g | f) - H(g)` rearranged: swapping the pair order. -/
theorem condEnt_swap (p : Ω → ℝ) (f : Ω → α) (g : Ω → β) :
    condEnt p f g = condEnt p g f + mapEntropyNats p f - mapEntropyNats p g := by
  unfold condEnt
  have h : mapEntropyNats p (fun w => (f w, g w)) = mapEntropyNats p (fun w => (g w, f w)) := by
    apply mapEntropyNats_same_fibers
    intro w v
    constructor
    · intro hh; obtain ⟨h1, h2⟩ := Prod.mk.inj hh; exact Prod.ext h2 h1
    · intro hh; obtain ⟨h1, h2⟩ := Prod.mk.inj hh; exact Prod.ext h2 h1
  rw [h]
  ring

end EntropyTools

theorem mapEntropyNats_const {Ω β : Type*} [Fintype Ω] [Fintype β]
    (p : Ω → ℝ) (hp1 : ∑ w, p w = 1) (b : β) :
    mapEntropyNats p (fun _ => b) = 0 := by
  classical
  rw [mapEntropyNats_atom]
  simp [cellMass,hp1]

section VecAlgebra

variable {k : ℕ}

theorem vec_solve_last {a b c a' b' c' : Vec k} (h : a + b + c = a' + b' + c') (ha : a = a')
    (hb : b = b') : c = c' := by
  subst ha hb
  exact add_left_cancel h

theorem vec_solve_mid {a b c a' b' c' : Vec k} (h : a + b + c = a' + b' + c') (ha : a = a')
    (hc : c = c') : b = b' := by
  subst ha hc
  rw [add_right_comm a b c, add_right_comm a b' c] at h
  exact add_left_cancel h

theorem vec_solve_first {a b c a' b' c' : Vec k} (h : a + b + c = a' + b' + c') (hb : b = b')
    (hc : c = c') : a = a' := by
  subst hb hc
  exact add_right_cancel (add_right_cancel h)

theorem zmod2_xor_last (a b c d : ZMod 2) (h : a + b + c + d = 0) : d = a + b + c := by
  revert a b c d; decide

end VecAlgebra

section Construction

variable {Ω₁ : Type*} [Fintype Ω₁] {m : ℕ}

/-- The coordinates in `S`, padded with `none`. -/
def sideInfo (X : Fin 4 → Ω₁ → Fin m) (S : Finset (Fin 4)) (x : Ω₁) :
    Fin 4 → Option (Fin m) :=
  fun i => if i ∈ S then some (X i x) else none

/-- Parity bit of variable `i`. -/
def parity (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2) (i : Fin 4) (x : Ω₁) :
    ZMod 2 :=
  π i (X i x)

/-- Hash key of variable `i`. -/
def key (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2) {k n : ℕ} (M : Mat k n)
    (i : Fin 4) (ω : Fin n → Ω₁) : Vec k :=
  mulVec M (blockZ (parity X π i) ω)

/-- The nonlocal auxiliary variable `W = (K_A, K_B, K_C)`. -/
def auxW (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2) {k n : ℕ} (M : Mat k n)
    (ω : Fin n → Ω₁) : Vec k × Vec k × Vec k :=
  (key X π M 0 ω, key X π M 1 ω, key X π M 2 ω)

/-- Block side information for a set of variables. -/
def blockSide (X : Fin 4 → Ω₁ → Fin m) (S : Finset (Fin 4)) {n : ℕ} (ω : Fin n → Ω₁) :
    Fin n → Fin 4 → Option (Fin m) :=
  blockS (sideInfo X S) ω

/-- The ten (binary source, side information) pairs. -/
def pairZ (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2) : Fin 10 → Ω₁ → ZMod 2 :=
  ![fun x => parity X π 0 x + parity X π 2 x, parity X π 1, parity X π 1, parity X π 0,
    parity X π 0, parity X π 0, parity X π 1, parity X π 0, parity X π 3, parity X π 2]

def pairSet : Fin 10 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}, {0}, {1}, {2}, {3}]

def pairS (X : Fin 4 → Ω₁ → Fin m) : Fin 10 → Ω₁ → Fin 4 → Option (Fin m) :=
  fun j => sideInfo X (pairSet j)

/-- The hashing deficit of pair `j` for a matrix `M`. -/
def deficit (p₁ : Ω₁ → ℝ) (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2) {k n : ℕ}
    (M : Mat k n) (j : Fin 10) : ℝ :=
  (k : ℝ) * Real.log 2 -
    condEnt (prodMass p₁ n) (fun ω => mulVec M (blockZ (pairZ X π j) ω)) (blockS (pairS X j))

variable (p₁ : Ω₁ → ℝ) (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2)

theorem key_det {k n : ℕ} (M : Mat k n) {S : Finset (Fin 4)} {i : Fin 4} (hi : i ∈ S)
    {ω ω' : Fin n → Ω₁} (h : blockSide X S ω = blockSide X S ω') :
    key X π M i ω = key X π M i ω' := by
  have hx : ∀ t, X i (ω t) = X i (ω' t) := by
    intro t
    have h1 := congrFun (congrFun h t) i
    simp only [blockSide, blockS, sideInfo, hi, ite_true] at h1
    exact Option.some.inj h1
  unfold key
  congr 1
  funext t
  simp only [blockZ, parity, hx t]

theorem key_three (hxor : ∀ x, parity X π 0 x + parity X π 1 x + parity X π 2 x +
      parity X π 3 x = 0) {k n : ℕ} (M : Mat k n) (ω : Fin n → Ω₁) :
    key X π M 3 ω = key X π M 0 ω + key X π M 1 ω + key X π M 2 ω := by
  have hb : blockZ (parity X π 3) ω =
      blockZ (parity X π 0) ω + blockZ (parity X π 1) ω + blockZ (parity X π 2) ω := by
    funext t
    exact zmod2_xor_last _ _ _ _ (hxor (ω t))
  unfold key
  rw [hb, mulVec_add, mulVec_add]

theorem key_sum02 {k n : ℕ} (M : Mat k n) (ω : Fin n → Ω₁) :
    mulVec M (blockZ (fun x => parity X π 0 x + parity X π 2 x) ω) =
      key X π M 0 ω + key X π M 2 ω := by
  unfold key
  rw [← mulVec_add]
  rfl

theorem blockSide_mono {S T : Finset (Fin 4)} (hST : S ⊆ T) {n : ℕ} {ω ω' : Fin n → Ω₁}
    (h : blockSide X T ω = blockSide X T ω') : blockSide X S ω = blockSide X S ω' := by
  funext t i
  have h1 := congrFun (congrFun h t) i
  simp only [blockSide, blockS, sideInfo] at h1 ⊢
  by_cases hi : i ∈ S
  · have hiT : i ∈ T := hST hi
    simp only [hi, hiT, ite_true] at h1 ⊢
    exact h1
  · simp [hi]

end Construction

section Bounds

variable {Ω₁ : Type*} [Fintype Ω₁] {m : ℕ}
variable {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
variable (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2)
variable (hxor : ∀ x, parity X π 0 x + parity X π 1 x + parity X π 2 x + parity X π 3 x = 0)
variable {k n : ℕ} (M : Mat k n)

include hp hp1 in
theorem deficit_nonneg (j : Fin 10) : 0 ≤ deficit p₁ X π M j :=
  hash_deficit_nonneg (prodMass p₁ n) (prodMass_nonneg hp n) (prodMass_sum hp1 n) M _ _

include hp hp1 in
theorem deficit_subsum_le (s : Finset (Fin 10)) :
    ∑ j ∈ s, deficit p₁ X π M j ≤ ∑ j, deficit p₁ X π M j :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun j _ _ => deficit_nonneg hp hp1 X π M j)

theorem condEnt_pair_eq (j : Fin 10) :
    condEnt (prodMass p₁ n) (fun ω => mulVec M (blockZ (pairZ X π j) ω))
      (blockSide X (pairSet j)) = (k : ℝ) * Real.log 2 - deficit p₁ X π M j := by
  unfold deficit
  have : blockSide X (pairSet j) = blockS (pairS X j) (n := n) := rfl
  rw [this]
  ring

include hp hp1 in
theorem entropy_W_le :
    mapEntropyNats (prodMass p₁ n) (auxW X π M) ≤ 3 * ((k : ℝ) * Real.log 2) := by
  have h := mapEntropyNats_le_log_card (prodMass p₁ n) (prodMass_nonneg hp n)
    (prodMass_sum hp1 n) (auxW X π M)
  rw [Fintype.card_prod, Fintype.card_prod, card_vec] at h
  push_cast at h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at h
  linarith

include hp hp1 in
theorem entropy_W_ge :
    3 * ((k : ℝ) * Real.log 2) -
        (deficit p₁ X π M 0 + deficit p₁ X π M 6 + deficit p₁ X π M 7) ≤
      mapEntropyNats (prodMass p₁ n) (auxW X π M) := by
  set μ := prodMass p₁ n
  have hμ0 : ∀ ω, 0 ≤ μ ω := prodMass_nonneg hp n
  have hμ1 : ∑ ω, μ ω = 1 := prodMass_sum hp1 n
  set k0 := key X π M 0
  set k1 := key X π M 1
  set k2 := key X π M 2
  have hW : mapEntropyNats μ (auxW X π M) =
      mapEntropyNats μ (fun ω => (k0 ω, k1 ω, k0 ω + k2 ω)) := by
    apply mapEntropyNats_same_fibers
    intro w v
    simp only [auxW, k0, k1, k2, Prod.mk.injEq]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h0, h1, by rw [h0, h2]⟩
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h0, h1, ?_⟩
      rw [h0] at h2
      exact add_left_cancel h2
  rw [hW, entropy_triple_chain]
  -- the three pieces
  have e7 := condEnt_pair_eq X π M (p₁ := p₁) 7
  have e6 := condEnt_pair_eq X π M (p₁ := p₁) 6
  have e0 := condEnt_pair_eq X π M (p₁ := p₁) 0
  have hz7 : (fun ω => mulVec M (blockZ (pairZ X π 7) ω)) = k0 := rfl
  have hz6 : (fun ω => mulVec M (blockZ (pairZ X π 6) ω)) = k1 := rfl
  have hz0 : (fun ω => mulVec M (blockZ (pairZ X π 0) ω)) = fun ω => k0 ω + k2 ω := by
    funext ω
    exact key_sum02 X π M ω
  rw [hz7] at e7
  rw [hz6] at e6
  rw [hz0] at e0
  have hs7 : pairSet 7 = {1} := rfl
  have hs6 : pairSet 6 = {0} := rfl
  have hs0 : pairSet 0 = {0, 1} := rfl
  rw [hs7] at e7
  rw [hs6] at e6
  rw [hs0] at e0
  have i1 : condEnt μ k0 (blockSide X {1}) ≤ mapEntropyNats μ k0 :=
    condEnt_le_entropy μ hμ0 hμ1 k0 _
  have i2 : condEnt μ k1 (blockSide X {0}) ≤ condEnt μ k1 k0 :=
    condEnt_mono_of_determined μ hμ0 k1 _ k0
      (fun w v h => key_det X π M (by decide) h)
  have i3 : condEnt μ (fun ω => k0 ω + k2 ω) (blockSide X {0, 1}) ≤
      condEnt μ (fun ω => k0 ω + k2 ω) (fun ω => (k1 ω, k0 ω)) :=
    condEnt_mono_of_determined μ hμ0 _ _ _
      (fun w v h => Prod.ext (key_det X π M (by decide) h) (key_det X π M (by decide) h))
  linarith

/-- Pair case: the hashed missing form carries all remaining uncertainty. -/
theorem pair_case (j : Fin 10) (S : Finset (Fin 4)) (hS : pairSet j = S)
    (N : (Fin n → Ω₁) → Vec k) (hN : ∀ ω, mulVec M (blockZ (pairZ X π j) ω) = N ω)
    (hfib : ∀ w v, blockSide X S w = blockSide X S v →
      (auxW X π M w = auxW X π M v ↔ N w = N v)) :
    condEnt (prodMass p₁ n) (auxW X π M) (blockSide X S) =
      (k : ℝ) * Real.log 2 - deficit p₁ X π M j := by
  rw [condEnt_congr_left _ _ N _ hfib, ← condEnt_pair_eq X π M j, hS]
  congr 1
  funext ω
  exact (hN ω).symm

include hp hp1 in
/-- Singleton case, using the partner key and the missing form of a pair. -/
theorem single_case (jp jm : Fin 10) (i : Fin 4) (T : Finset (Fin 4))
    (hjp : pairSet jp = {i}) (hjm : pairSet jm = T) (hiT : ({i} : Finset (Fin 4)) ⊆ T)
    (Kp N : (Fin n → Ω₁) → Vec k)
    (hKp : ∀ ω, mulVec M (blockZ (pairZ X π jp) ω) = Kp ω)
    (hN : ∀ ω, mulVec M (blockZ (pairZ X π jm) ω) = N ω)
    (hKdet : ∀ w v, blockSide X T w = blockSide X T v → Kp w = Kp v)
    (hfib : ∀ w v, blockSide X {i} w = blockSide X {i} v →
      (auxW X π M w = auxW X π M v ↔ (Kp w, N w) = (Kp v, N v))) :
    2 * ((k : ℝ) * Real.log 2) - (deficit p₁ X π M jp + deficit p₁ X π M jm) ≤
        condEnt (prodMass p₁ n) (auxW X π M) (blockSide X {i}) ∧
      condEnt (prodMass p₁ n) (auxW X π M) (blockSide X {i}) ≤ 2 * ((k : ℝ) * Real.log 2) := by
  set μ := prodMass p₁ n
  have hμ0 : ∀ ω, 0 ≤ μ ω := prodMass_nonneg hp n
  have hμ1 : ∑ ω, μ ω = 1 := prodMass_sum hp1 n
  rw [condEnt_congr_left _ _ (fun ω => (Kp ω, N ω)) _ hfib]
  constructor
  · rw [condEnt_pair]
    have ep := condEnt_pair_eq X π M (p₁ := p₁) jp
    have em := condEnt_pair_eq X π M (p₁ := p₁) jm
    have hKp' : (fun ω => mulVec M (blockZ (pairZ X π jp) ω)) = Kp := funext hKp
    have hN' : (fun ω => mulVec M (blockZ (pairZ X π jm) ω)) = N := funext hN
    rw [hKp', hjp] at ep
    rw [hN', hjm] at em
    have hmono : condEnt μ N (blockSide X T) ≤
        condEnt μ N (fun ω => (Kp ω, blockSide X {i} ω)) :=
      condEnt_mono_of_determined μ hμ0 N _ _
        (fun w v h => Prod.ext (hKdet w v h) (blockSide_mono X hiT h))
    linarith
  · have h := condEnt_le_log_card μ hμ0 hμ1 (fun ω => (Kp ω, N ω)) (blockSide X {i})
    rw [Fintype.card_prod, card_vec] at h
    push_cast at h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
    linarith

/-- Triple case: the auxiliary is a function of the observed blocks. -/
theorem det_case (S : Finset (Fin 4))
    (hdet : ∀ w v, blockSide X S w = blockSide X S v → auxW X π M w = auxW X π M v) :
    condEnt (prodMass p₁ n) (auxW X π M) (blockSide X S) = 0 :=
  condEnt_eq_zero_of_determined _ _ _ hdet

include hp hp1 in
theorem empty_case :
    condEnt (prodMass p₁ n) (auxW X π M) (blockSide X ∅) =
      mapEntropyNats (prodMass p₁ n) (auxW X π M) := by
  have hconst : ∀ w v : Fin n → Ω₁, blockSide X ∅ w = blockSide X ∅ v := by
    intro w v
    funext t i
    simp [blockSide, blockS, sideInfo]
  unfold condEnt
  rw [mapEntropyNats_same_fibers (prodMass p₁ n) (fun w => (auxW X π M w, blockSide X ∅ w))
    (auxW X π M)]
  · have hfun : (blockSide X ∅ (n := n)) = fun _ => (fun _ _ => none) := by
      funext w t i
      simp [blockSide, blockS, sideInfo]
    have : mapEntropyNats (prodMass p₁ n) (blockSide X ∅ (n := n)) = 0 := by
      rw [hfun]
      exact mapEntropyNats_const _ (prodMass_sum hp1 n) _
    linarith
  · intro w v
    constructor
    · intro h; exact (Prod.mk.inj h).1
    · intro h; exact Prod.ext h (hconst w v)

end Bounds

section Profile

variable {Ω₁ : Type*} [Fintype Ω₁] {m : ℕ}
variable {p₁ : Ω₁ → ℝ} (hp : ∀ x, 0 ≤ p₁ x) (hp1 : ∑ x, p₁ x = 1)
variable (X : Fin 4 → Ω₁ → Fin m) (π : Fin 4 → Fin m → ZMod 2)
variable (hxor : ∀ x, parity X π 0 x + parity X π 1 x + parity X π 2 x + parity X π 3 x = 0)
variable {k n : ℕ} (M : Mat k n)

include hp hp1 in
theorem deficit_two_le (a b : Fin 10) (hab : a ≠ b) :
    deficit p₁ X π M a + deficit p₁ X π M b ≤ ∑ j, deficit p₁ X π M j := by
  have h := deficit_subsum_le hp hp1 X π M {a, b}
  rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton] at h
  exact h

include hp hp1 in
theorem deficit_three_le (a b c : Fin 10) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    deficit p₁ X π M a + deficit p₁ X π M b + deficit p₁ X π M c ≤
      ∑ j, deficit p₁ X π M j := by
  have h := deficit_subsum_le hp hp1 X π M {a, b, c}
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton] at h
  linarith

include hp hp1 hxor in
/-- The conditional-entropy error for one subset, in all sixteen cases. -/
theorem cond_error_bound (S : Finset (Fin 4)) :
    |condEnt (prodMass p₁ n) (auxW X π M) (blockSide X S) -
        mapEntropyNats (prodMass p₁ n) (auxW X π M) +
        (k : ℝ) * ((min 3 S.card : ℕ) : ℝ) * Real.log 2| ≤ ∑ j, deficit p₁ X π M j := by
  classical
  set D := ∑ j, deficit p₁ X π M j with hD
  set HW := mapEntropyNats (prodMass p₁ n) (auxW X π M) with hHW
  set L := (k : ℝ) * Real.log 2 with hL
  have hWle := entropy_W_le hp hp1 X π M
  have hWge := entropy_W_ge hp hp1 X π M
  have hnn : ∀ j, 0 ≤ deficit p₁ X π M j := deficit_nonneg hp hp1 X π M
  have h067 := deficit_three_le hp hp1 X π M 0 6 7 (by decide) (by decide) (by decide)
  set k0 := key X π M 0 with hk0
  set k1 := key X π M 1 with hk1
  set k2 := key X π M 2 with hk2
  set k3 := key X π M 3 with hk3
  have hrel : ∀ ω, k3 ω = k0 ω + k1 ω + k2 ω := key_three X π hxor M
  have hW : ∀ w v, auxW X π M w = auxW X π M v ↔ (k0 w = k0 v ∧ k1 w = k1 v ∧ k2 w = k2 v) := by
    intro w v
    simp only [auxW, Prod.mk.injEq,hk0,hk1,hk2]
  have rel3 : ∀ w v, k3 w = k3 v → k0 w + k1 w + k2 w = k0 v + k1 v + k2 v := by
    intro w v h
    rw [← hrel, ← hrel]
    exact h
  -- the generic finish for each of the three kinds of case
  have finish_det : ∀ c : ℝ, c = 0 → (min 3 S.card : ℕ) = 3 →
      |c - HW + L * ((min 3 S.card : ℕ) : ℝ)| ≤ D := by
    intro c hc h3
    rw [hc, h3, abs_le]
    push_cast
    constructor <;> nlinarith
  have finish_pair : ∀ (c : ℝ) (j : Fin 10), c = L - deficit p₁ X π M j →
      (min 3 S.card : ℕ) = 2 → deficit p₁ X π M j ≤ D →
      |c - HW + L * ((min 3 S.card : ℕ) : ℝ)| ≤ D := by
    intro c j hc h2 hj
    rw [hc, h2, abs_le]
    push_cast
    have := hnn j
    constructor <;> nlinarith
  have finish_single : ∀ (c : ℝ) (a b : Fin 10), 2 * L - (deficit p₁ X π M a +
      deficit p₁ X π M b) ≤ c → c ≤ 2 * L → (min 3 S.card : ℕ) = 1 →
      deficit p₁ X π M a + deficit p₁ X π M b ≤ D →
      |c - HW + L * ((min 3 S.card : ℕ) : ℝ)| ≤ D := by
    intro c a b hc1 hc2 h1 hab
    rw [h1, abs_le]
    push_cast
    constructor <;> nlinarith
  have hmul : (k : ℝ) * ((min 3 S.card : ℕ) : ℝ) * Real.log 2 = L * ((min 3 S.card : ℕ) : ℝ) := by
    rw [hL]; ring
  rw [hmul]
  by_cases h0 : (0 : Fin 4) ∈ S <;> by_cases h1 : (1 : Fin 4) ∈ S <;>
    by_cases h2 : (2 : Fin 4) ∈ S <;> by_cases h3 : (3 : Fin 4) ∈ S
  -- {0,1,2,3}
  · have hS : S = {0, 1, 2, 3} := by ext i; fin_cases i <;> simp_all
    subst hS
    refine finish_det _ (det_case X π M _ (fun w v h => (hW w v).2
      ⟨key_det X π M (by decide) h, key_det X π M (by decide) h,
        key_det X π M (by decide) h⟩)) rfl
  -- {0,1,2}
  · have hS : S = {0, 1, 2} := by ext i; fin_cases i <;> simp_all
    subst hS
    refine finish_det _ (det_case X π M _ (fun w v h => (hW w v).2
      ⟨key_det X π M (by decide) h, key_det X π M (by decide) h,
        key_det X π M (by decide) h⟩)) rfl
  -- {0,1,3}
  · have hS : S = {0, 1, 3} := by ext i; fin_cases i <;> simp_all
    subst hS
    refine finish_det _ (det_case X π M _ (fun w v h => ?_)) rfl
    have e0 : k0 w = k0 v := key_det X π M (by decide) h
    have e1 : k1 w = k1 v := key_det X π M (by decide) h
    have e3 : k3 w = k3 v := key_det X π M (by decide) h
    exact (hW w v).2 ⟨e0, e1, vec_solve_last (rel3 w v e3) e0 e1⟩
  -- {0,1}
  · have hS : S = {0, 1} := by ext i; fin_cases i <;> simp_all
    subst hS
    refine finish_pair _ 0 (pair_case X π M 0 {0, 1} rfl (fun ω => k0 ω + k2 ω)
      (fun ω => key_sum02 X π M ω) (fun w v h => ?_)) rfl (by linarith [hnn 6, hnn 7])
    have e0 : k0 w = k0 v := key_det X π M (by decide) h
    have e1 : k1 w = k1 v := key_det X π M (by decide) h
    rw [hW]
    constructor
    · rintro ⟨-, -, h2⟩; rw [e0, h2]
    · intro hs
      rw [e0] at hs
      exact ⟨e0, e1, add_left_cancel hs⟩
  -- {0,2,3}
  · have hS : S = {0, 2, 3} := by ext i; fin_cases i <;> simp_all
    subst hS
    refine finish_det _ (det_case X π M _ (fun w v h => ?_)) rfl
    have e0 : k0 w = k0 v := key_det X π M (by decide) h
    have e2 : k2 w = k2 v := key_det X π M (by decide) h
    have e3 : k3 w = k3 v := key_det X π M (by decide) h
    exact (hW w v).2 ⟨e0, vec_solve_mid (rel3 w v e3) e0 e2, e2⟩
  -- {0,2}
  · have hS : S = {0, 2} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hd1 : deficit p₁ X π M 1 ≤ D := by
      have := deficit_two_le hp hp1 X π M 1 0 (by decide); linarith [hnn 0]
    refine finish_pair _ 1 (pair_case X π M 1 {0, 2} rfl k1 (fun ω => rfl)
      (fun w v h => ?_)) rfl hd1
    have e0 : k0 w = k0 v := key_det X π M (by decide) h
    have e2 : k2 w = k2 v := key_det X π M (by decide) h
    rw [hW]
    exact ⟨fun hh => hh.2.1, fun e1 => ⟨e0, e1, e2⟩⟩
  -- {0,3}
  · have hS : S = {0, 3} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hd2 : deficit p₁ X π M 2 ≤ D := by
      have := deficit_two_le hp hp1 X π M 2 0 (by decide); linarith [hnn 0]
    refine finish_pair _ 2 (pair_case X π M 2 {0, 3} rfl k1 (fun ω => rfl)
      (fun w v h => ?_)) rfl hd2
    have e0 : k0 w = k0 v := key_det X π M (by decide) h
    have e3 : k3 w = k3 v := key_det X π M (by decide) h
    rw [hW]
    exact ⟨fun hh => hh.2.1, fun e1 => ⟨e0, e1, vec_solve_last (rel3 w v e3) e0 e1⟩⟩
  -- {0}
  · have hS : S = {0} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hsub : ({0} : Finset (Fin 4)) ⊆ {0, 1} := by decide
    obtain ⟨hc1, hc2⟩ := single_case hp hp1 X π M 6 0 0 {0, 1} rfl rfl hsub k1
      (fun ω => k0 ω + k2 ω) (fun ω => rfl) (fun ω => key_sum02 X π M ω)
      (fun w v h => key_det X π M (by decide) h)
      (fun w v h => by
        have e0 : k0 w = k0 v := key_det X π M (by decide) h
        rw [hW, Prod.mk.injEq]
        constructor
        · rintro ⟨-, h1, h2⟩; exact ⟨h1, by rw [e0, h2]⟩
        · rintro ⟨h1, hs⟩
          rw [e0] at hs
          exact ⟨e0, h1, add_left_cancel hs⟩)
    exact finish_single _ 6 0 hc1 hc2 rfl
      (by have := deficit_two_le hp hp1 X π M 6 0 (by decide); linarith)
  -- {1,2,3}
  · have hS : S = {1, 2, 3} := by ext i; fin_cases i <;> simp_all
    subst hS
    refine finish_det _ (det_case X π M _ (fun w v h => ?_)) rfl
    have e1 : k1 w = k1 v := key_det X π M (by decide) h
    have e2 : k2 w = k2 v := key_det X π M (by decide) h
    have e3 : k3 w = k3 v := key_det X π M (by decide) h
    exact (hW w v).2 ⟨vec_solve_first (rel3 w v e3) e1 e2, e1, e2⟩
  -- {1,2}
  · have hS : S = {1, 2} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hd3 : deficit p₁ X π M 3 ≤ D := by
      have := deficit_two_le hp hp1 X π M 3 0 (by decide); linarith [hnn 0]
    refine finish_pair _ 3 (pair_case X π M 3 {1, 2} rfl k0 (fun ω => rfl)
      (fun w v h => ?_)) rfl hd3
    have e1 : k1 w = k1 v := key_det X π M (by decide) h
    have e2 : k2 w = k2 v := key_det X π M (by decide) h
    rw [hW]
    exact ⟨fun hh => hh.1, fun e0 => ⟨e0, e1, e2⟩⟩
  -- {1,3}
  · have hS : S = {1, 3} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hd4 : deficit p₁ X π M 4 ≤ D := by
      have := deficit_two_le hp hp1 X π M 4 0 (by decide); linarith [hnn 0]
    refine finish_pair _ 4 (pair_case X π M 4 {1, 3} rfl k0 (fun ω => rfl)
      (fun w v h => ?_)) rfl hd4
    have e1 : k1 w = k1 v := key_det X π M (by decide) h
    have e3 : k3 w = k3 v := key_det X π M (by decide) h
    rw [hW]
    exact ⟨fun hh => hh.1, fun e0 => ⟨e0, e1, vec_solve_last (rel3 w v e3) e0 e1⟩⟩
  -- {1}
  · have hS : S = {1} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hsub : ({1} : Finset (Fin 4)) ⊆ {0, 1} := by decide
    obtain ⟨hc1, hc2⟩ := single_case hp hp1 X π M 7 0 1 {0, 1} rfl rfl hsub k0
      (fun ω => k0 ω + k2 ω) (fun ω => rfl) (fun ω => key_sum02 X π M ω)
      (fun w v h => key_det X π M (by decide) h)
      (fun w v h => by
        have e1 : k1 w = k1 v := key_det X π M (by decide) h
        rw [hW, Prod.mk.injEq]
        constructor
        · rintro ⟨h0, -, h2⟩; exact ⟨h0, by rw [h0, h2]⟩
        · rintro ⟨h0, hs⟩
          rw [h0] at hs
          exact ⟨h0, e1, add_left_cancel hs⟩)
    exact finish_single _ 7 0 hc1 hc2 rfl
      (by have := deficit_two_le hp hp1 X π M 7 0 (by decide); linarith)
  -- {2,3}
  · have hS : S = {2, 3} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hd5 : deficit p₁ X π M 5 ≤ D := by
      have := deficit_two_le hp hp1 X π M 5 0 (by decide); linarith [hnn 0]
    refine finish_pair _ 5 (pair_case X π M 5 {2, 3} rfl k0 (fun ω => rfl)
      (fun w v h => ?_)) rfl hd5
    have e2 : k2 w = k2 v := key_det X π M (by decide) h
    have e3 : k3 w = k3 v := key_det X π M (by decide) h
    rw [hW]
    exact ⟨fun hh => hh.1, fun e0 => ⟨e0, vec_solve_mid (rel3 w v e3) e0 e2, e2⟩⟩
  -- {2}
  · have hS : S = {2} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hsub : ({2} : Finset (Fin 4)) ⊆ {2, 3} := by decide
    obtain ⟨hc1, hc2⟩ := single_case hp hp1 X π M 8 5 2 {2, 3} rfl rfl hsub k3
      k0 (fun ω => rfl) (fun ω => rfl)
      (fun w v h => key_det X π M (by decide) h)
      (fun w v h => by
        have e2 : k2 w = k2 v := key_det X π M (by decide) h
        rw [hW, Prod.mk.injEq]
        constructor
        · rintro ⟨h0, h1, h2⟩
          refine ⟨?_, h0⟩
          rw [hrel, hrel, h0, h1, h2]
        · rintro ⟨e3, h0⟩
          exact ⟨h0, vec_solve_mid (rel3 w v e3) h0 e2, e2⟩)
    exact finish_single _ 8 5 hc1 hc2 rfl
      (by have := deficit_two_le hp hp1 X π M 8 5 (by decide); linarith)
  -- {3}
  · have hS : S = {3} := by ext i; fin_cases i <;> simp_all
    subst hS
    have hsub : ({3} : Finset (Fin 4)) ⊆ {2, 3} := by decide
    obtain ⟨hc1, hc2⟩ := single_case hp hp1 X π M 9 5 3 {2, 3} rfl rfl hsub k2
      k0 (fun ω => rfl) (fun ω => rfl)
      (fun w v h => key_det X π M (by decide) h)
      (fun w v h => by
        have e3 : k3 w = k3 v := key_det X π M (by decide) h
        rw [hW, Prod.mk.injEq]
        constructor
        · rintro ⟨h0, -, h2⟩; exact ⟨h2, h0⟩
        · rintro ⟨e2, h0⟩
          exact ⟨h0, vec_solve_mid (rel3 w v e3) h0 e2, e2⟩)
    exact finish_single _ 9 5 hc1 hc2 rfl
      (by have := deficit_two_le hp hp1 X π M 9 5 (by decide); linarith)
  -- ∅
  · have hS : S = ∅ := by ext i; fin_cases i <;> simp_all
    subst hS
    rw [empty_case hp hp1 X π M]
    simpa [hHW,hD] using (Finset.sum_nonneg (fun j (_ : j ∈ (univ : Finset (Fin 10))) => hnn j))

include hp hp1 hxor in
/-- **All fifteen coordinates.**  For every subset `S`,
`|H(X_Sⁿ | W) - (n h(S) - k min(3,|S|) log 2)| ≤ ∑ⱼ Δⱼ` (natural logarithms). -/
theorem block_profile_bound (S : Finset (Fin 4)) :
    |condEnt (prodMass p₁ n) (blockSide X S) (auxW X π M) -
        ((n : ℝ) * mapEntropyNats p₁ (sideInfo X S) -
          (k : ℝ) * ((min 3 S.card : ℕ) : ℝ) * Real.log 2)| ≤ ∑ j, deficit p₁ X π M j := by
  have hswap := condEnt_swap (prodMass p₁ n) (blockSide X S) (auxW X π M)
  have hblock : mapEntropyNats (prodMass p₁ n) (blockSide X S (n := n)) =
      n * mapEntropyNats p₁ (sideInfo X S) :=
    mapEntropyNats_prod_coord hp hp1 n (sideInfo X S)
  have h := cond_error_bound hp hp1 X π hxor M S
  rw [hswap, hblock]
  have heq : condEnt (prodMass p₁ n) (auxW X π M) (blockSide X S) +
      ↑n * mapEntropyNats p₁ (sideInfo X S) - mapEntropyNats (prodMass p₁ n) (auxW X π M) -
      (↑n * mapEntropyNats p₁ (sideInfo X S) - ↑k * ↑(min 3 S.card) * Real.log 2) =
      condEnt (prodMass p₁ n) (auxW X π M) (blockSide X S) -
        mapEntropyNats (prodMass p₁ n) (auxW X π M) + ↑k * ↑(min 3 S.card) * Real.log 2 := by
    ring
  rw [heq]
  exact h

end Profile

end
end ParityHashing
