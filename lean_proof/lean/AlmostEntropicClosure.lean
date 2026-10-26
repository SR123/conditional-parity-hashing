import Balanced
import Mathlib

/-!
The actual topological closure of finite-law entropy profiles.
Only these definitions and elementary inclusion lemmas are needed here.
The definitions are unchanged from the original checked development;
unrelated stability and Gaussian theorems have been omitted.
-/

namespace SharpStability

open Set
open scoped Topology

noncomputable section

def finiteEntropyProfiles : Set EntropyTable :=
  {h | ∃ (n : ℕ) (P : FiniteLaw4 n), h = finiteEntropy P}

def almostEntropicProfiles : Set EntropyTable := closure finiteEntropyProfiles

theorem finite_profile_mem {n : ℕ} (P : FiniteLaw4 n) :
    finiteEntropy P ∈ finiteEntropyProfiles := ⟨n, P, rfl⟩

theorem finite_profiles_subset_almost :
    finiteEntropyProfiles ⊆ almostEntropicProfiles := subset_closure

theorem finite_profile_almost {n : ℕ} (P : FiniteLaw4 n) :
    finiteEntropy P ∈ almostEntropicProfiles :=
  finite_profiles_subset_almost (finite_profile_mem P)

end
end SharpStability
