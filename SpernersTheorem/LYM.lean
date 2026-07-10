import Mathlib

namespace Sperners

abbrev Family (n : ℕ) :=
  Finset (Finset (Fin n))

abbrev IsSubsetChain {n} (C : Family n) :=
  IsChain (· ⊆ ·) (C : Set (Finset (Fin n)))

abbrev IsSubsetAntichain {n} (C : Family n) :=
  IsAntichain (· ⊆ ·) (C : Set (Finset (Fin n)))

def Layer (n k : ℕ) : Family n :=
  (Finset.univ : Finset (Fin n)).powersetCard k

theorem local_lym_mul {n r} (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) :
    𝒜.shadow.card * r ≥ 𝒜.card * (n - (r - 1)) := by
  sorry

theorem local_lym {n r} (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) :
    𝒜.shadow.card / (Layer n (r-1)).card ≥ 𝒜.card / (Layer n r).card := by
  sorry


theorem lym {n} (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    ∑ r ∈ Finset.range (n + 1), (𝒜.slice r).card / (n.choose r) ≤ 1 := by
  sorry

end Sperners
