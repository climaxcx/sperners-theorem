import Mathlib

namespace Sperners

abbrev Family (n : ℕ) :=
  Finset (Finset (Fin n))

abbrev IsSubsetChain {n} (C : Family n) :=
  IsChain (· ⊆ ·) (C : Set (Finset (Fin n)))

abbrev IsSubsetAntichain {n} (C : Family n) :=
  IsAntichain (· ⊆ ·) (C : Set (Finset (Fin n)))

abbrev Layer (n k : ℕ) : Family n :=
  (Finset.univ : Finset (Fin n)).powersetCard k

def incidences (𝒜 : Family n) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (𝒜.product (Finset.shadow 𝒜)).filter
    (fun p => p.2 ⊆ p.1)

def fiberOver {n} (𝒜 : Family n) (A : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (Finset.shadow 𝒜).filter (fun B => B ⊆ A)

lemma erase_mem_fiber
    (a : Fin n)
    (ha : a ∈ A)
    (hA : A ∈ 𝒜) :
    A.erase a ∈ fiberOver 𝒜 A := by
  sorry

lemma exists_unique_erased
    (B : Finset (Fin n))
    (hB : B ∈ fiberOver 𝒜 A) :
    ∃! a,
      a ∈ A ∧
      B = A.erase a := by
  sorry

lemma card_fiberOver
    (hA : A ∈ 𝒜)
    (hCard : A.card = r) :
    (fiberOver 𝒜 A).card = r := by
  sorry

lemma CountingA {𝒜 : Family n}
    (h𝒜 : 𝒜 ⊆ Layer n r) :
    (incidences 𝒜).card = 𝒜.card * r := by
  sorry

lemma CountingB {𝒜 : Family n}
    (h𝒜 : 𝒜 ⊆ Layer n r) :
    (incidences 𝒜).card ≤ 𝒜.shadow.card * (n - (r - 1)) := by
  sorry

theorem local_lym_mul {n r} (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) :
    𝒜.shadow.card * (n - (r - 1)) ≥ 𝒜.card * r := by
  nth_rw 2 [← CountingA]
  · rw[ge_iff_le]
    exact CountingB h𝒜
  exact h𝒜




theorem local_lym {n r} (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) (hr : r ≠ 0) :
    (𝒜.shadow.card : ℚ) / (Layer n (r-1)).card ≥ 𝒜.card / ↑(Layer n r).card := by
  sorry


theorem lym {n} (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    ∑ r ∈ Finset.range (n + 1), (𝒜.slice r).card / (n.choose r) ≤ 1 := by
  sorry

end Sperners
