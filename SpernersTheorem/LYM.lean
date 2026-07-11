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

theorem mem_layer_card (𝒜 : Family n)
    (A : Finset (Fin n))
    (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) (hlay : 𝒜 ⊆ Layer n r) :
    A.card = B.card := by
  rw[Layer] at hlay
  have : A ∈ Finset.powersetCard r Finset.univ := by
    exact Finset.mem_def.mpr (hlay hA)
  have : B ∈ Finset.powersetCard r Finset.univ := by
    exact Finset.mem_def.mpr (hlay hB)
  simp_all only [Finset.mem_powersetCard, Finset.subset_univ, true_and]

theorem fiber_layer_eq (𝒜 : Family n) (A : Finset (Fin n)) (hA : A ∈ 𝒜) (hlay : 𝒜 ⊆ Layer n r) :
    fiberOver 𝒜 A = ({A} : Family n).shadow := by
  refine Finset.ext_iff.mpr ?_
  rw[fiberOver]
  intro B
  refine Iff.intro ?_ ?_
  · intro h
    rw[Finset.mem_shadow_iff_exists_mem_card_add_one]
    simp_all only [Finset.mem_filter, Finset.mem_singleton, exists_eq_left, true_and]
    obtain ⟨left, right⟩ := h
    rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at left
    rcases left with ⟨C, hC, hBC, hcard⟩
    have hcardA_eq_cardC : A.card = C.card := by
      exact mem_layer_card 𝒜 A hA hC hlay
    rw[hcardA_eq_cardC]
    exact hcard
  intro hB
  rw[Finset.mem_filter]
  rw[Finset.mem_shadow_iff] at hB
  rcases hB with ⟨C, hC, a, haC, hCeaB⟩
  rw[Finset.mem_singleton] at hC
  refine And.intro ?_ ?_
  · rw[←hCeaB, hC]
    refine Finset.erase_mem_shadow ?_ ?_
    · exact hA
    subst hC hCeaB
    simp_all only
  subst hC hCeaB
  exact Finset.erase_subset a C



theorem fiber_equiv (𝒜 : Family n) (hA : A ∈ 𝒜) (hlay : 𝒜 ⊆ Layer n r) :
    ∀ B ∈ fiberOver 𝒜 A, ∃! a, a ∈ A ∧ A.erase a = B := by
  intro B hB
  rw[fiber_layer_eq 𝒜 A hA hlay, Finset.mem_shadow_iff] at hB
  rcases hB with ⟨C, hC, a, haC, h⟩
  have : A = C := by
    subst h
    simp_all only [Finset.mem_singleton]
  refine ExistsUnique.intro a ?_ ?_
  · subst h this
    simp_all only [Finset.mem_singleton, and_self]
  intro b ⟨left, right⟩
  subst this h
  exact (Finset.erase_inj A left).mp right




theorem card_fiber (𝒜 : Family n) (hlay : 𝒜 ⊆ Layer n r) (hA𝒜 : A ∈ 𝒜) :
    (fiberOver 𝒜 A).card = A.card := by
  apply Eq.symm
  refine Finset.card_bij ?_ (fun a ↦ ?_) ?_ ?_
  · intro a hA
    exact A.erase a
  · intro hA
    rw[fiberOver]
    simp only [Finset.mem_filter]
    refine And.symm ⟨?_, ?_⟩
    · exact Finset.erase_subset a A
    exact Finset.erase_mem_shadow hA𝒜 hA
  · intro a hA b hB h
    exact (Finset.erase_inj A hA).mp h
  intro B hB
  obtain ha := (fiber_equiv 𝒜 hA𝒜 hlay B hB)
  obtain ⟨a, left, _⟩ := ha
  refine Exists.intro a ?_
  refine Exists.intro ?_ ?_
  · exact left.left
  exact left.right



theorem card_layer :
    (Layer n k).card = n.choose k := by
  rw[Layer]
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]



lemma CountingA {𝒜 : Family n}
    (h𝒜 : 𝒜 ⊆ Layer n r) :
    (incidences 𝒜).card = 𝒜.card * r := by
  sorry



lemma CountingB {𝒜 : Family n}
    (h𝒜 : 𝒜 ⊆ Layer n r) :
    (incidences 𝒜).card ≤ 𝒜.shadow.card * (n - (r - 1)) := by
  sorry

theorem local_lym_mul {n r} (𝒜 : Family n) (hrn : r ≤ n) (h𝒜 : 𝒜 ⊆ Layer n r) :
    𝒜.shadow.card * (n - (r - 1)) ≥ 𝒜.card * r := by
  nth_rw 2 [← CountingA]
  · rw[ge_iff_le]
    exact CountingB h𝒜
  exact h𝒜




theorem local_lym {n r} (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) (hrn : r ≤ n) (hr : r ≠ 0) :
    (𝒜.shadow.card : ℚ) / (Layer n (r-1)).card ≥ 𝒜.card / ↑(Layer n r).card := by
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  refine (div_le_div_iff₀ ?_ ?_).mpr ?_
  · rw[Nat.cast_pos]
    apply Nat.choose_pos
    assumption
  · rw[Nat.cast_pos]
    apply Nat.choose_pos
    refine Nat.sub_le_iff_le_add.mpr ?_
    exact Nat.le_add_right_of_le hrn
  sorry


theorem lym {n} (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    ∑ r ∈ Finset.range (n + 1), (𝒜.slice r).card / (n.choose r) ≤ 1 := by
  sorry

end Sperners
