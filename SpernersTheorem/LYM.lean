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

-- def incidences (𝒜 : Family n) :
--     Finset (Finset (Fin n) × Finset (Fin n)) :=
--   (𝒜.product (Finset.shadow 𝒜)).filter
--     (fun p => p.2 ⊆ p.1)

def fiberOver {n} (𝒜 : Family n) (A : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (Finset.shadow 𝒜).filter (fun B => B ⊆ A)

def incidences (𝒜 : Family n) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  𝒜.biUnion fun A =>
    (fiberOver 𝒜 A).image (fun B => (A, B))

theorem mem_incidences_iff (𝒜 : Family n) : -- incidences are equivalent to original definitions
    (A, B) ∈ incidences 𝒜 ↔
      A ∈ 𝒜 ∧ B ∈ 𝒜.shadow ∧ B ⊆ A := by
  refine Iff.intro ?_ ?_
  · intro h
    rw[incidences] at h
    simp_all only [Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq, exists_eq_right_right, true_and]
    obtain ⟨left, right⟩ := h
    apply And.intro
    · exact Finset.mem_of_mem_filter B right
    rw[fiberOver, Finset.mem_filter] at right
    exact right.right
  intro ⟨hA, hB, hBA⟩
  rw[incidences]
  refine Finset.mem_biUnion.mpr ?_
  refine Exists.intro A ?_
  simp_all only [Finset.mem_image, Prod.mk.injEq, true_and, exists_eq_right]
  rw[fiberOver]
  refine Finset.mem_filter.mpr ?_
  simp_all only [and_self]

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

theorem mem_layer_card_nat (𝒜 : Family n)
    (A : Finset (Fin n))
    (hA : A ∈ 𝒜) (hlay : 𝒜 ⊆ Layer n r) :
    A.card = r := by
  rw[Layer] at hlay
  exact Finset.mem_powersetCard_univ.mp (hlay hA)

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
  rw[incidences, Finset.card_biUnion, Finset.sum_const_nat]
  · intro A hA
    have : A.card = r := by
      exact mem_layer_card_nat 𝒜 _ hA h𝒜
    rw[Finset.card_image_of_injective]
    · rw[←this]
      exact card_fiber 𝒜 h𝒜 hA
    exact Prod.mk_right_injective A
  rw[Finset.pairwiseDisjoint_iff]
  intro A hA B hB hneq
  rcases hneq with ⟨p, hp⟩
  simp_all only [SetLike.mem_coe, Finset.mem_inter, Finset.mem_image]
  obtain ⟨fst, snd⟩ := p
  obtain ⟨left, right⟩ := hp
  obtain ⟨w, h⟩ := left
  obtain ⟨w_1, h_1⟩ := right
  obtain ⟨left, right⟩ := h
  obtain ⟨left_1, right_1⟩ := h_1
  simp_all only [Prod.mk.injEq]


theorem exists_insert {B C : Finset (Fin n)}
    (hsub : B ⊆ C)
    (hcard : B.card + 1 = C.card) :
    ∃ x, x ∉ B ∧ insert x B = C := by
  have  : ∃ a, (C \ B) = {a} := by
    refine Finset.card_eq_one.mp ?_
    rw [Finset.card_sdiff_of_subset hsub]
    exact Eq.symm (Nat.eq_sub_of_add_eq' hcard)
  rcases this with ⟨a, h⟩
  refine Exists.intro a ?_
  have : a ∈ C \ B := by
      simp_all only [Finset.mem_singleton]
  rw[Finset.mem_sdiff] at this
  apply And.intro
  · exact this.right
  obtain ⟨left, right⟩ := this
  rw[Finset.insert_eq]
  rw[←h]
  simp only [Finset.sdiff_union_self_eq_union, Finset.union_eq_left]
  exact hsub


theorem t1 (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) (hr : 0 < r) :
    ∀ B ∈ 𝒜.shadow, {A ∈ Layer n r | B ⊆ A}.card = n - (r - 1) := by
  intro B hB
  have : B.card = r - 1 := by
    rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at hB
    obtain ⟨C, hC, _, hcard⟩ := hB
    have : C.card = r := by
      refine mem_layer_card_nat (Layer n r) C (h𝒜 hC) ?_
      rfl
    subst this
    simp_all only [lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, add_tsub_cancel_right]
  have : Bᶜ.card = n - (r - 1) := by
    refine Nat.eq_sub_of_add_eq ?_
    rw[←this]
    simp only [Finset.card_compl_add_card, Fintype.card_fin]
  rw[←this]
  apply Eq.symm
  refine Finset.card_bij (fun (a : Fin n) (_ : a ∈ Bᶜ) => insert a B) ?_ ?_ ?_
  · intro a ha
    rw[Finset.mem_filter]
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.subset_insert,
      and_true]
    simp_all only [Finset.mem_compl, not_false_eq_true, Finset.card_insert_of_notMem]
    exact Nat.sub_add_cancel hr
  · intro a ha b hb h
    simp_all only [Finset.mem_compl]
    exact (Finset.insert_inj ha).mp h
  intro C hC
  rw[Finset.mem_filter] at hC
  rcases hC with ⟨hClay, hBC⟩
  have : ∃ a, insert a B = C := by
    have : B.card + 1 = C.card := by
      have : C.card = r := by
        refine mem_layer_card_nat (Layer n r) C hClay ?_
        rfl
      subst this
      simp_all only [Finset.card_pos, Finset.mem_powersetCard, Finset.subset_univ, and_self,
      Finset.one_le_card, Nat.sub_add_cancel]
    obtain ⟨a, _, h⟩ := (exists_insert hBC this)
    exact Exists.intro a h
  rcases this with ⟨a, hA⟩
  refine Exists.intro a ?_
  refine Exists.intro ?_ ?_
  · refine Finset.mem_compl.mpr ?_
    intro h
    rw[Finset.insert_eq_of_mem] at hA
    · have : B ≠ C := by
        rename_i this_1
        subst hA
        simp_all only [Finset.mem_powersetCard, Finset.subset_univ, true_and,
        subset_refl, ne_eq, not_true_eq_false]
        omega
      exact Ne.elim this hA
    exact h
  exact hA




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




theorem local_lym {n r} (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) (hrn : r ≤ n) (hr : r ≠ 0) :
    (𝒜.shadow.card : ℚ) / (Layer n (r-1)).card ≥ 𝒜.card / ↑(Layer n r).card := by
  sorry


theorem lym {n} (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    ∑ r ∈ Finset.range (n + 1), (𝒜.slice r).card / (n.choose r) ≤ 1 := by
  sorry

end Sperners
