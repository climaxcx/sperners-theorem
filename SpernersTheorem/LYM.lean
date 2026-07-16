import Mathlib

namespace Sperners

abbrev Family (n : ℕ) :=
  Finset (Finset (Fin n))

abbrev IsSubsetChain {n} (C : Family n) :=
  IsChain (· ⊆ ·) (C : Set (Finset (Fin n)))

abbrev IsSubsetAntichain {n} (C : Family n) :=
  IsAntichain (· ⊆ ·) (C : Set (Finset (Fin n)))



theorem IsSubsetAntichain.subset (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (h : F ⊆ 𝒜) :
    IsSubsetAntichain F := by
  unfold IsSubsetAntichain
  unfold IsSubsetAntichain at h𝒜
  exact IsAntichain.subset h𝒜 h

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


theorem existsUnique_insert {B C : Finset (Fin n)}
    (hsub : B ⊆ C)
    (hcard : B.card + 1 = C.card) :
    ∃! x, x ∉ B ∧ insert x B = C := by
  have  : ∃ a, (C \ B) = {a} := by
    refine Finset.card_eq_one.mp ?_
    rw [Finset.card_sdiff_of_subset hsub]
    exact Eq.symm (Nat.eq_sub_of_add_eq' hcard)
  rcases this with ⟨a, h⟩
  refine ExistsUnique.intro a ?_ ?_
  · have : a ∈ C \ B := by
      simp_all only [Finset.mem_singleton]
    rw[Finset.mem_sdiff] at this
    apply And.intro
    · exact this.right
    obtain ⟨left, right⟩ := this
    rw[Finset.insert_eq]
    rw[←h]
    simp only [Finset.sdiff_union_self_eq_union, Finset.union_eq_left]
    exact hsub
  intro b ⟨hb, hb2⟩
  subst hb2
  simp_all only [Finset.subset_insert, not_false_eq_true, Finset.card_insert_of_notMem,
    Finset.insert_sdiff_cancel, Finset.singleton_inj]


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
    obtain ⟨a, _, h⟩ := (existsUnique_insert hBC this).exists
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


def upperFiber (𝒜 : Family n) (B : Finset (Fin n)) : Family n :=
  𝒜.filter (fun A => B ⊆ A)

theorem card_upperFiber
    {𝒜 : Family n}
    (h𝒜 : 𝒜 ⊆ Layer n r)
    (hr : 0 < r)
    (hB : B ∈ Finset.shadow 𝒜) :
    (upperFiber 𝒜 B).card ≤ n - (r - 1) := by
  rw[upperFiber]
  have : {A ∈ 𝒜 | B ⊆ A}.card ≤ {A ∈ Layer n r | B ⊆ A}.card := by
    have : {A ∈ 𝒜 | B ⊆ A} ⊆ {A ∈ Layer n r | B ⊆ A} := by
      exact Finset.filter_subset_filter (fun A ↦ B ⊆ A) h𝒜
    exact Finset.card_le_card this
  rw[←t1 𝒜 h𝒜 hr B hB]
  exact this

def incidencesByShadow (𝒜 : Family n) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (Finset.shadow 𝒜).biUnion fun B =>
    (upperFiber 𝒜 B).image (fun A => (A, B))

theorem incidences_eq_byShadow :
    incidences 𝒜 = incidencesByShadow 𝒜 := by
  ext p
  obtain ⟨A, B⟩ := p
  apply Iff.intro
  · intro h
    rw[incidencesByShadow, Finset.mem_biUnion]
    rw[mem_incidences_iff] at h
    obtain ⟨hA, hB, hBA⟩ := h
    refine Exists.intro B ?_
    refine And.intro hB ?_
    refine Finset.mem_image.mpr ?_
    refine Exists.intro A ?_
    refine And.intro ?_ ?_
    · rw[upperFiber]
      simp_all only [Finset.mem_filter, and_self]
    rfl
  · intro h
    rw[incidencesByShadow, Finset.mem_biUnion] at h
    obtain ⟨C, hC, h⟩ := h
    rw[Finset.mem_image] at h
    obtain ⟨D, h1, h2⟩ := h
    have hDA: D = A := by
      simp_all only [Prod.mk.injEq]
    have hCB : C = B := by
      simp_all only [Prod.mk.injEq]
    rw[upperFiber, Finset.mem_filter] at h1
    obtain ⟨hD𝒜, hCD⟩ := h1
    rw[mem_incidences_iff]
    apply And.intro
    · aesop
    · apply And.intro
      · aesop
      · aesop

theorem incidences_card_eq_sum_upperFiber :
  (incidences 𝒜).card =
    ∑ B ∈ Finset.shadow 𝒜,
      (upperFiber 𝒜 B).card := by
  rw[incidences_eq_byShadow, incidencesByShadow, Finset.card_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro A hA
    refine Finset.card_image_of_injective (upperFiber 𝒜 A) ?_
    exact Prod.mk_left_injective A
  intro A hA B hB hneq
  unfold Function.onFun
  rw[Finset.disjoint_left]
  intro p hpA hpB
  rw[Finset.mem_image] at hpA hpB
  simp_all only [SetLike.mem_coe, ne_eq]
  obtain ⟨fst, snd⟩ := p
  obtain ⟨w, h⟩ := hpA
  obtain ⟨w_1, h_1⟩ := hpB
  obtain ⟨left, right⟩ := h
  obtain ⟨left_1, right_1⟩ := h_1
  simp_all only [Prod.mk.injEq, not_true_eq_false]



lemma CountingB {𝒜 : Family n}
    (hr : 0 < r)
    (h𝒜 : 𝒜 ⊆ Layer n r) :
    (incidences 𝒜).card ≤ 𝒜.shadow.card * (n - (r - 1)) := by
  rw[incidences_card_eq_sum_upperFiber]
  rw[←Finset.sum_const_nat (f := fun _ => n - (r - 1))]
  · refine Finset.sum_le_sum ?_
    intro A hA
    exact card_upperFiber h𝒜 hr hA
  intro _ _
  rfl







theorem local_lym_mul {n r} (𝒜 : Family n) (hr : 0 < r) (h𝒜 : 𝒜 ⊆ Layer n r) :
    𝒜.shadow.card * (n - (r - 1)) ≥ 𝒜.card * r := by
  nth_rw 2 [← CountingA]
  · rw[ge_iff_le]
    exact CountingB hr h𝒜
  exact h𝒜

theorem local_lym {n r} (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) (hrn : r ≤ n) (hr : r < 0) :
    (𝒜.shadow.card : ℚ) / (Layer n (r-1)).card ≥ 𝒜.card / ↑(Layer n r).card := by
  sorry

theorem shadow_ninter_slice (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (r : Fin n) :
    Disjoint (𝒜.slice r) (𝒜.slice r.succ).shadow := by
  refine Finset.disjoint_left.mpr ?_
  intro A hA h
  rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at h
  obtain ⟨B, hB, hAB, hcard⟩ := h
  have : A ≠ B := by
    intro h
    rw[h] at hcard
    omega
  apply this
  rw[IsSubsetAntichain] at h𝒜
  have hA𝒜 : A ∈ 𝒜 := by
    exact Finset.mem_of_mem_filter A hA
  have hB𝒜 : B ∈ 𝒜 := by
    exact Finset.mem_of_mem_filter B hB
  exact IsAntichain.eq h𝒜 hA𝒜 hB𝒜 hAB

def F (𝒜 : Family n) (r : Fin (n + 1)) :
    Family n :=
  𝒜.slice r

noncomputable def G (𝒜 : Family n) : (k : ℕ) → k ≤ n → Family n
| 0, h =>
  F 𝒜 ⟨n, by omega⟩
| k + 1, h =>
  let hk : k ≤ n := by omega
  let r : Fin (n + 1) :=
    ⟨n - (k + 1), by omega⟩
  F 𝒜 r ∪ (G 𝒜 k hk).shadow

theorem F_antichain (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (r : Fin (n + 1)) :
    IsSubsetAntichain (F 𝒜 r) := by
  refine IsSubsetAntichain.subset 𝒜 h𝒜 ?_
  unfold F
  exact Finset.slice_subset


theorem G0_card (𝒜 : Family n) :
    Finset.card (G 𝒜 (0 : Fin (n + 1)) (by omega)) = Finset.card (F 𝒜 ⟨n, by omega⟩) := by
  exact Finset.card_sdiff_eq_card_sdiff_iff.mp rfl

theorem G_in_some_F (𝒜 : Family n) (k : ℕ) (hk : k ≤ n) :
    ∀ B ∈ G 𝒜 k hk, ∃ A ∈ 𝒜, B ⊆ A := by
  induction k with
  | zero =>
    intro B hB
    use B
    unfold G at hB
    unfold F at hB
    rw[Finset.mem_slice] at hB
    exact And.intro (hB.left) (subset_refl B)
  | succ i ih =>
    intro B hB
    unfold G at hB
    simp only at hB
    rw[Finset.mem_union] at hB
    rcases hB with hF | hG
    · unfold F at hF
      use B
      rw[Finset.mem_slice] at hF
      exact And.intro (hF.left) (subset_refl B)
    rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at hG
    obtain ⟨C, hC, hBC, _⟩ := hG
    obtain ⟨A', hA', hCA'⟩ := ih (Nat.le_of_succ_le hk) C hC
    use A'
    exact And.intro hA' (subset_trans hBC hCA')


theorem G_disj (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (k : ℕ) (hk : k < n) :
    Disjoint (F 𝒜 ⟨n - (k + 1), by omega⟩) (G 𝒜 k (by omega)).shadow := by
  refine Finset.disjoint_left.mpr ?_
  intro A hA h
  rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at h
  obtain ⟨B, hB, hAB, hcard⟩ := h
  obtain ⟨C, hC, hBC⟩ := G_in_some_F 𝒜 k (le_of_lt hk) B hB
  unfold IsSubsetAntichain at h𝒜
  unfold F at hA
  rw[Finset.mem_slice] at hA
  have : A ≠ C := by
    have hABs : A ⊂ B := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      refine And.intro hAB ?_
      intro h
      rw[h] at hcard
      omega
    have : A ⊂ C := by
      exact Finset.ssubset_of_ssubset_of_subset hABs hBC
    exact Std.ne_of_lt this
  apply this
  exact h𝒜.eq hA.left hC (subset_trans hAB hBC)


theorem G_card (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (k : ℕ) (hk : k < n) :
    (G 𝒜 (k + 1) (by omega)).card = (G 𝒜 k (by omega)).shadow.card +
      (F 𝒜 ⟨n - (k + 1), by omega⟩).card := by
  rw[G]
  have := Finset.card_union_of_disjoint (G_disj 𝒜 h𝒜 k hk)
  rw[this]
  omega

theorem G_lay (𝒜 : Family n) (k : ℕ) (hk : k ≤ n) :
    (G 𝒜 k hk) ⊆ Layer n (n - k) := by
  unfold Layer
  induction k with
  | zero =>
    intro A hA
    refine Finset.mem_powersetCard_univ.mpr ?_
    unfold G at hA
    unfold F at hA
    obtain ⟨_, h⟩ := Finset.mem_slice.mp hA
    omega
  | succ i hi =>
    intro A hA
    refine Finset.mem_powersetCard_univ.mpr ?_
    unfold G at hA
    rw[Finset.mem_union] at hA
    rcases hA with hF | hG
    · unfold F at hF
      obtain ⟨_, h⟩ := Finset.mem_slice.mp hF
      omega
    obtain ⟨B, hB, _, hc⟩ := Finset.mem_shadow_iff_exists_mem_card_add_one.mp hG
    have : i ≤ n := by omega
    have := hi this
    rw[Finset.subset_iff] at this
    have := this hB
    have : B.card = (n - i) := by
      exact Finset.mem_powersetCard_univ.mp this
    omega



theorem G_local_lym_mul (𝒜 : Family n) (k : ℕ) (hkle : k < n) :
    (G 𝒜 k (by omega)).shadow.card * (k + 1) ≥ (G 𝒜 k (by omega)).card * (n - k) := by
  set Gk := (G 𝒜 k (by omega)) with hGk
  have hlay : Gk ⊆ Layer n (n - k) := by
    exact G_lay 𝒜 k (by omega)
  have : 0 < (n - k) := by omega
  have h := local_lym_mul Gk this hlay
  have : (n - (n - k - 1)) = k + 1 := by omega
  rw[this] at h
  exact h


theorem t2 (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (r : ℕ) (hr : r ≤ n) :
    (G 𝒜 r hr).card * r.factorial * (n-r).factorial ≥
      ∑ i ∈ Finset.range (r + 1), (F 𝒜 ⟨n-i, by omega⟩).card * i.factorial * (n-i).factorial := by
  induction r with
  | zero =>
    unfold G
    rw[Finset.sum_range_one]
    ring_nf!
    omega
  | succ j ih =>
    have hjn': j ≤ n := by omega
    have ih := ih hjn'
    have hjn : j < n := by omega
    have := G_card 𝒜 h𝒜 j hjn
    rw[this]
    have hloc := ge_iff_le.mp (G_local_lym_mul 𝒜 j hjn)
    set Gr := (G 𝒜 j hjn')
    set Fj := (F 𝒜 ⟨n - (j + 1), (by omega)⟩)
    set Gr1 := (G 𝒜 (j+1) hjn)
    calc (Gr.shadow.card +
      Fj.card) * (j + 1).factorial * (n - (j + 1)).factorial
    = (Gr.shadow.card + Fj.card)
      * (j + 1) * j.factorial * (n - (j + 1)).factorial := by
          rw[Nat.factorial_succ]
          ring
  _  = Gr.shadow.card * (j + 1) * j.factorial * (n - (j + 1)).factorial +
      Fj.card * (j + 1) * j.factorial * (n - (j + 1)).factorial := by
          ring
  _  ≥ (Gr.card * (n - j)) * j.factorial * (n - (j + 1)).factorial +
      Fj.card * (j + 1) * j.factorial * (n - (j + 1)).factorial := by
          rw[ge_iff_le]
          have : (Gr.card * (n - j)) * j.factorial * (n - (j + 1)).factorial
            ≤ Gr.shadow.card * (j + 1) * j.factorial * (n - (j + 1)).factorial := by
              have : 0 ≤ (n - (j + 1)).factorial := by omega
              refine mul_le_mul_of_nonneg_right ?_ this
              exact mul_le_mul_of_nonneg_right hloc (by omega)
          exact add_le_add_left this _
  _ = (Gr.card * (n - j)) * j.factorial * (n - (j + 1)).factorial +
        Fj.card * (j + 1).factorial * (n - (j + 1)).factorial := by
        rw[Nat.factorial_succ]
        ring
  _ = Gr.card * j.factorial * ((n - j) * (n - j - 1).factorial) +
        Fj.card * (j + 1).factorial * (n - (j + 1)).factorial := by
        ring!
  _ = Gr.card * j.factorial * (n - j).factorial +
        Fj.card * (j + 1).factorial * (n - (j + 1)).factorial := by
      have : (n - j) * (n - j - 1).factorial = (n - j).factorial := by
        refine Nat.mul_factorial_pred ?_
        omega
      rw[this]
  _ ≥ ∑ i ∈ Finset.range (j + 1),
        Finset.card (F 𝒜 ⟨n - i, by omega⟩) * i.factorial * (n - i).factorial +
        Fj.card * (j + 1).factorial * (n - (j + 1)).factorial := by
      rw[ge_iff_le]
      exact add_le_add_left ih _
  _ =
      ∑ i ∈ Finset.range (j + 1 + 1),
        Finset.card (F 𝒜 ⟨n - i, (by omega)⟩) * i.factorial * (n - i).factorial := by
          have : Finset.card (F 𝒜 ⟨n - (j + 1), (by omega)⟩) *
              (j + 1).factorial * (n - (j + 1)).factorial =
              Fj.card * (j + 1).factorial * (n - (j + 1)).factorial := by
            ring
          exact
            Eq.symm
              (Finset.sum_range_succ
                (fun x ↦ Finset.card (F 𝒜 ⟨n - x, by omega⟩) * x.factorial * (n - x).factorial)
                (j + 1))









theorem lym_mult (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    ∑ r ∈ Finset.range (n + 1), (𝒜.slice r).card *
      r.factorial * (n - r).factorial ≤ n.factorial := by
  have hnn : n ≤ n := by omega
  have h := t2 𝒜 h𝒜 n hnn
  unfold F at h
  rw[ge_iff_le] at h
  set Gn := G 𝒜 n hnn
  have hGncard : Gn.card ≤ 1 := by
    have := G_lay 𝒜 n hnn
    rw[tsub_self] at this
    unfold Layer at this
    have hc: ∀ A ∈ Gn, A.card = 0 := by
      intro A hA
      unfold Gn at hA
      rw[Finset.subset_powersetCard_univ_iff] at this
      exact Set.powersetCard.mem_iff.mp (this hA)
    refine Finset.card_le_one_iff_subset_singleton.mpr ?_
    use ∅
    refine Finset.subset_singleton_iff'.mpr ?_
    intro A hA
    have := hc A hA
    exact Finset.card_eq_zero.mp (hc A hA)
  have : ∑ i ∈ Finset.range (n + 1), (𝒜.slice (n - i)).card * i.factorial * (n - i).factorial =
          ∑ i ∈ Finset.range (n + 1), (𝒜.slice i).card * i.factorial * (n - i).factorial := by
        refine Finset.sum_bij ?_ ?_ ?_ ?_ ?_
        · exact (fun i hi => n - i)
        · intro i hi
          rw[Finset.mem_range]
          omega
        · intro a ha b hb heq
          rw[Finset.mem_range] at ha hb
          have hb := Nat.le_of_lt_succ hb
          have ha := Nat.le_of_lt_succ ha
          omega
        · intro i hi
          rw[Finset.mem_range] at hi
          use (n - i)
          refine exists_prop.mpr ?_
          apply And.intro
          · rw[Finset.mem_range]
            omega
          omega
        intro i hi
        rw[Finset.mem_range] at hi
        have : (n - (n - i)) = i := by
          omega
        rw[this]
        ring
  rw[←this]
  refine le_trans h ?_
  simp_all only [tsub_self, Nat.factorial_zero, mul_one]
  have : 0 ≤ n.factorial := by omega
  nth_rw 2 [←one_mul n.factorial]
  exact mul_le_mul_of_nonneg_right hGncard this



theorem lym {n} (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ)  / (n.choose r) ≤ 1 := by
  calc
    ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ)  / (n.choose r)
    = ∑ r ∈ Finset.range (n + 1),
        ((𝒜.slice r).card : ℚ)  * r.factorial * (n - r).factorial / n.factorial := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      have hrn : r ≤ n := by
        exact Finset.mem_range_succ_iff.mp hr
      have := Nat.choose_mul_factorial_mul_factorial hrn
      have : (n.choose r : ℚ) * r.factorial * (n - r).factorial = n.factorial := by
        exact_mod_cast this
      field_simp
      rw[←this]
      field_simp
      refine Rat.mul_div_cancel ?_
      exact Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hrn)
  _ = (n.factorial : ℚ)⁻¹ * ∑ r ∈ Finset.range (n + 1),
        (𝒜.slice r).card * r.factorial * (n - r).factorial := by
      field_simp
      rw[Finset.mul_sum]
      field_simp
      simp_all only [Nat.cast_sum, Nat.cast_mul]
  _ ≤ (n.factorial : ℚ)⁻¹ * n.factorial := by
      have zero_le : 0 ≤ (n.factorial : ℚ)⁻¹ := Rat.inv_nonneg Rat.natCast_nonneg
      refine Rat.mul_le_mul_of_nonneg_left ?_ zero_le
      refine Rat.natCast_le_natCast.mpr ?_
      exact lym_mult 𝒜 h𝒜
  _ = 1 := by
      exact Rat.inv_mul_cancel ↑n.factorial (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

end Sperners
