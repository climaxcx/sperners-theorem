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
    simp_all only [Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq,
      exists_eq_right_right, true_and]
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


theorem shadow_layer (𝒜 : Family n) (h𝒜 : 𝒜 = Layer n r) (hr : 0 < r) (hrn : r ≤ n) :
    𝒜.shadow = Layer n (r - 1) := by
  rw[h𝒜]
  refine Finset.ext_iff.mpr ?_
  intro A
  apply Iff.intro
  · intro hA
    rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at hA
    obtain ⟨B, hB, _, hc⟩ := hA
    unfold Layer
    refine Finset.mem_powersetCard_univ.mpr ?_
    unfold Layer at hB
    rw[Finset.mem_powersetCard_univ] at hB
    rw[hB] at hc
    omega
  intro hA
  rw[Layer, Finset.mem_powersetCard_univ] at hA
  rw[Finset.mem_shadow_iff_exists_mem_card_add_one]
  have : Finset.Nonempty Aᶜ := by
    rw[Finset.compl_eq_univ_sdiff]
    refine Finset.sdiff_nonempty_of_card_lt_card ?_
    rw[hA]
    subst h𝒜
    simp_all only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha⟩ := this
  use insert a A
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.mem_powersetCard_univ.mpr ?_
    rw[Finset.card_insert_of_notMem]
    · omega
    exact Finset.mem_compl.mp ha
  · exact Finset.subset_insert a A
  refine Finset.card_insert_of_notMem ?_
  exact Finset.mem_compl.mp ha



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
    𝒜.card * r ≤ 𝒜.shadow.card * (n - (r - 1)) := by
  rw [← CountingA]
  · exact CountingB hr h𝒜
  exact h𝒜



theorem local_lym {n r} (𝒜 : Family n) (h𝒜 : 𝒜 ⊆ Layer n r) (hrn : r ≤ n) (hr : 0 < r) :
    (𝒜.card : ℚ) / n.choose r ≤ (𝒜.shadow.card : ℚ) / n.choose (r - 1):= by
  have hL:= local_lym_mul 𝒜 hr h𝒜
  calc _ = (𝒜.card : ℚ) * r.factorial * (n - r).factorial / n.factorial := by
        have := Nat.choose_mul_factorial_mul_factorial hrn
        have : (n.choose r : ℚ) * r.factorial * (n - r).factorial = n.factorial := by
          exact_mod_cast this
        field_simp
        rw[←this]
        field_simp
        refine Rat.mul_div_cancel ?_
        exact Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hrn)
  _ = (𝒜.card : ℚ) * r * (r-1).factorial * (n - r).factorial / n.factorial := by
        rw[←Nat.mul_factorial_pred hr.ne.symm]
        simp_all only [Nat.cast_mul]
        field
  _ ≤ (𝒜.shadow.card : ℚ) * (r-1).factorial * (n - (r - 1)).factorial / n.factorial := by
        field_simp
        have : n - (r - 1) ≠ 0 := by omega
        rw[←Nat.mul_factorial_pred this]
        have : n - (r - 1) - 1 = n - r := by omega
        rw[this]
        simp_all only [ne_eq, Nat.cast_mul, ge_iff_le]
        field_simp
        rw [←Nat.cast_mul, ←Nat.cast_mul]
        exact Rat.natCast_le_natCast.mpr hL
  _ = (𝒜.shadow.card : ℚ) * ((r-1).factorial * (n - (r - 1)).factorial / n.factorial) := by
        field
  _ = (𝒜.shadow.card : ℚ) * (n.choose (r - 1) : ℚ)⁻¹ := by
        simp_all only [mul_eq_mul_left_iff, Nat.cast_eq_zero, Finset.card_eq_zero]
        left
        have h' : r - 1 ≤ n := by omega
        have hr1: ((r - 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr
          (Nat.factorial_ne_zero (r - 1))
        have hnr1: ((n - (r - 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr
          (Nat.factorial_ne_zero (n - (r - 1)))
        have hn: (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
        have hnc: (n.choose (r - 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
        have hr1nr : ((r-1).factorial * (n - (r - 1)).factorial : ℚ) ≠ 0 := by
          exact (mul_ne_zero_iff_right hnr1).mpr hr1
        field_simp[hr1, hnr1, hn, hnc, hr1nr]
        rw[←Nat.cast_mul, ←Nat.cast_mul]
        have := Nat.choose_mul_factorial_mul_factorial h'
        refine Rat.natCast_inj.mpr ?_
        rw[← this]
        ring
  _ = (𝒜.shadow.card : ℚ) / n.choose (r - 1):= by
        field


noncomputable def G (𝒜 : Family n) : (k : ℕ) → Family n
| 0 =>
  𝒜.slice n
| k + 1 =>
  𝒜.slice (n - (k + 1)) ∪ (G 𝒜 k).shadow


theorem G_in_some_F (𝒜 : Family n) (k : ℕ) (hk : k ≤ n) :
    ∀ B ∈ G 𝒜 k, ∃ A ∈ 𝒜, B ⊆ A := by
  induction k with
  | zero =>
    intro B hB
    use B
    rw[G, Finset.mem_slice] at hB
    exact ⟨hB.left, subset_refl B⟩
  | succ i ih =>
    intro B hB
    rw[G, Finset.mem_union] at hB
    rcases hB with h | h
    · use B
      rw[Finset.mem_slice] at h
      exact ⟨h.left, subset_refl B⟩
    rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at h
    obtain ⟨C, hG, hBC, _⟩ := h
    obtain ⟨A, hA, hCA⟩ := ih (Nat.le_of_succ_le hk) C hG
    exact ⟨A, hA, subset_trans hBC hCA⟩



theorem G_disj (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (k : ℕ) (hk : k < n) :
    Disjoint (𝒜.slice (n - (k + 1))) (G 𝒜 k).shadow := by
  rw [Finset.disjoint_right]
  intro A hA h
  rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at hA
  obtain ⟨B, hB, hAB, hcard⟩ := hA
  obtain ⟨C, hC, hBC⟩ := G_in_some_F 𝒜 k (le_of_lt hk) B hB
  rw[Finset.mem_slice] at h
  have := (h𝒜.eq h.left hC (subset_trans hAB hBC))
  rw[this] at hcard
  have : B.card ≤ C.card := by
    exact Finset.card_le_card hBC
  omega

theorem G_card (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (k : ℕ) (hk : k < n) :
    (G 𝒜 (k + 1)).card = (G 𝒜 k).shadow.card +
      (𝒜.slice (n - (k + 1))).card := by
  rw[G]
  have := Finset.card_union_of_disjoint (G_disj 𝒜 h𝒜 k hk)
  rw[this]
  omega

theorem G_lay (𝒜 : Family n) (k : ℕ) (hk : k ≤ n) :
    (G 𝒜 k) ⊆ Layer n (n - k) := by
  unfold Layer
  induction k with
  | zero =>
    intro A hA
    refine Finset.mem_powersetCard_univ.mpr ?_
    unfold G at hA
    obtain ⟨_, h⟩ := Finset.mem_slice.mp hA
    omega
  | succ i hi =>
    intro A hA
    refine Finset.mem_powersetCard_univ.mpr ?_
    unfold G at hA
    rw[Finset.mem_union] at hA
    rcases hA with hF | hG
    · obtain ⟨_, h⟩ := Finset.mem_slice.mp hF
      omega
    obtain ⟨B, hB, _, hc⟩ := Finset.mem_shadow_iff_exists_mem_card_add_one.mp hG
    have : i ≤ n := by omega
    have := hi this
    rw[Finset.subset_iff] at this
    have := this hB
    have : B.card = (n - i) := by
      exact Finset.mem_powersetCard_univ.mp this
    omega

theorem Gn_card (𝒜 : Family n) :
    (G 𝒜 n).card ≤ 1 := by
  have := G_lay 𝒜 n (n.le_refl)
  simp only [tsub_self, Finset.powersetCard_zero] at this
  exact Finset.card_le_one_iff_subset_singleton.mpr ⟨∅, this⟩




theorem lym_sum (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (r : ℕ) (hr : r ≤ n) :
  ∑ i ∈ Finset.range (r + 1), ((𝒜.slice (n - i)).card : ℚ)  / (n.choose (n - i)) ≤
    ((G 𝒜 r).card : ℚ) / (n.choose r) := by
  induction r with
  |zero =>
    unfold G
    aesop
  |succ j ih =>
    have := (Finset.sum_range_succ (fun x ↦ ((𝒜.slice (n-x)).card : ℚ) / n.choose (n - x)) (j + 1))
    -- rw[this, ih (Nat.le_of_succ_le hr)]
    let S := ∑ x ∈ Finset.range (j + 1), ((Finset.slice 𝒜 (n - x)).card : ℚ) / (n.choose (n - x))
    calc _ = S + ((𝒜.slice (n - (j + 1))).card : ℚ) / n.choose (n - (j + 1)) := by
          exact this
      _ ≤ ((G 𝒜 j).card : ℚ) / n.choose j +  ((𝒜.slice (n - (j + 1))).card : ℚ)
            / n.choose (n - (j + 1)) := by
          rw [add_le_add_iff_right]
          exact ih (Nat.le_of_succ_le hr)
      _ ≤ ((G 𝒜 j).shadow.card : ℚ) / n.choose (j + 1) + ((𝒜.slice (n - (j + 1))).card : ℚ)
            / n.choose (n - (j + 1)) := by
          rw[add_le_add_iff_right]
          have := local_lym (G 𝒜 j) (G_lay 𝒜 j (Nat.le_of_succ_le hr))
            (Nat.sub_le n j) (Nat.zero_lt_sub_of_lt hr)
          have hnj: (n - j - 1) = n - (j + 1) := by omega
          rw[hnj, Nat.choose_symm, Nat.choose_symm] at this
          · exact this
          · exact hr
          exact Nat.le_of_succ_le hr
      _ = (((G 𝒜 j).shadow.card : ℚ) + ((𝒜.slice (n - (j + 1))).card : ℚ))
            / (n.choose (j + 1) : ℚ) := by
          rw[Nat.choose_symm]
          · rw [add_div]
          exact hr
      _ = ((G 𝒜 (j + 1)).card : ℚ) / n.choose (j + 1):= by
          have := G_card 𝒜 h𝒜 j (Nat.lt_of_succ_le hr)
          rw[this]
          simp only [Nat.cast_add]





theorem lym {n} (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ)  / (n.choose r) ≤ 1 := by
  have hlym := lym_sum 𝒜 h𝒜 n (n.le_refl)
  simp only [Nat.choose_self, Nat.cast_one, div_one] at hlym
  have : ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ) / (n.choose r) =
      ∑ i ∈ Finset.range (n + 1), ((𝒜.slice (n - i)).card : ℚ) / (n.choose (n - i)) := by
    refine Finset.sum_bij (fun i hi => n - i) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_range_succ_iff.mpr (Nat.sub_le n i)
    · intro a ha b hb hdiff
      simp_all only [Finset.mem_range, Order.lt_add_one_iff]
      omega
    · intro i hi
      rw[Finset.mem_range] at hi
      refine ⟨(n - i), ?_, ?_⟩
      · rw[Finset.mem_range]
        omega
      omega
    intro i hi
    rw[Finset.mem_range] at hi
    have : n - (n - i) = i := by
      omega
    simp_all only [Order.lt_add_one_iff]
  rw[this]
  exact Rat.le_trans hlym (Nat.cast_le_one.mpr (Gn_card 𝒜))




theorem sperners (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    𝒜.card ≤ n.choose (n/2) := by
  have : (𝒜.card : ℚ) / n.choose (n/2) ≤ 1 := by
    have hne0 : (n.choose (n / 2) : ℚ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
    calc (𝒜.card : ℚ) / n.choose (n/2)
      = (∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ)) / n.choose (n / 2) := by
          have : 𝒜.card = ∑ r ∈ Finset.range (n + 1), (𝒜.slice r).card := by
            refine Finset.card_eq_sum_card_fiberwise ?_
            refine Finset.mapsTo_iff_image_subset.mpr ?_
            refine Finset.subset_range.mpr ?_
            intro i hi
            rw[Finset.mem_image] at hi
            obtain ⟨A, hA, hcardA⟩ := hi
            rw[←hcardA]
            refine Order.lt_add_one_iff.mpr ?_
            exact card_finset_fin_le A
          rw[this]
          simp_all only [Nat.cast_sum]
    _ = ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ) / n.choose (n / 2) := by
          refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
          · exact hne0
          rw[Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro r hr
          refine Eq.symm (Rat.div_mul_cancel ?_)
          · exact hne0
    _ ≤ ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ) / n.choose r := by
          refine Finset.sum_le_sum ?_
          intro r hr
          refine div_le_div_of_nonneg_left ?_ ?_ ?_
          · exact Rat.natCast_nonneg
          · refine Rat.natCast_pos.mpr ?_
            refine Nat.choose_pos ?_
            exact Finset.mem_range_succ_iff.mp hr
          refine Rat.natCast_le_natCast.mpr ?_
          exact Nat.choose_le_middle r n
    _ ≤ 1 := by
          exact lym 𝒜 h𝒜
  have hzle : 0 < (n.choose (n / 2) : ℚ) := by
    refine Rat.natCast_pos.mpr ?_
    refine Nat.choose_pos ?_
    exact Nat.div_le_self n 2
  have := (div_le_one hzle).mp this
  exact Rat.natCast_le_natCast.mp this
end Sperners
