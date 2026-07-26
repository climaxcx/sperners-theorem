import Mathlib
import SpernersTheorem.LYM

namespace Sperners

lemma CountingB_eq {𝒜 : Family n}
    (hr : 0 < r)
    (hrn : r ≤ n)
    (h𝒜 : 𝒜 ⊆ Layer n r) :
    𝒜.shadow.card * (n - (r - 1)) = (incidences 𝒜).card ↔ 𝒜 = ∅ ∨ 𝒜 = Layer n r := by
  apply Iff.intro
  · intro h
    rw[incidences_card_eq_sum_upperFiber, ←Finset.sum_const_nat (f := fun _ => n - (r - 1))] at h
    · have hle : ∀ B ∈ 𝒜.shadow, (upperFiber 𝒜 B).card ≤ n - (r - 1) := by
        intro B hB
        exact card_upperFiber h𝒜 hr hB
      have hall : ∀ B ∈ 𝒜.shadow, (upperFiber 𝒜 B).card = n - (r - 1) := by
        intro B hB
        by_contra!
        obtain hleB := hle B hB
        have := lt_of_le_of_ne hleB this
        have : ∑ B ∈ Finset.shadow 𝒜, Finset.card (upperFiber 𝒜 B) <
            ∑ x ∈ Finset.shadow 𝒜, (n - (r - 1)) := by
          refine Finset.sum_lt_sum hle ?_
          use B
        rw[h, lt_self_iff_false] at this
        exact this
      have hhh : ∀ B ∈ 𝒜.shadow, ∀ i ∉ B, insert i B ∈ 𝒜 := by
        intro B hB i hi
        have hcard := hall B hB
        have hsub: B ⊆ insert i B := by
          exact Finset.subset_insert i B
        by_contra! h
        unfold upperFiber at hcard
        have : {A ∈ Layer n r | B ⊆ A}.card =
            {A ∈ 𝒜 | B ⊆ A}.card + {A ∈ (Layer n r) \ 𝒜 | B ⊆ A}.card := by
          have hdisj: Disjoint {A ∈ 𝒜 | B ⊆ A} {A ∈ (Layer n r) \ 𝒜 | B ⊆ A} := by
            refine Finset.disjoint_filter_filter ?_
            exact Finset.disjoint_sdiff
          have := Finset.card_disjUnion {A ∈ 𝒜 | B ⊆ A} {A ∈ (Layer n r) \ 𝒜 | B ⊆ A} hdisj
          rw[←this]
          have : {A ∈ 𝒜 | B ⊆ A} ∪ {A ∈ (Layer n r) \ 𝒜 | B ⊆ A} =
              {A ∈ Layer n r | B ⊆ A} := by
            refine Finset.ext_iff.mpr ?_
            intro A
            refine Iff.intro ?_ ?_
            · intro hA
              refine Finset.mem_filter.mpr ?_
              rw[Finset.mem_union] at hA
              rcases hA with h1 | h2
              · refine And.symm ⟨?_, ?_⟩
                · exact (Finset.mem_filter.mp h1).right
                refine Finset.mem_of_subset h𝒜 ?_
                exact Finset.mem_of_mem_filter A h1
              apply And.intro
              · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h2).left).left
              exact (Finset.mem_filter.mp h2).right
            intro hA
            obtain ⟨hA, hBA⟩ := Finset.mem_filter.mp hA
            have : Layer n r = 𝒜 ∪ (Layer n r \ 𝒜) := by
              exact Eq.symm (Finset.union_sdiff_of_subset h𝒜)
            rw[this, Finset.mem_union] at hA
            rw[Finset.mem_union]
            rcases hA with h1 | h2
            · left
              refine Finset.mem_filter.mpr ?_
              exact ⟨h1, hBA⟩
            right
            refine Finset.mem_filter.mpr ?_
            exact ⟨h2, hBA⟩
          simp_all
        rw [t1 𝒜 h𝒜 hr B hB, hcard] at this
        simp only [Nat.left_eq_add, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
          Finset.mem_sdiff, Finset.mem_powersetCard, Finset.subset_univ, true_and, and_imp] at this
        have hcardins: (insert i B).card = r := by
          rw [Finset.card_insert_of_notMem hi]
          have : B.card = r - 1 := by
            rw[Finset.mem_shadow_iff_exists_mem_card_add_one] at hB
            obtain ⟨A, hA, hBA, hc⟩ := hB
            rw [mem_layer_card_nat 𝒜 A hA h𝒜] at hc
            omega
          omega
        have := this hcardins h
        exact this hsub
      by_contra!
      obtain ⟨hnem, hssub⟩ := this
      have : ∃ x, x ∈ 𝒜 := by
        exact Finset.nonempty_def.mp hnem
      obtain ⟨A1, hA1⟩ := this
      have hssub := ssubset_of_ne_of_subset hssub h𝒜
      have hexA : ∃ A ∈ Layer n r, A ∉ 𝒜 := by
        exact Set.exists_of_ssubset hssub
      obtain ⟨A2, _, hA2⟩ := hexA
      let S : Set ℕ := {m | ∃ A ∈ 𝒜, ∃ A' ∈ Layer n r, A' ∉ 𝒜 ∧ (symmDiff A A').card = m}
      have hnonempty : S.Nonempty := by
        use (symmDiff A1 A2).card
        refine Set.mem_setOf.mpr ?_
        use A1
        refine And.intro hA1 ?_
        use A2
      let m := Nat.find hnonempty
      have hm : ∃ A ∈ 𝒜, ∃ A' ∈ Layer n r, A' ∉ 𝒜 ∧ (symmDiff A A').card = m := by
       exact Nat.find_spec hnonempty
      have hmin : ∀ k < m, ¬ (∃ A ∈ 𝒜, ∃ A' ∈ Layer n r, A' ∉ 𝒜 ∧ (symmDiff A A').card = k) := by
        intro k hk h
        exact Nat.find_min hnonempty hk h
      obtain ⟨A, hA, hA'⟩ := hm
      obtain ⟨A', hAl, hA', h⟩ := hA'
      have hcardA : A.card = r := by
        exact mem_layer_card_nat 𝒜 A hA h𝒜
      have hcardA' : A'.card = r := by
        exact mem_layer_card_nat (Layer n r) A' hAl (subset_refl (Layer n r))
      have hAcardA' : A.card = A'.card := by
        rw[hcardA, hcardA']
      have hAneA' : A ≠ A' := by
        intro h
        apply hA'
        rw[←h]
        exact hA
      have hnon1 : (A \ A').Nonempty := by
        refine Finset.sdiff_nonempty.mpr ?_
        intro h
        apply hAneA'
        refine Finset.eq_of_subset_of_card_le h ?_
        exact Nat.le_of_eq (id (Eq.symm hAcardA'))
      have hnon2 : (A' \ A).Nonempty := by
        refine Finset.sdiff_nonempty.mpr ?_
        intro h
        apply hAneA'
        symm
        refine Finset.eq_of_subset_of_card_le h ?_
        exact Nat.le_of_eq hAcardA'
      obtain ⟨a1, ha1⟩ := Finset.nonempty_def.mp hnon1
      obtain ⟨a2, ha2⟩ := Finset.nonempty_def.mp hnon2
      set A3 := insert a2 (A.erase a1) with hA3
      have : (symmDiff A3 A').card < m := by
        rw[←h]
        refine Finset.card_lt_card ?_
        refine (Finset.ssubset_iff_of_subset ?_).mpr ?_
        · refine Finset.subset_iff.mpr ?_
          intro x hx
          rw[Finset.mem_symmDiff] at hx
          rw[Finset.mem_symmDiff]
          rcases hx with ⟨h1, h1'⟩ | ⟨h2, h2'⟩
          · unfold A3 at h1
            rw[Finset.insert_eq, Finset.mem_union] at h1
            rcases h1 with h3 | h4
            · left
              refine And.intro ?_ h1'
              simp_all
            simp_all
          right
          refine And.intro h2 ?_
          intro hxA
          simp_all
        use a1
        apply And.intro
        · refine Finset.mem_symmDiff.mpr ?_
          left
          exact Finset.mem_sdiff.mp ha1
        intro h
        rw[Finset.mem_symmDiff] at h
        rcases h with h1 | h2
        · apply h1.right
          simp_all
        have : a1 ∉ A' := by
          simp_all
        exact this h2.left
      set k := (symmDiff A3 A').card with hk
      apply hmin k this
      use A3
      apply And.intro
      · have : A.erase a1 ∈ 𝒜.shadow := by
          rw[Finset.mem_shadow_iff]
          use A
          refine And.intro hA ?_
          use a1
          refine And.intro ?_ rfl
          exact (Finset.mem_sdiff.mp ha1).left
        unfold A3
        have ha2ni: a2 ∉ A.erase a1 := by
          have := (Finset.mem_sdiff.mp ha2).right
          simp_all
        exact hhh (A.erase a1) this a2 ha2ni
      use A'
    intros
    rfl
  intro h
  symm
  rcases h with he | h
  · have hse : 𝒜.shadow = ∅ := by
      rw[he]
      exact Finset.shadow_empty
    have : 𝒜.shadow.card = 0 := by
      exact Finset.card_eq_zero.mpr hse
    rw[this]
    ring_nf
    rw[incidences_card_eq_sum_upperFiber]
    rw[hse]
    exact Finset.sum_empty
  have : 𝒜.shadow = Layer n (r - 1) := by
    unfold Layer
    refine Finset.ext_iff.mpr ?_
    intro B
    apply Iff.intro
    · intro hB
      refine Finset.mem_powersetCard_univ.mpr ?_
      obtain ⟨A, hA, _, _⟩ := Finset.mem_shadow_iff_exists_mem_card_add_one.mp hB
      have := mem_layer_card_nat 𝒜 A hA h𝒜
      omega
    intro hB
    rw [Finset.mem_powersetCard_univ] at hB
    rw[h]
    unfold Layer
    rw[Finset.mem_shadow_iff_exists_mem_card_add_one]
    have : ∃ x : Fin n, x ∉ B := by
      by_contra!
      have : B.card = n := by
        have : B = (Finset.univ : Finset (Fin n)) := by
          exact Finset.eq_univ_iff_forall.mpr this
        rw[this]
        exact Finset.card_fin n
      omega
    obtain ⟨x, hx⟩ := this
    use insert x B
    refine And.intro ?_ ?_
    · refine Finset.mem_powersetCard_univ.mpr ?_
      rw[Finset.card_insert_of_notMem hx]
      omega
    refine And.intro ?_ ?_
    · exact Finset.subset_insert x B
    exact Finset.card_insert_of_notMem hx
  rw[this]
  rw[incidences_card_eq_sum_upperFiber]
  symm
  calc Finset.card (Layer n (r - 1)) * (n - (r - 1))
    = ∑ B ∈ Layer n (r - 1), (n - (r - 1)) := by
        rw[←Finset.sum_const_nat (f := fun _ => (n - (r - 1)))]
        intros
        rfl
  _ = ∑ B ∈ Finset.shadow 𝒜, Finset.card (upperFiber 𝒜 B) := by
        rw[this]
        refine Finset.sum_congr rfl ?_
        intro B hB
        have : B ∈ 𝒜.shadow := by
          rw[this]
          exact hB
        have := t1 𝒜 h𝒜 hr B this
        unfold upperFiber
        rw[h]
        symm
        exact this

theorem G_empty_of_A_empty {n} (hk : k ≤ n) :
    G (∅ : Family n) k = ∅ := by
  induction k with
  |zero =>
    unfold G
    exact Finset.val_eq_zero.mp rfl
  |succ k ih =>
    unfold G
    simp_all only [Order.add_one_le_iff, Finset.union_eq_empty]
    refine ⟨?_, ?_⟩
    · rfl
    rw [ih (le_of_lt hk)]
    exact Finset.shadow_empty




theorem local_lym_mul_eq {n r} (𝒜 : Family n) (hr : 0 < r) (hrn : r ≤ n) (h𝒜 : 𝒜 ⊆ Layer n r) :
    𝒜.shadow.card * (n - (r - 1)) = 𝒜.card * r ↔  𝒜 = ∅ ∨ 𝒜 = Layer n r:= by
  nth_rw 2 [←CountingA]
  · exact (CountingB_eq hr hrn h𝒜)
  exact h𝒜

theorem G_subsets (𝒜 : Family n) (A : Finset (Fin n)) (hA : A ∈ 𝒜) (k : ℕ) (hk : k ≤ n) :
    ∀ B ⊆ A, B.card = (n - k) → B ∈ G 𝒜 k := by
  induction k with
  |zero =>
    intro B hB hBcard
    rw[tsub_zero] at hBcard
    unfold G
    have hBA : B = A := by
      have : A.card ≤ B.card := by
        exact le_of_le_of_eq (card_finset_fin_le A) hBcard.symm
      exact Finset.eq_of_subset_of_card_le hB this
    rw[hBA]
    refine Finset.mem_slice.mpr ?_
    refine ⟨hA, ?_⟩
    rw[←hBA, hBcard]
  |succ k ih =>
    intro B hB hBcard
    unfold G
    simp only [Finset.mem_union]
    have : B ⊂ A ∨ B = A := by
      exact ssubset_or_eq_of_subset hB
    rcases this with h | h
    · have : Finset.Nonempty (A \ B) := by
        rw [Finset.sdiff_nonempty]
        exact not_subset_of_ssubset h
      obtain ⟨x, hx⟩ := this
      rw[Finset.mem_shadow_iff_exists_mem_card_add_one]
      right
      use insert x B
      refine ⟨?_, ?_, ?_⟩
      · have h1 : insert x B ⊆ A := by
          refine Finset.insert_subset ?_ hB
          exact (Finset.mem_sdiff.mp hx).left
        have h2 : (insert x B).card = n - k := by
          rw[Finset.card_insert_of_notMem]
          · rw[hBcard]
            omega
          exact (Finset.mem_sdiff.mp hx).right
        exact ih (Nat.le_of_succ_le hk) (insert x B) h1 h2
      · exact Finset.subset_insert x B
      refine Finset.card_insert_of_notMem ?_
      rw[Finset.mem_sdiff] at hx
      exact hx.right
    left
    rw[Finset.mem_slice]
    refine ⟨?_, ?_⟩
    · rw[h]
      exact hA
    subst h
    simp_all only [subset_refl]




theorem G_local_lym_mul_eq (𝒜 : Family n) :
    ∀ k < n, (G 𝒜 k).shadow.card * (k + 1) = (G 𝒜 k).card * (n - k)
      → (G 𝒜 k) = ∅ ∨ (G 𝒜 k) = Layer n (n - k) := by
  intro k hk h
  have h0 : 0 < n - k := by omega
  have hkn : n - k ≤ n := by omega
  refine (local_lym_mul_eq (G 𝒜 k) h0 hkn ?_).mp ?_
  · exact G_lay 𝒜 k (le_of_lt hk)
  have : (n - (n - k - 1)) = k + 1 := by omega
  rw[this]
  exact h

theorem G_local_lym (𝒜 : Family n) :
    ∀ k < n, ((G 𝒜 k).card : ℚ) / n.choose k ≤ ((G 𝒜 k).shadow.card : ℚ) / n.choose (k + 1) := by
  intro k hk
  have := local_lym (G 𝒜 k) (G_lay 𝒜 k hk.le) (Nat.sub_le n k) (Nat.zero_lt_sub_of_lt hk)
  rw[Nat.choose_symm, (Nat.sub_sub n k 1), Nat.choose_symm] at this
  · exact this
  · exact Nat.succ_le_of_lt hk
  exact hk.le


theorem Gn_empty_iff (𝒜 : Family n) :
    (G 𝒜 n) = ∅ ↔ 𝒜 = ∅ := by
  apply Iff.intro
  · intro h
    by_contra!
    obtain ⟨A, hA⟩ := this
    have := G_subsets 𝒜 A hA n (Nat.le_refl n) ∅ (Finset.empty_subset A) (by aesop)
    simp_all only [Finset.notMem_empty]
  intro h
  rw[h]
  exact G_empty_of_A_empty (Nat.le_refl n)


theorem G123 (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (hne : Finset.Nonempty 𝒜)
    (h : ∀ k ≤ n, (G 𝒜 k) = ∅ ∨ (G 𝒜 k) = Layer n (n - k)) :
    ∃ i ≤ n, 𝒜.slice i = Layer n i := by
  by_cases hEx : ∃ i ≤ n, G 𝒜 i = Layer n (n - i)
  · set b := Nat.find hEx with hb
    have hspec := Nat.find_spec hEx
    rcases hspec with ⟨hbn, hG⟩
    rw[←hb] at hbn
    have hG : G 𝒜 b = Layer n (n - b) := by
      exact Finset.val_inj.mp (congrArg Finset.val hG)
    use (n - b)
    have hmin : ∀ (i : ℕ) (hi : i < b), G 𝒜 i = ∅ := by
      intro i hi
      have hile : i ≤ n := (Nat.le_trans (Nat.le_of_lt hi) hbn)
      have hneq : G 𝒜 i ≠ Layer n (n - i) := by
        intro hEq
        apply (Nat.find_min hEx hi)
        exact ⟨hile, hEq⟩
      exact Or.resolve_right (h i hile) hneq
    refine ⟨Nat.sub_le n b, ?_⟩
    rcases b with h0 | c
    · unfold G at hG
      simp only [tsub_zero]
      simp only [tsub_zero] at hG
      exact hG
    unfold G at hG
    have hem := hmin c (by omega)
    rw[hem, Finset.shadow_empty, Finset.union_empty] at hG
    exact hG
  simp_all
  have : 𝒜 = ∅ := by
    exact (Gn_empty_iff 𝒜).mp (h n (Nat.le_refl n))
  subst this
  simp_all only [Finset.not_nonempty_empty]



theorem layer_maximal (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) (i : ℕ) (hin : i ≤ n)
    (h : 𝒜.slice i = Layer n i) :
    𝒜 = Layer n i := by
  by_contra! h'
  have : Layer n i ⊂ 𝒜 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · rw[←h]
      exact Finset.slice_subset
    symm
    exact h'
  have : Finset.Nonempty (𝒜 \ Layer n i) := by
    refine Finset.sdiff_nonempty.mpr ?_
    exact not_subset_of_ssubset this
  obtain ⟨A, hA⟩ := this
  rw[Finset.mem_sdiff] at hA
  have : A.card < i ∨ A.card > i := by
    refine Nat.lt_or_gt_of_ne ?_
    intro h
    apply hA.right
    unfold Layer
    exact Finset.mem_powersetCard_univ.mpr h
  rcases this with b | b
  · have : ∃ B ⊇ A, B.card = i := by
      refine Finset.exists_superset_card_eq ?_ ?_
      · exact le_of_lt b
      rw [Fintype.card_fin]
      exact hin
    obtain ⟨B, hBA, hB⟩ := this
    unfold IsSubsetAntichain at h𝒜
    have : B ∈ 𝒜 := by
      exact Finset.mem_of_subset this.subset (Finset.mem_powersetCard_univ.mpr hB)
    have hAeqB := h𝒜.eq hA.left this hBA
    rw[hAeqB] at b
    omega
  have : ∃ B ⊆ A, B.card = i := by
    refine Finset.le_card_iff_exists_subset_card.mp ?_
    omega
  obtain ⟨B, hBA, hB⟩ := this
  have : B ∈ 𝒜 := by
    exact Finset.mem_of_subset this.subset (Finset.mem_powersetCard_univ.mpr hB)
  have hAeqB := h𝒜.eq this hA.left hBA
  rw[hAeqB] at hB
  omega


theorem Gn_or (𝒜 : Family n) (hn : n ≤ n) :
    G 𝒜 n = ∅ ∨ G 𝒜 n = Layer n 0 := by
  have h:= G_lay 𝒜 n hn
  rw[Nat.sub_self] at h
  have : Layer n 0 = {∅} := by
    exact Finset.powersetCard_zero Finset.univ
  rw[this]
  rw[this] at h
  rw [←Finset.subset_singleton_iff]
  exact h

theorem form_change (a b n k : ℕ) (hk : k < n) :
    b * (k + 1) = a * (n - k) ↔ (b : ℚ) / n.choose (k + 1) = (a : ℚ) / n.choose k := by
  have : ↑(n.choose k) ≠ 0 := by
    exact Nat.choose_ne_zero_iff.mpr hk.le
  have : ↑(n.choose (k + 1)) ≠ 0 := by
    exact Nat.choose_ne_zero_iff.mpr hk
  apply Iff.intro
  · intro h
    field_simp
    rw [←Nat.cast_mul, ←Nat.cast_mul, Rat.natCast_inj]
    have hk1 : k + 1 ≠ 0 := by
      exact Ne.symm (Nat.zero_ne_add_one k)
    refine mul_right_cancel₀ hk1 ?_
    rw[Nat.mul_assoc, Nat.mul_comm (n.choose k), ← Nat.mul_assoc, h,
      Nat.mul_assoc (n.choose (k + 1)), Nat.mul_comm a (k + 1), ←Nat.mul_assoc (n.choose (k + 1)),
      Nat.choose_succ_right_eq]
    ring_nf
  intro h
  field_simp at h
  rw [←Nat.cast_mul, ←Nat.cast_mul, Rat.natCast_inj] at h
  rw[Nat.mul_comm]
  refine mul_left_cancel₀ this ?_
  rw[←Nat.mul_assoc, ←Nat.mul_assoc, ←h, Nat.choose_succ_right_eq]
  ring


theorem G_local_lym_eq (𝒜 : Family n) (k : ℕ) (hk : k < n)
    (h : ((G 𝒜 k).card : ℚ) / n.choose k = ((G 𝒜 k).shadow.card : ℚ) / n.choose (k + 1)) :
    (G 𝒜 k) = ∅ ∨ (G 𝒜 k) = Layer n (n - k) := by
  refine G_local_lym_mul_eq 𝒜 k hk ?_
  refine (form_change (G 𝒜 k).card (G 𝒜 k).shadow.card n k hk).mpr h.symm


theorem lym_eq'' (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜)
    (hc : ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ) / (n.choose r) = 1) :
    ∀ k ≤ n, ∑ r ∈ Finset.range (k + 1),
      ((𝒜.slice (n - r)).card : ℚ) / (n.choose (n - r)) = ((G 𝒜 k).card : ℚ) / n.choose k := by
  by_contra! ⟨k, hkn, hk⟩
  have hk := lt_of_le_of_ne (lym_sum 𝒜 h𝒜 k hkn) hk
  have : ∀ (i : ℕ), k ≤ i → i ≤ n → ∑ r ∈ Finset.range (i + 1),
      ((𝒜.slice (n - r)).card : ℚ) / n.choose (n - r) < ((G 𝒜 i).card : ℚ) / n.choose i := by
    intro i hki hin
    have h : ∀ d, ∀ j, j = k + d → j ≤ n →  ∑ r ∈ Finset.range (j + 1),
        ((𝒜.slice (n - r)).card : ℚ) / n.choose (n - r) < ((G 𝒜 j).card : ℚ) / n.choose j := by
      intro d
      induction d with
      |zero =>
        intro j hjk hjn
        rw[add_zero] at hjk
        subst hjk
        exact hk
      |succ j' ih =>
        intro j hjk hjn
        have ih := ih (k + j') rfl (by omega)
        calc ∑ r ∈ Finset.range (j + 1), ((𝒜.slice (n - r)).card : ℚ) / n.choose (n - r)
          = ∑ r ∈ Finset.range (k + j' + 1 + 1),
            ((𝒜.slice (n - r)).card : ℚ) / n.choose (n - r) := by
              rw[hjk]
              ring_nf
        _ = ∑ r ∈ Finset.range (k + j' + 1), ((𝒜.slice (n - r)).card : ℚ) / n.choose (n - r)
            + ((𝒜.slice (n - (k + j' + 1))).card : ℚ) / n.choose (n - (k + j' + 1)) := by
              rw[Finset.sum_range_succ
                (fun x ↦ ((𝒜.slice (n-x)).card : ℚ) / n.choose (n - x)) (k + j' + 1)]
        _ < ((G 𝒜 (k + j')).card : ℚ) / n.choose (k + j')
            + ((𝒜.slice (n - (k + j' + 1))).card : ℚ) / n.choose (k + j' + 1) := by
              rw[Nat.choose_symm]
              · exact Rat.add_lt_add_right.mpr ih
              omega
        _ ≤ ((G 𝒜 (k + j')).shadow.card : ℚ ) / n.choose (k + j' + 1)
              + ((𝒜.slice (n - (k + j' + 1))).card : ℚ) / n.choose (k + j' + 1) := by
              refine Rat.add_le_add_right.mpr ?_
              exact G_local_lym 𝒜 (k + j') (by omega)
        _ = ((G 𝒜 (k + j')).shadow.card
              + (𝒜.slice (n - (k + j' + 1))).card : ℚ) / n.choose (k + j' + 1) := by
              field
        _ = ((G 𝒜 (k + j' + 1)).card : ℚ) / n.choose (k + j' + 1) := by
              rw[G_card 𝒜 h𝒜 (k + j')]
              · aesop
              omega
        _ = ((G 𝒜 j).card : ℚ) / n.choose j := by
              rw[hjk]
              ring_nf
    have : i = k + (i - k) := by omega
    exact h (i - k) i this hin
  have h:= this n hkn n.le_refl
  have h' : ((G 𝒜 n).card : ℚ) / n.choose n ≤ 1 := by
    rw[Nat.choose_self, ←Nat.cast_div, Nat.div_one]
    · exact Nat.cast_le_one.mpr (Gn_card 𝒜)
    · exact Nat.one_dvd (Finset.card (G 𝒜 n))
    exact Rat.abs_pos_iff.mp rfl
  apply ne_of_lt (lt_of_lt_of_le h h')
  rw[← hc]
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
  intros
  rfl

theorem lym_eq' (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜)
    (hc : ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ) / (n.choose r) = 1) :
    ∀ k < n, ((G 𝒜 k).card : ℚ) / n.choose k = ((G 𝒜 k).shadow.card : ℚ) / n.choose (k + 1) := by
  by_contra! ⟨k, hkn, hG⟩
  have hG := lt_of_le_of_ne (G_local_lym 𝒜 k hkn) hG
  set Sk1 := ∑ r ∈ Finset.range (k + 1 + 1),
      ((𝒜.slice (n - r)).card : ℚ) / (n.choose (n - r)) with hSk1
  set Sk := ∑ r ∈ Finset.range (k + 1),
      ((𝒜.slice (n - r)).card : ℚ) / (n.choose (n - r)) with hSk
  have h1: Sk1 = ((G 𝒜 (k + 1)).card : ℚ) / n.choose (k + 1) :=
    lym_eq'' 𝒜 h𝒜 hc (k + 1) (Nat.succ_le_of_lt hkn)
  have h2: Sk ≤ ((G 𝒜 k).card : ℚ) / n.choose k := by
    exact lym_sum 𝒜 h𝒜 k hkn.le
  have h3: Sk1 = Sk + ((𝒜.slice (n - (k + 1))).card : ℚ) / n.choose (k + 1) := by
    have h := Finset.sum_range_succ (fun x ↦ ((𝒜.slice (n-x)).card : ℚ) / n.choose (n - x)) (k + 1)
    rw[←hSk, ←hSk1, Nat.choose_symm] at h
    · exact h
    exact Order.add_one_le_iff.mpr hkn
  have h4: Sk1 < ((G 𝒜 (k + 1)).card : ℚ) / n.choose (k + 1) := by
    calc Sk1
      = Sk + ((𝒜.slice (n - (k + 1))).card : ℚ) / n.choose (k + 1) := by assumption
    _ ≤ ((G 𝒜 k).card : ℚ) / n.choose k
      + ((𝒜.slice (n - (k + 1))).card : ℚ) / n.choose (k + 1) := by
        exact Rat.add_le_add_right.mpr h2
    _ < ((G 𝒜 k).shadow.card : ℚ) / n.choose (k + 1)
      + ((𝒜.slice (n - (k + 1))).card : ℚ) / n.choose (k + 1) := by
        exact Rat.add_lt_add_right.mpr hG
    _ = (((G 𝒜 k).shadow.card : ℚ) + ((𝒜.slice (n - (k + 1))).card : ℚ)) / n.choose (k + 1) := by
        field_simp
    _ = ((G 𝒜 (k + 1)).card : ℚ) / n.choose (k + 1) := by
        rw[←Nat.cast_add, G_card 𝒜 h𝒜 k hkn]
  refine (lt_self_iff_false Sk1).mp ?_
  rw[←h1] at h4
  exact h4



theorem lym_eq (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜)
    (hc : ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ) / (n.choose r) = 1) :
    ∃ i ≤ n, 𝒜 = Layer n i := by
  have := lym_eq' 𝒜 h𝒜 hc
  have : ∀ k ≤ n, (G 𝒜 k) = ∅ ∨ (G 𝒜 k) = Layer n (n - k) := by
    intro k hk
    rcases hk.lt_or_eq with hlt | heq
    · exact G_local_lym_eq 𝒜 k hlt (this k hlt)
    subst k
    rw[Nat.sub_self]
    exact Gn_or 𝒜 hk
  have hnon: Finset.Nonempty 𝒜 := by
    by_contra!
    have : ∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ) / n.choose r = 0 := by
      rw[Finset.sum_eq_zero_iff_of_nonneg]
      · intro i hi
        rw[this]
        aesop
      intro i hi
      refine Rat.div_nonneg ?_ ?_
      · exact Rat.natCast_nonneg
      exact Rat.natCast_nonneg
    rw[this] at hc
    exact zero_ne_one hc
  have : ∃ i ≤ n, 𝒜.slice i = Layer n i := G123 𝒜 h𝒜 hnon this
  obtain ⟨i, hi, hL⟩ := this
  exact ⟨i, hi, layer_maximal 𝒜 h𝒜 i hi hL⟩

theorem choose_le_succ_of_lt_half_left {r n : ℕ} (h : r < n / 2) :
    n.choose r < n.choose (r + 1) := by
  have : n.choose r * (n - r) < n.choose (r + 1) * (n - r) := by
    rw[← Nat.choose_succ_right_eq]
    have : 0 < n.choose (r + 1) := by
      refine Nat.choose_pos ?_
      omega
    refine Nat.mul_lt_mul_of_pos_left ?_ this
    omega
  refine Nat.lt_of_mul_lt_mul_right this

theorem eq_middle_of_choose_eq_even (n r : ℕ) (he : Even n) (h : n.choose r = n.choose (n / 2)) :
    r = n / 2 := by
  by_contra!
  rcases lt_or_gt_of_ne this with b | b
  · have := choose_le_succ_of_lt_half_left b
    have := lt_of_lt_of_le this (Nat.choose_le_middle (r + 1) n)
    simp_all only [ne_eq, lt_self_iff_false]
  have hrn : r ≤ n := by
    by_contra!
    rw [Nat.choose_eq_zero_of_lt this] at h
    have := Nat.choose_eq_zero_iff.mp h.symm
    omega
  rw[←Nat.choose_symm hrn] at h
  have : n < 2 * r := by
    omega
  have : n - r < n / 2 := by
    have : 2 * (n - r) < 2 * (n / 2) := by
      have : 2 * (n / 2) = n := by
        exact Nat.two_mul_div_two_of_even he
      rw[this]
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  have := lt_of_lt_of_le (choose_le_succ_of_lt_half_left this) (Nat.choose_le_middle (n-r+1) n)
  omega

theorem eq_middle_of_choose_eq_odd (n r : ℕ) (h : n.choose r = n.choose (n / 2)) :
    r = n / 2 ∨ r = n / 2 + 1 := by
  by_contra!
  have : r < n / 2 ∨ r > n / 2 + 1 := by
    omega
  rcases this with b | b
  · have := Nat.lt_of_lt_of_le (choose_le_succ_of_lt_half_left b) (Nat.choose_le_middle (r + 1) n)
    omega
  have hrn : r ≤ n := by
    by_contra!
    rw [Nat.choose_eq_zero_of_lt this] at h
    have := Nat.choose_eq_zero_iff.mp h.symm
    omega
  rw[←Nat.choose_symm hrn] at h
  have : n - r < n / 2 := by
    omega
  have := lt_of_lt_of_le (choose_le_succ_of_lt_half_left this) (Nat.choose_le_middle (n - r + 1) n)
  omega

theorem Nat.choose_eq_middle_even (n r : ℕ) :
    n.choose r = n.choose (n / 2) ↔ (Even n ∧ r = n / 2) ∨
      (Odd n ∧ (r = n / 2 ∨ r = n / 2 + 1)) := by
  apply Iff.intro
  · intro h
    rcases Nat.even_or_odd n with he | ho
    · left
      refine ⟨he, ?_⟩
      exact eq_middle_of_choose_eq_even n r he h
    right
    refine ⟨ho, ?_⟩
    exact eq_middle_of_choose_eq_odd n r h
  intro a
  cases a with
  | inl h => simp_all only
  | inr h_1 =>
    obtain ⟨left, right⟩ := h_1
    cases right with
    | inl h =>
      subst h
      simp_all only
    | inr h_1 =>
      subst h_1
      refine Nat.choose_symm_of_eq_add ?_
      ring_nf
      exact Eq.symm (Nat.one_add_div_two_mul_two_of_odd left)

theorem sperners_eq (𝒜 : Family n) (h𝒜 : IsSubsetAntichain 𝒜) :
    𝒜.card = n.choose (n / 2) ↔ (Even n ∧ 𝒜 = Layer n (n / 2)) ∨
      (Odd n ∧ (𝒜 = Layer n (n / 2) ∨ 𝒜 = Layer n (n / 2 + 1))) := by
  apply Iff.intro
  · intro h
    have h' : ∑ r ∈ Finset.range (n + 1),
        ((𝒜.slice r).card : ℚ)  / (n.choose r) = 1 := by
      by_contra!
      have hne0: (n.choose (n / 2) : ℚ) ≠ 0 := by
        rw[Nat.cast_ne_zero]
        refine Nat.choose_ne_zero_iff.mpr ?_
        omega
      have := lt_of_le_of_ne (lym 𝒜 h𝒜) this
      have : (𝒜.card : ℚ) / (n.choose (n / 2)) < 1 := by
        calc (𝒜.card : ℚ) / (n.choose (n / 2))
          = (∑ r ∈ Finset.range (n + 1), ((𝒜.slice r).card : ℚ)) / n.choose (n / 2) := by
              have : 𝒜.card = ∑ r ∈ Finset.range (n + 1), (𝒜.slice r).card := by
                symm
                have : Finset.Iic  (Fintype.card (Fin n)) = Finset.range (n + 1) := by
                  ext i
                  rw[Finset.mem_Iic]
                  aesop
                rw[←this]
                exact Finset.sum_card_slice 𝒜
              rw[this]
              simp only [Nat.cast_sum]
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
        _ < 1 := by
              exact this
      rw[h] at this
      have dself:= div_self_eq_one₀.mpr hne0
      rw[dself] at this
      exact (Bool.eq_not_self (Rat.blt 1 1)).mp this
    have := (lym_eq 𝒜 h𝒜 h')
    obtain ⟨r, hrn, heq⟩ := this
    rcases (Nat.even_or_odd n) with he | ho
    · left
      refine And.intro he ?_
      rw[heq]
      rw[heq, card_layer] at h
      have : r = n / 2 := by
        exact eq_middle_of_choose_eq_even n r he h
      rw[this]
    right
    refine ⟨ho, ?_⟩
    rw[heq]
    rw[heq, card_layer] at h
    have : r = n / 2 ∨ r = n / 2 + 1 := by
      exact eq_middle_of_choose_eq_odd n r h
    rcases this with b | b
    · left
      rw[b]
    right
    rw[b]
  intro h
  rcases h with ⟨he, heq⟩ | ⟨ho, heq⟩
  · rw[heq]
    exact card_layer
  rcases heq with h1 | h2
  · rw[h1]
    exact card_layer
  rw[h2, card_layer]
  refine Nat.choose_symm_of_eq_add ?_
  ring_nf
  exact Eq.symm (Nat.one_add_div_two_mul_two_of_odd ho)

end Sperners
