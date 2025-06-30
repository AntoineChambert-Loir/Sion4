import Mathlib.Data.Set.Basic
import Sion.Semicontinuous

namespace Set

variable {E β : Type*}

section LE

variable [LE β]

def LeSublevel (f : E → β) (b : β) : Set E := { x | f x ≤ b }

/-- The sublevel set of `f` on `s`. -/
def LeSublevelOn (s : Set E) (f : E → β) (b : β) : Set E := { x ∈ s | f x ≤ b }

variable {s : Set E} {f : E → β} {b : β}

theorem mem_leSublevelOn_iff {x : E} :
    x ∈ LeSublevelOn s f b ↔ x ∈ s ∧ f x ≤ b := by
  simp [LeSublevelOn]

theorem leSublevelOn_subset : LeSublevelOn s f b ⊆ s :=
  fun _ hx ↦ hx.1

theorem le_of_mem_leSublevelOn {x : E} (hx : x ∈ LeSublevelOn s f b) :
    f x ≤ b := hx.2

end LE

section LT

variable [LT β]

variable {s : Set E} {f : E → β} {b : β}

def LtSublevelOn (s : Set E) (f : E → β) (b : β) :=
  { x ∈ s | f x < b }

end LT

section Preorder

variable [Preorder β]

variable {s : Set E} {f : E → β} {b : β}

theorem leSublevelOn_eq_inter : LeSublevelOn s f b = s ∩ f ⁻¹' (Iic b) := rfl

end Preorder

section LinearOrder

variable [LinearOrder β]

variable {s : Set E} {f : E → β} {b : β}

theorem leSublevelOn_empty_iff :
    LeSublevelOn s f b = ∅ ↔ ∀ x ∈ s, b < f x := by
  simp [LeSublevelOn]

theorem biInter_leSublevelOn_empty_iff {ι : Type*} {f : ι → E → β} {I : Set ι}
    (ne_I : I.Nonempty) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔ ∀ x ∈ s, ∃ i ∈ I, b < f i x := by
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  by_cases hx : x ∈ s <;>
    simp [hx, mem_leSublevelOn_iff, mem_iInter]
  exact ne_I

theorem biInter_leSublevelOn_empty_iff' {ι : Type*} {f : ι → E → β} {I : Set ι}
    (ne_s : s.Nonempty) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔ ∀ x ∈ s, ∃ i ∈ I, b < f i x := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_I
  · have ne_E : Nonempty E := Exists.nonempty ne_s
    simpa
  exact biInter_leSublevelOn_empty_iff ne_I

theorem isClosed_leSublevelOn [TopologicalSpace E] (hf : LowerSemicontinuousOn f s) (hs : IsClosed s) :
    IsClosed (LeSublevelOn s f b : Set E) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hf
  obtain ⟨v, hv, hv'⟩ := hf b
  rw [leSublevelOn_eq_inter, hv']
  exact IsClosed.inter hs hv

theorem isCompact_leSublevelOn [TopologicalSpace E] (hf : LowerSemicontinuousOn f s) (ks : IsCompact s) :
    IsCompact (LeSublevelOn s f b : Set E) := by
  suffices LeSublevelOn s f b = Subtype.val '' (Subtype.val ⁻¹' (LeSublevelOn s f b) : Set s) by
    rw [this, ← Topology.IsInducing.subtypeVal.isCompact_iff]
    haveI ks' : CompactSpace s := isCompact_iff_compactSpace.mp ks
    apply IsClosed.isCompact
    rw [Topology.IsInducing.subtypeVal.isClosed_iff]
    rw [lowerSemicontinuousOn_iff_preimage_Iic] at hf
    obtain ⟨v, hv, hv'⟩ := hf b
    use v, hv
    rw [Subtype.preimage_coe_eq_preimage_coe_iff, ← hv']
    ext x
    simp [mem_leSublevelOn_iff]
  simp [leSublevelOn_subset]

-- We need a better elimination theorem for intersections in a compact subset
-- which are closed in the compact subset and not necessarily in the ambient space
theorem inter_leSublevelOn_empty_iff_exists_finset_inter {ι : Type*} {f : ι → E → β} {I : Set ι}
    (ne_I : I.Nonempty) [TopologicalSpace E] (ks : IsCompact s)
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔
      ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, b < f i x := by
  have : Nonempty I := Nonempty.to_subtype ne_I
  let sl (i : I) : Set s := Subtype.val ⁻¹' (LeSublevelOn s (f i) b)
  have e_csl' (i) : ∃ t : Set E, IsClosed t ∧ sl i = s ∩ t := by
    specialize hfi i.val i.prop
    rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfi
    obtain ⟨v, v_closed, hv⟩ := hfi b
    use v, v_closed
    simp [← hv, sl, leSublevelOn_eq_inter]
  let sl' (i) := (e_csl' i).choose
  have closed_sl' (i) : IsClosed (sl' i) := (e_csl' i).choose_spec.1
  have inter_sl' (i) : sl i = s ∩ sl' i := (e_csl' i).choose_spec.2
  have : ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔ s ∩ ⋂ i, sl' i = ∅ := by
    rw [Set.inter_iInter s]
    simp_rw [← inter_sl', sl]
    simp only [Subtype.image_preimage_coe, iInter_coe_set]
    nth_rewrite 2 [Set.biInter_eq_iInter]
    rw [← Set.inter_iInter s, Set.inter_eq_self_of_subset_right, Set.biInter_eq_iInter]
    apply subset_trans Set.iInter_subset_iUnion
    simp [leSublevelOn_subset]
  rw [this]
  constructor
  · intro H
    obtain ⟨u, hu⟩ := IsCompact.elim_finite_subfamily_closed ks sl' closed_sl' H
    use u
    rw [Set.ext_iff] at hu
    intro x hx
    specialize hu x
    simp [hx] at hu
    obtain ⟨i, hi, hi', hi''⟩ := hu
    refine ⟨⟨i, hi⟩, hi', ?_⟩
    replace hi'' : x ∉ s ∩ sl' ⟨i, hi⟩ := by simpa [hx] using hi''
    simpa [sl, ← inter_sl', hx, mem_leSublevelOn_iff] using hi''
  · rintro ⟨u, hu⟩
    apply Set.eq_empty_of_forall_notMem
    intro x
    by_cases hx : x ∈ s
    · simp_rw [inter_iInter, ← inter_sl']
      simp only [Subtype.image_preimage_coe, iInter_coe_set, mem_iInter, mem_inter_iff, hx,
        mem_leSublevelOn_iff, true_and, not_forall, Classical.not_imp, not_le, sl]
      obtain ⟨i, hi, hi'⟩ := hu x hx
      exact ⟨i, i.prop, hi'⟩
    · exact fun hx' ↦ hx (mem_of_mem_inter_left hx')


-- We need a better elimination theorem for intersections in a compact subset
-- which are closed in the compact subset and not necessarily in the ambient space
theorem inter_leSublevelOn_empty_iff_exists_finset_inter' {ι : Type*} {f : ι → E → β} {I : Set ι}
    (ne_s : s.Nonempty)
    [TopologicalSpace E] (ks : IsCompact s)
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔
      ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, b < f i x := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_I
  · have ne_E : Nonempty E := Exists.nonempty ne_s
    simpa
  apply inter_leSublevelOn_empty_iff_exists_finset_inter ne_I ks hfi

theorem IsCompact.elim_finite_subfamily_closedOn {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s)
    {ι : Type*} (t : ι → Set X)
    (htc : ∀ (i : ι), IsClosed (Subtype.val ⁻¹' (t i) : Set s))
    (hst : s ∩ ⋂ i, t i = ∅) :
    ∃ u : Finset ι, s ∩ ⋂ i ∈ u, t i = ∅  := by
  sorry


-- We need a better elimination theorem for intersections in a compact subset
-- which are closed in the compact subset and not necessarily in the ambient space
theorem inter_leSublevelOn_empty_iff_exists_finset_inter_var {ι : Type*} {f : ι → E → β} {I : Set ι}
    (ne_I : I.Nonempty) [TopologicalSpace E] (ks : IsCompact s)
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔
      ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, b < f i x := by
  have := IsCompact.elim_finite_subfamily_closedOn ks (fun i ↦ LeSublevel (f i) b) ?_
  · sorry
  · intro i


  have : Nonempty I := Nonempty.to_subtype ne_I
  let sl (i : I) : Set s := Subtype.val ⁻¹' (LeSublevelOn s (f i) b)
  have e_csl' (i) : ∃ t : Set E, IsClosed t ∧ sl i = s ∩ t := by
    specialize hfi i.val i.prop
    rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfi
    obtain ⟨v, v_closed, hv⟩ := hfi b
    use v, v_closed
    simp [← hv, sl, leSublevelOn_eq_inter]
  let sl' (i) := (e_csl' i).choose
  have closed_sl' (i) : IsClosed (sl' i) := (e_csl' i).choose_spec.1
  have inter_sl' (i) : sl i = s ∩ sl' i := (e_csl' i).choose_spec.2
  have : ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔ s ∩ ⋂ i, sl' i = ∅ := by
    rw [Set.inter_iInter s]
    simp_rw [← inter_sl', sl]
    simp only [Subtype.image_preimage_coe, iInter_coe_set]
    nth_rewrite 2 [Set.biInter_eq_iInter]
    rw [← Set.inter_iInter s, Set.inter_eq_self_of_subset_right, Set.biInter_eq_iInter]
    apply subset_trans Set.iInter_subset_iUnion
    simp [leSublevelOn_subset]
  rw [this]
  constructor
  · intro H
    obtain ⟨u, hu⟩ := IsCompact.elim_finite_subfamily_closed ks sl' closed_sl' H
    use u
    rw [Set.ext_iff] at hu
    intro x hx
    specialize hu x
    simp [hx] at hu
    obtain ⟨i, hi, hi', hi''⟩ := hu
    refine ⟨⟨i, hi⟩, hi', ?_⟩
    replace hi'' : x ∉ s ∩ sl' ⟨i, hi⟩ := by simpa [hx] using hi''
    simpa [sl, ← inter_sl', hx, mem_leSublevelOn_iff] using hi''
  · rintro ⟨u, hu⟩
    apply Set.eq_empty_of_forall_notMem
    intro x
    by_cases hx : x ∈ s
    · simp_rw [inter_iInter, ← inter_sl']
      simp only [Subtype.image_preimage_coe, iInter_coe_set, mem_iInter, mem_inter_iff, hx,
        mem_leSublevelOn_iff, true_and, not_forall, Classical.not_imp, not_le, sl]
      obtain ⟨i, hi, hi'⟩ := hu x hx
      exact ⟨i, i.prop, hi'⟩
    · exact fun hx' ↦ hx (mem_of_mem_inter_left hx')







end LinearOrder


