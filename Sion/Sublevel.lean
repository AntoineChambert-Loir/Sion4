import Mathlib.Data.Set.Basic
import Sion.Semicontinuous

namespace Set

variable {E β : Type*}

section LE

variable [LE β]

/-- The sublevel sets of `f`. -/
def LeSublevel (f : E → β) (b : β) : Set E := { x | f x ≤ b }

/-- The sublevel sets of `f` on `s`. -/
def LeSublevelOn (s : Set E) (f : E → β) (b : β) : Set E := { x ∈ s | f x ≤ b }

/-- The overlevel sets of `f`. -/
def LeOverlevel (f : E → β) (b : β) : Set E := { x | b ≤ f x }

/-- The overlevel sets of `f` on `s`. -/
def LeOverlevelOn (s : Set E) (f : E → β) (b : β) : Set E := { x ∈ s | b ≤ f x }

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

theorem inter_leSublevelOn_empty_iff_exists_finset_inter
    {ι : Type*} {f : ι → E → β} {I : Set ι}
    (ne_I : I.Nonempty) [TopologicalSpace E] (ks : IsCompact s)
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔
      ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, b < f i x := by
  have : Nonempty I := Nonempty.to_subtype ne_I
  constructor
  · intro H
    apply ks.induction_on
      (p := fun s ↦ ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, b < f i x)
    · use ∅, by simp
    · rintro s t hst ⟨u, hu⟩
      use u, fun x a ↦ hu x (hst a)
    · classical
      rintro s t ⟨u, hu⟩ ⟨v, hv⟩
      use u ∪ v
      rintro x (hx | hx)
      · obtain ⟨i, hi, hx⟩ := hu x hx
        use i, Finset.mem_union_left v hi, hx
      · obtain ⟨i, hi, hx⟩ := hv x hx
        use i, Finset.mem_union_right u hi, hx
    · intro x hx
      simp only [eq_empty_iff_forall_notMem] at H
      specialize H x
      simp only [mem_iInter, not_forall, Classical.not_imp] at H
      obtain ⟨i, hi, H⟩ := H
      simp only [mem_leSublevelOn_iff, hx, true_and, not_le] at H
      specialize hfi i hi x hx b H
      simp only [Filter.Eventually] at hfi
      use {x | b < f i x}, hfi, {⟨i, hi⟩}
      intro x hx
      use ⟨i, hi⟩, by simp, hx
  · rintro ⟨u, hu⟩
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    simp only [mem_iInter, mem_leSublevelOn_iff] at hx
    have hxs : x ∈ s := by
      obtain ⟨i , hi⟩ := ne_I
      exact (hx i hi).1
    obtain ⟨i, hiu, hv⟩ := hu x hxs
    apply lt_irrefl b (lt_of_lt_of_le hv (hx i i.prop).2)

/-- Variant of `LowerSemicontinuousOn.inter_leSubleveOn_empty_iff_exists_finset_inter` where `s` is assumed to be nonempty. -/
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
  have et' (i : ι) : ∃ f : Set X, IsClosed f ∧ s ∩ f = s ∩ t i := by
    obtain ⟨f, hf, hf'⟩ := Topology.IsInducing.subtypeVal.isClosed_iff.mp (htc i)
    rw [Subtype.preimage_coe_eq_preimage_coe_iff] at hf'
    refine ⟨f, hf, hf'⟩
  let t' (i) := (et' i).choose
  have ht' (i) : IsClosed (t' i) := (et' i).choose_spec.1
  have ht's (i) : s ∩ t' i = s ∩ t i := (et' i).choose_spec.2
  suffices s ∩ ⋂ i, t' i = ∅ by
    obtain ⟨u, hu⟩ := IsCompact.elim_finite_subfamily_closed hs t' ht' this
    use u
    rcases (u : Set ι).eq_empty_or_nonempty with hu_e | hu_ne
    · simp only [Finset.coe_eq_empty] at hu_e
      simpa only [hu_e, Finset.notMem_empty, iInter_of_empty, iInter_univ, inter_univ] using hu
    simp_rw [← Finset.mem_coe] at hu ⊢
    rw [← Set.inter_biInter] at hu ⊢
    rw [← hu]
    apply Set.iInter₂_congr
    simp [ht's]
    trivial
    trivial
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa [hι] using hst
  · simp_rw [Set.inter_iInter, ht's, ← Set.inter_iInter]
    exact hst


example
    {ι : Type*} {f : ι → E → β} {I : Set ι}
    (ne_I : I.Nonempty) [TopologicalSpace E] (ks : IsCompact s)
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔
      ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, b < f i x := by
  have : Nonempty I := Nonempty.to_subtype ne_I
  constructor
  · intro H
    obtain ⟨u, hu⟩ := IsCompact.elim_finite_subfamily_closedOn ks
      (fun (i : I) ↦ LeSublevelOn s (f i) b)
      (fun i ↦ by
        specialize hfi i i.prop
        rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfi
        obtain ⟨v, hv, hv'⟩ := hfi b
        rw [Topology.IsInducing.subtypeVal.isClosed_iff]
        use v, hv
        rw [Subtype.preimage_coe_eq_preimage_coe_iff, ← hv']
        ext
        simp [LeSublevelOn])
      (by
        rw [Set.eq_empty_iff_forall_notMem] at H ⊢
        rintro x ⟨hx, hxb⟩
        simp only [iInter_coe_set, mem_iInter] at hxb
        simp only [mem_iInter, not_forall, Classical.not_imp] at H
        obtain ⟨i, hi, hxi⟩ := H x
        exact hxi (hxb i hi))
    use u
    rw [Set.eq_empty_iff_forall_notMem] at hu
    intro x hx
    specialize hu x
    simp only [iInter_coe_set, mem_inter_iff, hx, mem_iInter, true_and, not_forall,
      Classical.not_imp, exists_and_right] at hu
    obtain ⟨i, hiI, hiu, hib⟩ := hu
    refine ⟨⟨i, hiI⟩, hiu, ?_⟩
    simp only [mem_leSublevelOn_iff, not_and, not_le] at hib
    exact hib hx
  · rintro ⟨u, hu⟩
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    simp only [mem_iInter, mem_leSublevelOn_iff] at hx
    have hxs : x ∈ s := by
      obtain ⟨i , hi⟩ := ne_I
      exact (hx i hi).1
    obtain ⟨i, hiu, hv⟩ := hu x hxs
    apply lt_irrefl b (lt_of_lt_of_le hv (hx i i.prop).2)


end LinearOrder


