import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Analysis.Convex.Topology
import Sion.Semicontinuous
import Sion.Concavexity

/-! # Sublevel sets -/

open Set in
-- We need a better elimination theorem for intersections in a compact subset
-- which are closed in the compact subset and not necessarily in the ambient space
theorem IsCompact.elim_finite_subfamily_closedOn {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s)
    {ι : Type*} (t : ι → Set X) {I : Set ι}
    (htc : ∀ i ∈ I, IsClosed (Subtype.val ⁻¹' (t i) : Set s))
    (hst : s ∩ ⋂ i ∈ I, t i = ∅) :
    ∃ u : Finset I, s ∩ ⋂ i ∈ u, t i = ∅  := by
  let t' (i : I) : Set s := Subtype.val ⁻¹' (t i)
  have htc' (i : I) : IsClosed (t' i) := htc i.val i.prop
  have := IsCompact.elim_finite_subfamily_closed (s := (Set.univ : Set s)) (ι := I) ?_ t' htc' ?_
  · obtain ⟨u, hu⟩ := this
    use u
    simp [Set.eq_empty_iff_forall_notMem, t'] at hu ⊢
    intro x hx
    obtain ⟨i, ⟨hi, hiu⟩, hi'⟩ := hu x hx
    use i, ⟨hi, hiu⟩
  · exact isCompact_iff_isCompact_univ.mp hs
  · rw [Set.eq_empty_iff_forall_notMem] at hst ⊢
    rintro ⟨x, hx⟩
    specialize hst x
    simp only [iInter_coe_set, univ_inter, mem_iInter, mem_preimage, not_forall, Classical.not_imp,
      t']
    simp [hx] at hst
    obtain ⟨i, hi, hxi⟩ := hst
    use i, hi

open Set Function

namespace Set

variable {α β : Type*}

variable (A : Set α) (f : α → β) (b : β)

section LeSublevel

section LE

variable [LE β]

/-- The sublevel sets of a function -/
def LeSublevel : Set α := { x | f x ≤ b }

/-- The sublevel sets of a function -/
def LeSublevelOn  : Set α := { x ∈ A | f x ≤ b }

variable {A f b}

theorem mem_leSublevel_iff {a : α} :
  a ∈ Set.LeSublevel f b ↔ f a ≤ b := by
  simp [LeSublevel]

theorem mem_leSublevelOn_iff {a : α} :
  a ∈ A.LeSublevelOn f b ↔ a ∈ A ∧ f a ≤ b := by
  simp [LeSublevelOn]

theorem leSublevelOn_eq_inter :
    A.LeSublevelOn f b = A ∩ LeSublevel f b := rfl

theorem leSublevel_restrict_eq_coe_val_preimage :
    LeSublevel (A.restrict f) b = Subtype.val ⁻¹' (A.LeSublevelOn f b) := by
  ext ⟨x, hx⟩
  simp [mem_leSublevel_iff, mem_leSublevelOn_iff, hx]

theorem leSublevelOn_subset : LeSublevelOn A f b ⊆ A :=
  fun _ hx ↦ hx.1

theorem le_of_mem_leSublevelOn  {x : α} (hx : x ∈ LeSublevelOn A f b) :
    f x ≤ b := hx.2

end LE

section LT

variable [LT β]

/-- The sublevel sets of a function -/
def LtSublevel : Set α := { x | f x < b }

/-- The sublevel sets of a function -/
def LtSublevelOn  : Set α := { x ∈ A | f x < b }

variable {A f b}

theorem ltSublevelOn_eq_inter :
    A.LtSublevelOn f b = A ∩ LtSublevel f b := rfl

theorem mem_ltSublevel_iff {a : α} :
  a ∈ Set.LtSublevel f b ↔ f a < b := by
  simp [LtSublevel]

theorem mem_ltSublevelOn_iff {a : α} :
  a ∈ A.LtSublevelOn f b ↔ a ∈ A ∧ f a < b := by
  simp [LtSublevelOn]

theorem ltSublevelOn_eq_coe_val_preimage :
    LtSublevel (A.restrict f) b = Subtype.val ⁻¹' (A.LtSublevelOn f b) := by
  ext ⟨x, hx⟩
  simp [mem_ltSublevel_iff, mem_ltSublevelOn_iff, hx]

end LT

section Preorder

variable [Preorder β]

theorem monotone_leSublevel :
    Monotone (fun (b : β) ↦ LeSublevel f b) :=
  fun _ _ hbc _ hb ↦ le_trans hb hbc

theorem monotone_leSublevelOn :
    Monotone (fun (b : β) ↦ A.LeSublevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, le_trans hb hbc⟩

theorem monotone_ltSublevel :
    Monotone (fun (b : β) ↦ LtSublevel f b) :=
  fun _ _ hbc _ hb ↦ lt_of_lt_of_le hb hbc

theorem monotone_ltSublevelOn :
    Monotone (fun (b : β) ↦ A.LtSublevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, lt_of_lt_of_le hb hbc⟩

end Preorder

section LinearOrder

variable [LinearOrder β]

theorem leSublevelOn_empty_iff :
    LeSublevelOn s f b = ∅ ↔ ∀ x ∈ s, b < f x := by
  simp [LeSublevelOn]

theorem inter_leSublevelOn_empty_iff {ι : Type*} {f : ι → E → β} {I : Set ι} (ne_s : s.Nonempty) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔ ∀ x ∈ s, ∃ i ∈ I, b < f i x := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_I
  · have : ¬(IsEmpty E) := fun _ ↦ IsEmpty.exists_iff.mp ne_s
    simpa [this] using ne_s
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  by_cases hx : x ∈ s <;> simp [hx, mem_leSublevelOn_iff, mem_iInter]
  exact ne_I

theorem inter_ltSublevelOn_empty_iff {ι : Type*} {f : ι → E → β} {I : Set ι} (ne_s : s.Nonempty) :
    ⋂ i ∈ I, LtSublevelOn s (f i) b = ∅ ↔ ∀ x ∈ s, ∃ i ∈ I, b ≤ f i x := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_I
  · have : ¬(IsEmpty E) := fun _ ↦ IsEmpty.exists_iff.mp ne_s
    simpa [this] using ne_s
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  by_cases hx : x ∈ s <;> simp [hx, mem_ltSublevelOn_iff, mem_iInter]
  exact ne_I

variable [TopologicalSpace α]

theorem isClosed_leSublevel_iff :
    (∀ b, IsClosed (LeSublevel f b)) ↔ LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_preimage.symm

theorem isClosed_val_preimage_leSublevelOn_iff :
    (∀ b, IsClosed (Subtype.val ⁻¹' (LeSublevelOn A f b) : Set A)) ↔ LowerSemicontinuousOn f A := by
  rw [lowerSemicontinuousOn_iff_restrict, ← isClosed_leSublevel_iff]
  simp_rw [← leSublevel_restrict_eq_coe_val_preimage]

theorem isClosed_leSublevelOn_iff (hA : IsClosed A) :
    (∀ b, IsClosed (LeSublevelOn A f b)) ↔ LowerSemicontinuousOn f A := by
  simp_rw [leSublevelOn_eq_inter, ← IsClosed.inter_preimage_val_iff,
      Topology.IsInducing.subtypeVal.isClosed_iff]
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  apply forall_congr'
  intro b
  apply exists_congr
  simp only [and_congr_right_iff]
  intro s hs
  rw [Subtype.preimage_val_eq_preimage_val_iff]
  exact eq_comm

theorem isCompact_leSublevelOn (hfA : LowerSemicontinuousOn f A) (kA : IsCompact A) :
    IsCompact (LeSublevelOn A f b) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfA
  obtain ⟨v, hv, hv'⟩ := hfA b
  haveI kA' : CompactSpace A := isCompact_iff_compactSpace.mp kA
  suffices LeSublevelOn A f b = Subtype.val '' (Subtype.val ⁻¹' (LeSublevelOn A f b) : Set A) by
    rw [this, ← Topology.IsInducing.subtypeVal.isCompact_iff]
    apply IsClosed.isCompact
    rw [Topology.IsInducing.subtypeVal.isClosed_iff]
    use v, hv
    rw [Subtype.preimage_coe_eq_preimage_coe_iff, ← hv']
    ext x
    simp [mem_leSublevelOn_iff]
  simp [leSublevelOn_subset]

theorem open_ltSublevel_iff :
    (∀ b, IsOpen (LtSublevel f b)) ↔ UpperSemicontinuous f :=
  upperSemicontinuous_iff_isOpen_preimage.symm

theorem open_val_preimage_ltSublevelOn_iff :
    (∀ b, IsOpen (Subtype.val ⁻¹' (LtSublevelOn A f b) : Set A)) ↔ UpperSemicontinuousOn f A := by
  rw [upperSemicontinuousOn_iff_restrict,
    ← open_ltSublevel_iff]
  simp_rw [← ltSublevelOn_eq_coe_val_preimage]

theorem isOpen_ltSublevelOn_iff (hA : IsOpen A) :
    (∀ b, IsOpen (LtSublevelOn A f b)) ↔ UpperSemicontinuousOn f A := by
  sorry

theorem inter_leSublevelOn_empty_iff_exists_finset_inter {ι : Type*} {f : ι → E → β} {I : Set ι}
    (ne_I : I.Nonempty) [TopologicalSpace E] (ks : IsCompact s)
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    ⋂ i ∈ I, LeSublevelOn s (f i) b = ∅ ↔
      ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, b < f i x := by
  symm
  constructor
  · rintro ⟨u, hu⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro x
    by_cases hx : x ∈ s
    · simp [mem_leSublevelOn_iff, hx]
      obtain ⟨i, hi, hi'⟩ := hu x hx
      use i.val, i.prop
    · simpa [mem_leSublevelOn_iff, hx] using ne_I
  intro H
  have := IsCompact.elim_finite_subfamily_closedOn ks (fun i ↦ LeSublevel (f i) b) (I := I) ?_ ?_
  · obtain ⟨u, hu⟩ := this
    use u
    intro x hx
    rw [Set.eq_empty_iff_forall_notMem] at hu
    specialize hu x
    simp only [iInter_coe_set, mem_inter_iff, hx, mem_iInter, true_and, not_forall,
      Classical.not_imp, exists_and_right] at hu
    obtain ⟨i, hi, hi', hi''⟩ := hu
    use ⟨i, hi⟩, hi'
    simpa [mem_leSublevel_iff] using hi''
  · intro i hi
    specialize hfi i hi
    rw [← isClosed_val_preimage_leSublevelOn_iff] at hfi
    convert hfi b using 1
    ext ⟨x, hx⟩
    simp [hx, mem_leSublevel_iff, mem_leSublevelOn_iff]
  · rw [← Set.inter_biInter ne_I _ s]
    exact H

end LinearOrder

end LeSublevel

/-- The overlevel sets of a function -/
def Function.overlevel [Preorder β] (b : β) : Set α :=
  f ⁻¹' (Set.Ici b)
