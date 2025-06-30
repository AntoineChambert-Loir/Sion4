import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Analysis.Convex.Topology
import Sion.Semicontinuous
import Sion.Concavexity

/-! # Sublevel sets -/

open Set Function

namespace Set

variable {α β : Type*}

variable (A : Set α) (f : α → β) (b : β)

section LeSublevel

section LE

variable [LE β]

/-- The sublevel sets of a function -/
def LeSublevel : Set α := { x | f x ≤ b}

/-- The sublevel sets of a function -/
def LeSublevelOn  : Set α := { x ∈ A | f x ≤ b }

variable {A f b}

theorem mem_leSublevel_iff {a : α} :
  a ∈ Set.LeSublevel f b ↔ f a ≤ b := by
  simp [LeSublevel]

theorem mem_leSublevelOn_iff {a : α} :
  a ∈ A.LeSublevelOn f b ↔ a ∈ A ∧ f a ≤ b := by
  simp [LeSublevelOn]

end LE

section Preorder

variable [Preorder β]

theorem monotone_sublevel :
    Monotone (fun (b : β) ↦ LeSublevel f b) :=
  fun _ _ hbc _ hb ↦ le_trans hb hbc

theorem monotone_leSublevelOn :
    Monotone (fun (b : β) ↦ A.LeSublevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, le_trans hb hbc⟩

end Preorder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder β]

theorem closed_LeSublevel_iff :
    (∀ b, IsClosed (LeSublevel f b)) ↔ LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_preimage.symm

theorem closed_val_preimage_LeSublevelOn_iff :
    (∀ b, IsClosed (Subtype.val ⁻¹' (LeSublevelOn A f b) : Set A)) ↔ LowerSemicontinuousOn f A := by
  rw [lowerSemicontinuousOn_iff_restrict,
    ← closed_LeSublevel_iff]
  suffices ∀ b, LeSublevel (A.restrict f) b
    = Subtype.val ⁻¹' (A.LeSublevelOn f b) by
      simp_rw [this]
  intro b
  ext ⟨x, hx⟩
  simp [mem_leSublevel_iff, mem_leSublevelOn_iff, hx]

end LinearOrder

end LeSublevel

/-- The overlevel sets of a function -/
def Function.overlevel [Preorder β] (b : β) : Set α :=
  f ⁻¹' (Set.Ici b)
