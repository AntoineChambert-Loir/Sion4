import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Analysis.Convex.Topology
import Sion.Semicontinuous
import Sion.Concavexity

-- import Mathlib

/-! # Sublevel sets -/

open Set Function

variable {α β : Type*} [TopologicalSpace α] (A : Set α) (f :α → β)

variable [Preorder β]
/-- The sublevel sets of a function -/
def Set.sublevel (b : β) : Set α := f ⁻¹' (Set.Iic b)

/-- The sublevel sets of a function -/
def Set.sublevelOn (b : β) : Set α := { x ∈ A | f x ≤ b }

variable {f}
theorem Set.mem_sublevel_iff {a : α} :
  a ∈ Set.sublevel f b ↔ f a ≤ b := by
  simp only [sublevel, mem_preimage, mem_Iic]

theorem Set.mem_sublevelOn_iff {a : α} :
  a ∈ A.sublevelOn f b ↔ a ∈ A ∧ f a ≤ b := by
  simp only [sublevelOn, mem_setOf_eq]

theorem Set.monotone_sublevel :
    Monotone (fun (b : β) ↦ Set.sublevel f b) :=
  fun _ _ hbc _ hb ↦ le_trans hb hbc

theorem Set.monotone_sublevelOn :
    Monotone (fun (b : β) ↦ A.sublevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, le_trans hb hbc⟩

theorem Set.closed_sublevel_iff :
    (∀ b, IsClosed (Set.sublevel f b)) ↔ LowerSemicontinuous f := by
  sorry

/-- The overlevel sets of a function -/
def Function.overlevel [Preorder β] (b : β) : Set α :=
  f ⁻¹' (Set.Ici b)
