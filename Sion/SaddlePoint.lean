import Mathlib
import Sion.Semicontinuous
import Sion.Concavexity
import Sion.ForMathlib.Misc
import Mathlib.Analysis.Convex.Topology

open Set

section SaddlePoint

variable {E F : Type*} {β : Type*}
variable (X : Set E) (Y : Set F) (f : E → F → β)

/-- The trivial minimax inequality -/
theorem iSup₂_iInf₂_le_iInf₂_iSup₂ [CompleteLinearOrder β]:
  (⨆ y ∈ Y, ⨅ x ∈ X, f x y) ≤ ⨅ x ∈ X, ⨆ y ∈ Y, f x y := by
  rw [iSup₂_le_iff]; intro y hy
  rw [le_iInf₂_iff]; intro x hx
  exact iInf₂_le_of_le x hx (le_iSup₂_of_le y hy (le_refl _))

-- [Hiriart-Urruty, (4.1.4)]
/-- The pair `(a,b)` is a saddle point of `f` on `X × Y`
if `f a y ≤ f x b` for all `x ∈ X` and all `y `in Y`.

Note: we do not require that a ∈ X and b ∈ Y. -/
def IsSaddlePointOn  [Preorder β] (a : E) (b : F) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, f a y ≤ f x b

variable {X Y f}
-- [Hiriart-Urruty, (4.1.1)]
lemma isSaddlePointOn_iff [CompleteLinearOrder β]
    {a : E} (ha : a ∈ X) {b : F} (hb : b ∈ Y) :
  IsSaddlePointOn X Y f a b ↔
  ⨆ y ∈ Y, f a y = f a b ∧  ⨅ x ∈ X, f x b = f a b := by
  constructor
  · intro h
    constructor
    · apply le_antisymm
      · simp only [iSup_le_iff]
        exact h a ha
      · apply le_iSup₂ b hb
    · apply le_antisymm
      · apply iInf₂_le a ha
      · simp only [le_iInf_iff]
        intro x hx
        exact h x hx b hb
  · rintro ⟨h, h'⟩ x hx y hy
    trans f a b
    · -- f a y ≤ f a b
      rw [← h]
      apply le_iSup₂ y hy
    · -- f a b ≤ f x b
      rw [← h']
      apply iInf₂_le x hx

-- [Hiriart-Urruty, Prop. 4.2.2]
lemma isSaddlePointOn_iff' [CompleteLinearOrder β]
    {a : E} (ha : a ∈ X) {b : F} (hb : b ∈ Y) :
  IsSaddlePointOn X Y f a b ↔
    ((⨆ y ∈ Y, f a y) ≤ (⨅ x ∈ X, f x b)) := by
  rw [isSaddlePointOn_iff ha hb]
  constructor
  · rintro ⟨h, h'⟩
    exact le_trans (le_of_eq h) (le_of_eq h'.symm)
  · intro h
    constructor
    · apply le_antisymm
      · apply le_trans h
        apply iInf₂_le a ha
      · apply le_iSup₂ b hb
    · apply le_antisymm
      · apply iInf₂_le a ha
      · apply le_trans _ h
        apply le_iSup₂ b hb

-- [Hiriart-Urruty, Prop. 4.2.2]
-- The converse doesn't seem to hold
/-- Minimax formulation of saddle points -/
lemma isSaddlePointOn_value [CompleteLinearOrder β]
    {a : E} (ha : a ∈ X) {b : F} (hb : b ∈ Y)
    (h : IsSaddlePointOn X Y f a b) :
    ((⨅ x ∈ X, ⨆ y ∈ Y, f x y = f a b) ∧ (⨆ y ∈ Y, ⨅ x ∈ X, f x y = f a b)) := by
  rw [isSaddlePointOn_iff ha hb] at h
  constructor
  · apply le_antisymm
    · rw [← h.1]
      exact le_trans (iInf₂_le a ha) (le_rfl)
    · rw [← h.2]
      apply iInf₂_mono
      intro x _
      apply le_iSup₂ b hb
  · apply le_antisymm
    · rw [← h.1]
      apply iSup₂_mono
      intro y _
      apply iInf₂_le a ha
    · rw [← h.2]
      apply le_trans (le_rfl) (le_iSup₂ b hb)

end SaddlePoint

