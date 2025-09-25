import Sion.Sion

section vonNeumann

variable {E F : Type*}
variable {X : Set E} {Y : Set F}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [Module.Finite ℝ E]
    (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [Module.Finite ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  (cY : Convex ℝ Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)

variable {f : E →L[ℝ] F →L[ℝ] ℝ}
/-     (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E ↦ f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
  (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y) -/

example (x : E) :
    ContinuousOn (fun y : F ↦ f x y) Y := by
  apply Continuous.continuousOn
  exact ContinuousLinearMap.continuous (f x)

noncomputable example : F →L[ℝ] E →L[ℝ] ℝ where
  toFun y := {
    toFun x := f x y
    map_add' x x' := by simp
    map_smul' r x := by simp
    cont := by
      refine Continuous.eval_const ?_ y
      exact ContinuousLinearMap.continuous f }
  map_add' y y' := by aesop
  map_smul' r y := by aesop
  cont := by
    apply?

example : TopologicalSpace (E →L[ℝ] ℝ) := by
  exact ContinuousLinearMap.topologicalSpace
example (y : F) :
    ContinuousOn (fun x : E ↦ f x y) X := by
  apply Continuous.continuousOn



end vonNeumann


