import Mathlib.Topology.Instances.EReal
import Mathlib.Data.Real.EReal

import Sion.Semicontinuous
import Sion.Concavexity
import Sion.ForMathlib.Misc
import Mathlib.Analysis.Convex.Topology

/-! # Formalization of the von Neumann Sion theorem

## Statements

`sion_exists` :
Let X and Y be convex subsets of topological vector spaces E and F,
X being moreover compact,
and let f : X × Y → ℝ be a function such that
- for all x, f(x, ⬝) is upper semicontinuous and quasiconcave
- for all y, f(⬝, y) is lower semicontinuous and quasiconvex
Then inf_x sup_y f(x,y) = sup_y inf_x f(x,y).

The classical case of the theorem assumes that f is continuous,
f(x, ⬝) is concave, f(⬝, y) is convex.

As a particular case, one get the von Neumann theorem where
f is bilinear and E, F are finite dimensional.

We follow the proof of Komiya (1988).

-- TODO :
  * For the moment, the proof is only done when the target is EReal
  * Replace ℝ with a general type
  * Explicit the classical particular cases (in particular, von Neumann)

## References

- Neumann, John von (1928). « Zur Theorie der Gesellschaftsspiele ».
Mathematische Annalen 100 (1): 295‑320.  https://doi.org/10.1007/BF01448847.

- Sion, Maurice (1958). « On general minimax theorems ».
Pacific Journal of Mathematics 8 (1): 171‑76.

- Komiya, Hidetoshi (1988). « Elementary Proof for Sion’s Minimax Theorem ».
Kodai Mathematical Journal 11 (1). https://doi.org/10.2996/kmj/1138038812.


## Comments on the proof

For the moment, the proof is made difficult by the absence of results in mathlib
pertaining to semicontinuous functions, and possibly to continuity properties
of convex functions.

One option would be to first do the proof for continuous functions
by `sorry`ing all the results that we need in the semicontinuous case.


-/


open Set

section sublevels

def Set.LeSublevelOn {E β: Type*} [LE β] (s : Set E) (f : E → β) (b : β) :=
  { x ∈ s | f x ≤ b }

def Set.LtSublevelOn {E β: Type*} [LT β] (s : Set E) (f : E → β) (b : β) :=
  { x ∈ s | f x < b }

end sublevels

section SaddlePoint

variable {E F : Type _} {β : Type _}
variable (X : Set E) (Y : Set F) (f : E → F → β)

/-- The trivial minimax inequality -/
theorem iSup₂_iInf₂_le_iInf₂_iSup₂ [CompleteLinearOrder β]:
  (⨆ y ∈ Y, ⨅ x ∈ X, f x y) ≤ ⨅ x ∈ X, ⨆ y ∈ Y, f x y := by
  rw [iSup₂_le_iff]; intro y hy
  rw [le_iInf₂_iff]; intro x hx
  exact iInf₂_le_of_le x hx (le_iSup₂_of_le y hy (le_refl _))

-- [Hiriart-Urruty, (4.1.4)]
/-- The pair (a,b) is a saddle point of f on X × Y
  (does not enforce that a ∈ X and b ∈ Y) -/
def IsSaddlePointOn  [Preorder β] (a : E) (b : F) :=
  ∀ x ∈ X, ∀ y ∈ Y, f a y ≤ f x b

variable {X Y f}
-- [Hiriart-Urruty, (4.1.1)]
lemma isSaddlePointOn_iff [CompleteLinearOrder β]
    {a : E} (ha : a ∈ X) {b : F} (hb : b ∈ Y) :
  IsSaddlePointOn X Y f a b ↔
  ⨆ y ∈ Y, f a y = f a b ∧  ⨅ x ∈ X, f x b = f a b := by
  constructor
  · intro h
    dsimp [IsSaddlePointOn] at h
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
  · rintro ⟨h, h'⟩
    intro x hx y hy
    suffices f a y ≤ f a b by
      apply le_trans this
      -- f a b ≤ f x b
      rw [← h']
      apply iInf₂_le x hx
    · -- f a y ≤ f a b
      rw [← h]
      apply le_iSup₂ y hy

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
-- Does the converse hold?
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

variable {E : Type _} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousSMul ℝ E]

variable {F : Type _} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [TopologicalAddGroup F]
  [ContinuousSMul ℝ F]

variable (X : Set E) (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)

variable (Y : Set F) (ne_Y : Y.Nonempty) (cY : Convex ℝ Y) (kY : IsCompact Y)

section EReal

namespace ERealSion


section

variable (f : E → F → β)
  -- [CompleteLinearOrder β] [DenselyOrdered β]
  [LinearOrder β] [DenselyOrdered β]
  -- [CompleteLinearOrderedAddCommMonoid β] [OrderedAddCommMonoid β] [DenselyOrdered β]

-- has to be removed from the definition of Quasiconcave / Quasiconvex

variable (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

variable (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
  (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

/-- The familywise sublevel sets of f -/
private def C : β → F → Set X :=
  fun b z => (fun x => f x z) ∘ (fun x ↦ ↑x)⁻¹' Iic b

private theorem mem_C_iff (b : β) (y : Y) (x : X) :
    x ∈ C X f b y ↔ f x y ≤ b := by simp [C]

private theorem monotone_C (u v : β) (y : Y) (h : u ≤ v) :
    C X f u y ⊆ C X f v y :=
  fun _ hxu ↦ le_trans hxu h

  -- Uses that X is compact and nonempty !
include ne_X kX hfy in
private theorem nonempty_C (y : Y) {b : β} (h : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ b) :
    (C X f b y).Nonempty := by
  rcases y with ⟨y, hy⟩
  obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_X kX (hfy y hy)
  obtain ⟨x', hx', hx'b⟩ := h y hy
  exact ⟨⟨x, hx⟩, le_trans (hx_le x' hx') hx'b⟩

include hfy in
private theorem isClosed_C (b : β) (y : Y) :
    IsClosed (C X f b y) := by
  specialize hfy y.val y.prop
  rw [lowerSemicontinuousOn_iff_restrict] at hfy
  rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy
  exact hfy b

include hfy' in
private theorem isPreconnected_C (b : β) (y : Y) :
    IsPreconnected (C X f b y) :=
  (hfy' y.val y.prop).isPreconnected_preimage

private theorem disjoint_C (a : E) (b : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y') :
    Disjoint (C X f b y) (C X f b y') := by
  rw [Set.disjoint_iff]
  rintro ⟨x, hx⟩ ⟨hx1, hx2⟩
  simp only [mem_empty_iff_false]
  apply not_le_of_lt hb
  apply le_trans (ha x hx)
  simp only [sup_le_iff]
  exact ⟨hx1, hx2⟩

include hfx' in
private theorem C_subset_union (b : β) (y y' : Y)
    (z : segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∪ C X f b y' := fun x hx ↦ by
    simp only [Set.mem_union, mem_C_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y ⊓ f x y')
    rw [convex_iff_segment_subset] at hfx'
    specialize hfx' ⟨y.prop, inf_le_left⟩ ⟨y'.prop, inf_le_right⟩ z.prop
    exact le_trans hfx'.2 hx

include cY hfy hfy' hfx' in
private theorem C_subset_or
    (a : E) (b : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y')
    (z : segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∨ C X f b z ⊆ C X f b y' := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_C X Y f hfy' b ⟨z, cY.segment_subset y.prop y'.prop z.prop⟩)
    _ _ (isClosed_C X Y f hfy b y) (isClosed_C X Y f hfy b y')
    (C_subset_union X Y f hfx' b y y' z)
  rw [Set.disjoint_iff_inter_eq_empty.mp (disjoint_C X Y f a b y y' ha hb),
    Set.inter_empty]

include cY hfy hfy' hfx' in
private theorem C_subset_or'
    (a : E) (b : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y')
    (z : Y) (hz : z.val ∈ segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∨ C X f b z ⊆ C X f b y' := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_C X Y f hfy' b ⟨z, cY.segment_subset y.prop y'.prop hz⟩)
    _ _ (isClosed_C X Y f hfy b y) (isClosed_C X Y f hfy b y')
    (C_subset_union X Y f hfx' b y y' ⟨z, hz⟩)
  rw [Set.disjoint_iff_inter_eq_empty.mp (disjoint_C X Y f a b y y' ha hb),
    Set.inter_empty]


example (y y' : F) : segment ℝ y y' = segment ℝ y' y :=
  segment_symm ℝ y y'

private def J (b b' : β) (y y' : Y) :=
    {z : segment ℝ y.val y'.val | C X f b z ⊆ C X f b' y}

-- L'ensemble J' est défini de même pour en changeant les rôles de y et y'
-- mais (segment ℝ y y') n'est pas déf. éal à (segment ℝ y' y)
-- On a besoin de dire qu'ils sont disjoints
-- Solutions :
--   1) définir ces ensembles dans F ou dans Y (ne marche pas bien)
--   2) calculer l'intersection dans F (essayons !)

private theorem mem_J_iff (b b' : β) (y y' : Y) (z : segment ℝ y.val y'.val) :
    z ∈ J X Y f b b' y y' ↔ C X f b z ⊆ C X f b' y := by
  simp only [mem_setOf_eq, J]

private theorem y_mem_J (b b' : β) (y y' : Y) (hbb' : b ≤ b') :
    (⟨y.val, left_mem_segment ℝ y.val y'.val⟩ : segment ℝ y.val y'.val) ∈ J X Y f b b' y y' :=
  monotone_C X Y f b b' y hbb'

include ne_X kX hfx hfx' cY hfy hfy' in
private theorem isClosed_J
    (a : E) (b b' : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ b)
    (hb' : b' < f a y ⊔ f a y')
    (hbb' : b < b') :
    IsClosed (J X Y f b b' y y') := by
  rw [isClosed_iff_clusterPt]
    -- Let `y` be a cluster point of `J1`
    -- let us show it's in `J1`, i.e `C t y ⊆ C t' y1`.
    -- Let `x ∈ C t y`
    -- and let's find some `z ∈ J1` such that `x ∈ C t z ⊆ C t' y1`.
  intro z hz x hx
  have hzY :=(convex_iff_segment_subset.mp cY) y.prop y'.prop z.prop
    /- y = lim yn, yn ∈ J1
       comme x ∈ C t y, on a f x y ≤ t < t',
       comme (f x ⬝) est usc, f x yn < t' pour n assez grand
       donc x ∈ C t' yn pour n assez grand

       pour z ∈ J1 tel que x ∈ C t' z
       On prouve C t' z ⊆ C t' y1
       Par hypothèse, C t z ⊆ C t' y1
       Sinon, C t' z ⊆ C t' y2 (hC_subset_or)
       Donc x ∈ C t' y1 ∩ C t' y2 = ∅, contradiction

       En particulier, x ∈ C yt' y1

    -/
  suffices ∃ z' ∈ J X Y f b b' y y', x ∈ C X f b' (z' : F) by
    obtain ⟨z', hz', hxz'⟩ := this
    suffices C X f b' z' ⊆ C X f b' y by
      exact this hxz'
    apply Or.resolve_right (C_subset_or X Y cY f hfx' hfy hfy' a b' y y' ha hb' z')
    intro hz'2
    have hz'Y :=(convex_iff_segment_subset.mp cY) y.prop y'.prop z'.prop
    apply (nonempty_C X ne_X kX Y f hfy ⟨z', hz'Y⟩ hb).not_subset_empty
    simp only [← disjoint_iff_inter_eq_empty.mp (disjoint_C X Y f a b' y y' ha hb')]
    apply Set.subset_inter hz'
    apply subset_trans (monotone_C X Y f b b' ⟨z', hz'Y⟩ hbb'.le) hz'2

    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
  simp only [UpperSemicontinuousOn, UpperSemicontinuousWithinAt] at hfx
  have := lt_of_le_of_lt hx hbb'
  dsimp only [Function.comp_apply] at this
  specialize hfx x.val x.prop z (cY.segment_subset y.prop y'.prop z.prop) b'
    (lt_of_le_of_lt hx hbb')
    -- We rewrite h into an ∃ᶠ form
  rw [Filter.clusterPt_principal_subtype_iff_frequently (cY.segment_subset y.prop y'.prop)] at hz
  suffices ∀ᶠ z' : F in nhdsWithin z Y,
    (∃ hz' : z' ∈ segment ℝ y.val y'.val, (⟨z', hz'⟩ : segment ℝ y.val y'.val) ∈ J X Y f b b' y y') →
      ∃ hz' : z' ∈ segment ℝ y.val y'.val, x ∈ C X f b' z'
        ∧ (⟨z', hz'⟩ : segment ℝ y.val y'.val) ∈ J X Y f b b' y y' by
    obtain ⟨z', hz', hxz'1, hxz'2⟩ := Filter.Frequently.exists (Filter.Frequently.mp hz this)
    exact ⟨⟨z', hz'⟩, ⟨hxz'2, hxz'1⟩⟩
  · -- this
    apply Filter.Eventually.mp hfx
    apply Filter.eventually_of_forall
    intro z hzt'
    rintro ⟨hz, hz'⟩
    exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩

include ne_X kX hfx hfx' cY hfy hfy' in
theorem exists_lt_iInf_of_lt_iInf_of_sup {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y) {t : β}
    (ht : ∀ x ∈ X, t < f x y1 ⊔ f x y2) :
    ∃ y0 ∈ Y, ∀ x ∈ X, t < f x y0 := by
  by_contra hinfi_le
  push_neg at hinfi_le
  obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact
    ne_X kX (f := fun x ↦ f x y1 ⊔ f x y2) (by
      apply LowerSemicontinuousOn.sup
      exact hfy y1 hy1
      exact hfy y2 hy2)
  obtain ⟨t', htt', ht'⟩ := exists_between (ht a ha)

  let J1 := J X Y f t t' ⟨y1, hy1⟩ ⟨y2, hy2⟩
  have mem_J1_iff : ∀ (z : F) (hz : z ∈ segment ℝ y1 y2),
      ⟨z, hz⟩ ∈ J1 ↔ ERealSion.C X f t z ⊆ ERealSion.C X f t' y1 :=
    fun z _ ↦ by simp [J1, J]
  let φ : segment ℝ y1 y2 ≃ₜ segment ℝ y2 y1 := by
    apply Homeomorph.subtype (Homeomorph.refl F)
    intro x
    rw [segment_symm ℝ y2 y1]
    simp only [Homeomorph.refl_apply, id_eq]
  let J2 := φ ⁻¹' (J X Y f t t' ⟨y2, hy2⟩ ⟨y1, hy1⟩)
  have mem_J2_iff : ∀ (z : F) (hz : z ∈ segment ℝ y1 y2),
      ⟨z, hz⟩ ∈ J2 ↔ ERealSion.C X f t z ⊆ ERealSion.C X f t' y2 :=
    fun z hz ↦ by simp [J2, J, φ, segment_symm ℝ y2 y1, hz]
  have hJ1J2 : J1 ∩ J2 = ∅ := by
    rw [Set.eq_empty_iff_forall_not_mem]
    simp only [mem_inter_iff, not_and]
    rintro ⟨z, hz⟩ hz1 hz2
    simp only [mem_J1_iff] at hz1
    simp only [mem_J2_iff] at hz2
    have hz_mem_Y : z ∈ Y := cY.segment_subset hy1 hy2 hz
    apply Set.Nonempty.not_subset_empty (nonempty_C X ne_X kX Y f hfy ⟨z, hz_mem_Y⟩ hinfi_le)
    rw [Set.subset_empty_iff, ← bot_eq_empty, ← disjoint_self]
    exact Set.disjoint_of_subset hz1 hz2 (disjoint_C X Y f a t' ⟨y1, hy1⟩ ⟨y2, hy2⟩ ha' ht')
  have hJ1_union_J2 : J1 ∪ J2 = segment ℝ y1 y2 := by
    ext z
    constructor
    · rintro ⟨⟨z, hz⟩, _, rfl⟩
      exact hz
    · intro hz
      have hz_mem_Y : z ∈ Y := cY.segment_subset hy1 hy2 hz
      use ⟨z, hz⟩
      refine ⟨?_, rfl⟩
      rcases C_subset_or X Y cY f hfx' hfy hfy' a t' ⟨y1, hy1⟩ ⟨y2, hy2⟩ ha' ht' ⟨z, hz⟩ with (h1 | h2)
      · left
        simp only [mem_J1_iff]
        exact subset_trans (monotone_C X Y f t t' ⟨z, hz_mem_Y⟩ htt'.le) h1
      · right
        simp only [mem_J2_iff]
        exact subset_trans (monotone_C X Y f t t' ⟨z, hz_mem_Y⟩ htt'.le) h2
  suffices IsPreconnected (Set.univ : Set (segment ℝ y1 y2)) by
    rw [isPreconnected_iff_subset_of_disjoint_closed] at this
    rw [Set.eq_empty_iff_forall_not_mem] at hJ1J2
    rcases this J1 J2 ?_ ?_ ?_ ?_ with (h1 | h2)
    · apply hJ1J2 ⟨y2, right_mem_segment ℝ y1 y2⟩
      rw [Set.mem_inter_iff]
      refine ⟨h1 (Set.mem_univ _), ?_⟩
      rw [mem_J2_iff]
      apply monotone_C X Y f t t' ⟨y2, hy2⟩ htt'.le
    · apply hJ1J2 ⟨y1, left_mem_segment ℝ y1 y2⟩
      rw [Set.mem_inter_iff]
      refine ⟨?_, h2 (Set.mem_univ _)⟩
      rw [mem_J1_iff]
      apply monotone_C X Y f t t' ⟨y1, hy1⟩ htt'.le
  · rw [← Set.eq_empty_iff_forall_not_mem] at hJ1J2
    simp only [hJ1J2, inter_empty]
  · -- is preconnected
    rw [← inducing_subtype_val.isPreconnected_image]
    simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]
    exact Convex.isPreconnected (convex_segment y1 y2)
  · -- is closed J1
    exact isClosed_J X ne_X kX Y cY f hfx hfx' hfy hfy' a t t' ⟨y1, hy1⟩ ⟨y2, hy2⟩ ha' hinfi_le ht' htt'
  · -- is closed J2
    rw [Homeomorph.isClosed_preimage]
    simp only [sup_comm (f _ y1)] at ha' ht'
    refine isClosed_J X ne_X kX Y cY f hfx hfx' hfy hfy' a t t' ⟨y2, hy2⟩ ⟨y1, hy1⟩ ha' hinfi_le ht' htt'
  · -- univ ⊆ J1 ∪ J2
    rintro ⟨z, hz⟩ _
    rw [← hJ1_union_J2] at hz
    rcases hz with ⟨⟨z, hz'⟩, hz'', rfl⟩
    exact hz''



/-
theorem exists_lt_iInf_of_lt_iInf_of_sup_orig {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y) {t : β}
    (ht : ∀ x ∈ X, t < f x y1 ⊔ f x y2) :
    ∃ y0 ∈ Y, ∀ x ∈ X, t < f x y0 := by
  by_contra hinfi_le
  push_neg at hinfi_le
  obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact
    ne_X kX (f := fun x ↦ f x y1 ⊔ f x y2) (by
      apply LowerSemicontinuousOn.sup
      exact hfy y1 hy1
      exact hfy y2 hy2)
  obtain ⟨t', htt', ht'⟩ := exists_between (ht a ha)

  let C : β → F → Set X := fun b z => (fun x => f x z) ∘ (fun x ↦ ↑x)⁻¹' Iic b

  have mem_C_iff : ∀ b z (x : X), x ∈ C b z ↔ f x z ≤ b := fun z x ↦ by
    simp [C]
  have hC : ∀ u v z (h : u ≤ v), C u z ⊆ C v z := fun u v z h x hxu ↦ le_trans hxu h

  -- Uses that X is compact and nonempty !
  have hC_ne : ∀ z ∈ Y, (C t z).Nonempty := by
    intro z hz
    obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_X kX (hfy z hz)
    use ⟨x, hx⟩
    rw [mem_C_iff, Subtype.coe_mk]
    obtain ⟨x', hx', hx't⟩ := hinfi_le z hz
    exact le_trans (hx_le x' hx') hx't

  have hC_closed : ∀ b, ∀ z ∈ Y, IsClosed (C b z) :=  by
    intro b z hz
    specialize hfy z hz
    rw [lowerSemicontinuousOn_iff_restrict] at hfy
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy
    exact hfy b

  have hC_preconnected : ∀ b, ∀ z ∈ Y, IsPreconnected (C b z) :=
    fun b z hz ↦ (hfy' z hz).isPreconnected_preimage


  have hCt'_disj : Disjoint (C t' y1) (C t' y2) := by
      rw [Set.disjoint_iff]
      rintro ⟨x, hx⟩ ⟨hx1, hx2⟩
      simp only [mem_empty_iff_false]
      apply not_le_of_lt ht'
      apply le_trans (ha' x hx)
      simp only [sup_le_iff]
      exact ⟨hx1, hx2⟩

  have hCt'_subset : ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∪ C t' y2 := by
    intro z hz x hx
    simp only [Set.mem_union, mem_C_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y1 ⊓ f x y2)
    rw [convex_iff_segment_subset] at hfx'
    specialize hfx' ⟨hy1, inf_le_left⟩ ⟨hy2, inf_le_right⟩ hz
    exact le_trans hfx'.2 hx

  have hCt'_subset_or :
    ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∨ C t' z ⊆ C t' y2 := by
    intro z hz
    apply isPreconnected_iff_subset_of_disjoint_closed.mp
      (hC_preconnected _ _ (cY.segment_subset hy1 hy2 hz))
      _ _  (hC_closed _ _ hy1) (hC_closed _ _ hy2) (hCt'_subset _ hz)
    rw [Set.disjoint_iff_inter_eq_empty.mp hCt'_disj, Set.inter_empty]

  let J1 := {z : segment ℝ y1 y2 | C t z ⊆ C t' y1}
  -- do we really need this ? (I can't do without it)
  have mem_J1_iff : ∀ z : segment ℝ y1 y2, z ∈ J1 ↔ C t z ⊆ C t' y1 :=
    fun z ↦ by simp only [mem_setOf_eq, J1]
  have hJ1_closed : IsClosed J1 := by
    rw [isClosed_iff_clusterPt]
    -- Let `y` be a cluster point of `J1`
    -- let us show it's in `J1`, i.e `C t y ⊆ C t' y1`.
    -- Let `x ∈ C t y`
    -- and let's find some `z ∈ J1` such that `x ∈ C t z ⊆ C t' y1`.
    intro y h x hx
    /- y = lim yn, yn ∈ J1
       comme x ∈ C t y, on a f x y ≤ t < t',
       comme (f x ⬝) est usc, f x yn < t' pour n assez grand
       donc x ∈ C t' yn pour n assez grand

       pour z ∈ J1 tel que x ∈ C t' z
       On prouve C t' z ⊆ C t' y1
       Par hypothèse, C t z ⊆ C t' y1
       Sinon, C t' z ⊆ C t' y2 (hC_subset_or)
       Donc x ∈ C t' y1 ∩ C t' y2 = ∅, contradiction

       En particulier, x ∈ C yt' y1

    -/
    suffices ∃ z ∈ J1, x ∈ C t' (z : F) by
      obtain ⟨z, hz, hxz⟩ := this
      suffices C t' z ⊆ C t' y1 by
        exact this hxz
      apply Or.resolve_right (hCt'_subset_or z z.2)
      intro hz2
      apply Set.Nonempty.not_subset_empty (hC_ne z ((convex_iff_segment_subset.mp cY) hy1 hy2 z.2))
      rw [← disjoint_iff_inter_eq_empty.mp hCt'_disj]
      apply Set.subset_inter hz
      apply subset_trans (hC _ _ _ htt'.le) hz2

    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [UpperSemicontinuousOn, UpperSemicontinuousWithinAt] at hfx
    specialize hfx x.val x.prop y
      (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt')
    -- We rewrite h into an ∃ᶠ form
    rw [Filter.clusterPt_principal_subtype_iff_frequently (cY.segment_subset hy1 hy2)] at h
    suffices ∀ᶠ z : F in nhdsWithin y Y,
        (∃ hz : z ∈ segment ℝ y1 y2, (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1) →
          ∃ hz : z ∈ segment ℝ y1 y2, x ∈ C t' z ∧ (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1 by
      obtain ⟨z, hz, hxz, hxz'⟩ := Filter.Frequently.exists (Filter.Frequently.mp h this)
      exact ⟨⟨z, hz⟩, ⟨hxz', hxz⟩⟩
    · -- this
      apply Filter.Eventually.mp hfx
      apply Filter.eventually_of_forall
      intro z hzt'
      rintro ⟨hz, hz'⟩
      exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩

  have hy1_mem_J1 : (⟨y1, left_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J1 := by
    rw [mem_J1_iff]
    apply hC
    exact le_of_lt htt'
  let J2 := {z : segment ℝ y1 y2 | C t z ⊆ C t' y2}
  have mem_J2_iff : ∀ z : segment ℝ y1 y2, z ∈ J2 ↔ C t z ⊆ C t' y2 :=
    fun z ↦ by simp only [mem_setOf_eq, J2]
  have hy2_mem_J2 : (⟨y2, right_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J2 :=
    hC t t' y2 (le_of_lt htt')
  have hJ2_closed : IsClosed J2 := by
    rw [isClosed_iff_clusterPt]
    intro y h x hx
    suffices ∃ z ∈ J2, x ∈ C t' (z : F) by
      obtain ⟨z, hz, hxz⟩ := this
      suffices C t' z ⊆ C t' y2 by
        exact this hxz
      apply Or.resolve_left (hCt'_subset_or z z.2)
      intro hz2
      apply Set.Nonempty.not_subset_empty (hC_ne z ((convex_iff_segment_subset.mp cY) hy1 hy2 z.2))
      rw [← disjoint_iff_inter_eq_empty.mp hCt'_disj]
      refine' Set.subset_inter (subset_trans (hC t t' z (le_of_lt htt')) hz2) hz
    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [UpperSemicontinuousOn, UpperSemicontinuousWithinAt] at hfx
    specialize hfx x.val x.prop y (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt')
    -- We rewrite h into an ∃ᶠ form
    rw [Filter.clusterPt_principal_subtype_iff_frequently (cY.segment_subset hy1 hy2)] at h
    suffices ∀ᶠ z : F in nhdsWithin y Y,
        (∃ hz : z ∈ segment ℝ y1 y2, (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J2) →
          ∃ hz : z ∈ segment ℝ y1 y2, x ∈ C t' z ∧ (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J2 by
      obtain ⟨z, hz, hxz, hxz'⟩ := Filter.Frequently.exists (Filter.Frequently.mp h this)
      exact ⟨⟨z, hz⟩, ⟨hxz', hxz⟩⟩
    · -- this
      apply Filter.Eventually.mp hfx
      apply Filter.eventually_of_forall
      intro z hzt'
      rintro ⟨hz, hz'⟩
      exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩
  -- On fait presque deux fois la même chose, il faut unifier les deux trucs.
  have hJ1J2 : J1 ∩ J2 = ∅ := by
    rw [Set.eq_empty_iff_forall_not_mem]
    rintro z ⟨hz1, hz2⟩
    rw [mem_J1_iff] at hz1
    rw [mem_J2_iff] at hz2
    have := hC_ne z (cY.segment_subset hy1 hy2 z.prop)
    apply Set.Nonempty.not_subset_empty (hC_ne z (cY.segment_subset hy1 hy2 z.prop))
    rw [Set.subset_empty_iff, ← bot_eq_empty, ← disjoint_self]
    exact Set.disjoint_of_subset hz1 hz2 hCt'_disj
  have hJ1_union_J2 : J1 ∪ J2 = Set.univ := by
    rw [← Set.top_eq_univ, eq_top_iff]
    intro z _
    rw [Set.mem_union, mem_J1_iff, mem_J2_iff]
    cases' hCt'_subset_or z z.prop with h1 h2
    left; exact Set.Subset.trans (hC t t' z (le_of_lt htt')) h1
    right; exact Set.Subset.trans (hC t t' z (le_of_lt htt')) h2
  suffices IsPreconnected (Set.univ : Set (segment ℝ y1 y2)) by
    rw [isPreconnected_iff_subset_of_disjoint_closed] at this
    specialize this _ _ hJ1_closed hJ2_closed (Eq.subset hJ1_union_J2.symm) _
    · rw [hJ1J2, Set.inter_empty]
    rw [Set.eq_empty_iff_forall_not_mem] at hJ1J2
    cases' this with h1 h2
    · apply hJ1J2
      rw [Set.mem_inter_iff]
      exact ⟨h1 (Set.mem_univ _), hy2_mem_J2⟩
    · apply hJ1J2
      rw [Set.mem_inter_iff]
      exact ⟨hy1_mem_J1, h2 (Set.mem_univ _)⟩
  rw [← inducing_subtype_val.isPreconnected_image]
  simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]
  exact Convex.isPreconnected (convex_segment y1 y2)
-/

include ne_X cX cY kX hfx hfx' hfy hfy' in
theorem exists_lt_iInf_of_lt_iInf_of_finite {s : Set F} (hs : s.Finite) {t : β}
    (ht : ∀ x ∈ X, ∃ y ∈ s, t < f x y) :
    s ⊆ Y → ∃ y0 ∈ Y, ∀ x ∈ X, t < f x y0 := by
  revert X
  --
  refine' Set.Finite.induction_on hs _ _
  · -- empty case
    intro X ne_X _ _ _ _ _ _
    obtain ⟨x, hx⟩ := id ne_X
    simp only [biInf_const ne_X, mem_empty_iff_false, ciSup_false, ciSup_const,
      not_lt_bot, IsEmpty.forall_iff]
    simp only [false_and, exists_const, imp_false, empty_subset, forall_true_left]
    intro h
    exfalso
    exact h x hx
  · -- insert case
    intro b s _ _ hrec X ne_X _ kX hfx hfx' hfy hfy' ht hs'Y
    have hb : (b ∈ Y) := hs'Y (mem_insert b s)
    -- obtain ⟨t' : ereal, htt', ht'_lt_infi_supr⟩ :=  exists_between ht,
    let X' := {x ∈ X | f x b ≤ t}
    cases' Set.eq_empty_or_nonempty X' with X'_e X'_ne
    · -- X' = ∅,
      use b, hb
      intro x hx
      rw [← not_le]
      intro h
      rw [Set.eq_empty_iff_forall_not_mem] at X'_e
      -- obtain ⟨x', _, _⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_X kX (hfy b hb)
      exact X'_e x ⟨hx, h⟩
    -- the nonempty case
    have hX'X : X' ⊆ X := by simp only [sep_subset, X']
    have kX' : IsCompact X' := by
      suffices X' = Subtype.val '' (Subtype.val ⁻¹' X' : Set X) by
        rw [this, ← Inducing.isCompact_iff inducing_subtype_val]
        haveI kX' : CompactSpace X := isCompact_iff_compactSpace.mp kX
        apply IsClosed.isCompact
        rw [inducing_subtype_val.isClosed_iff]
        specialize hfy b hb
        rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfy
        obtain ⟨v, hv, hv'⟩ := hfy t
        use v, hv
        rw [Subtype.preimage_coe_eq_preimage_coe_iff, ← hv']
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_setOf_eq, and_self_left, X']
      simp only [Set.image_preimage_eq_inter_range, ge_iff_le,
        Subtype.range_coe_subtype, setOf_mem_eq,
        Set.inter_eq_self_of_subset_left hX'X]
    have cX' : Convex ℝ X' := hfy' b hb t
    · specialize hrec X' X'_ne cX' kX'
            (fun x hx' ↦ hfx x (hX'X hx'))
            (fun x hx' ↦ hfx' x (hX'X hx'))
            (fun y hy ↦ LowerSemicontinuousOn.mono (hfy y hy) hX'X)
            (fun y hy ↦ cX'.quasiconvexOn_restrict (hfy' y hy) hX'X)
      have ht_lt : ∀ x ∈ X', ∃ y ∈ s, t < f x y := by
--      have ht_lt : t < ⨅ x ∈ X', ⨆ y ∈ s, f x y := by
          /- sinon, si  infi x ∈ X', supr y ∈ s f x y ≤ t
            pour tout t' > t, il existe x ∈ X', supr y ∈ s f x y ≤ t',
            comme x ∈ X' et t ≤ t', on  a supr y ∈ insert b s f x y  ≤ t',
            donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t',
            donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t -/
        intro x hx
        obtain ⟨y, hy, h⟩ := ht x hx.1
        rcases hy with (hy | hy)
        · exfalso
          rw [hy, ← not_le] at h
          exact h hx.2
        · exact ⟨y, hy, h⟩
      obtain ⟨y1, hy1, hty1⟩ := hrec  ht_lt (subset_trans (subset_insert b s) hs'Y)
      apply exists_lt_iInf_of_lt_iInf_of_sup X ne_X kX Y cY f hfx hfx' hfy hfy' hb hy1
      intro x hx
      by_cases hx' : x ∈ X'
      · exact lt_of_lt_of_le (hty1 x hx') (le_sup_right)
      · apply lt_of_lt_of_le _ (le_sup_left)
        rw [← not_le]
        exact fun h ↦ hx' ⟨hx, h⟩

end

section general

variable (f : E → F → β)
  [LinearOrder β] [DenselyOrdered β]

variable (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

variable (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
  (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

include ne_X cX cY kX hfx hfx' hfy hfy' in
theorem minimax
    (sup_y : E → β) (hsup_y : ∀ x ∈ X, IsLUB {f x y | y ∈ Y} (sup_y x)) 
    (inf_sup : β) (hinf_sup : IsGLB {sup_y x | x ∈ X} inf_sup) 
    (inf_x : F → β) (hinf_x : ∀ y ∈ Y, IsGLB {f x y | x ∈ X} (inf_x y)) 
    (sup_inf : β) (hsup_inf : IsLUB {inf_x y | y ∈ Y} sup_inf) :
    inf_sup = sup_inf := by
  apply symm
  apply le_antisymm
  -- the obvious inequality
  · rw [le_isGLB_iff hinf_sup, mem_lowerBounds]
    rintro _ ⟨x, hx, rfl⟩
    rw [isLUB_le_iff hsup_inf, mem_upperBounds]
    rintro _ ⟨y, hy, rfl⟩
    trans f x y
    · exact (hinf_x y hy).1 ⟨x, hx, rfl⟩
    · exact (hsup_y x hx).1 ⟨y, hy, rfl⟩
  -- the delicate inequality
  · rw [← forall_lt_iff_le]
    intro t ht
    let X' (y : F) := ({x ∈ X | f x y ≤ t} : Set E)

    suffices hs : ∃ s : Set F, s ⊆ Y ∧ s.Finite ∧ (⋂ y ∈ s, X' y) = ∅ by
      obtain ⟨s, hsY, hs, hes⟩ := hs
      suffices hst : ∀ x ∈ X, ∃ y ∈ s, t < f x y by
        obtain ⟨y0, hy0, ht0⟩ := exists_lt_iInf_of_lt_iInf_of_finite
          X ne_X cX kX Y cY f hfx hfx' hfy hfy' hs hst hsY
        simp only [lt_isLUB_iff hsup_inf, mem_setOf_eq, exists_exists_and_eq_and]
        use y0, hy0
        -- TODO : make automatic for semicontinuous
        obtain ⟨a, ha, h⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact
          ne_X kX (hfy y0 hy0)
        apply lt_of_lt_of_le (ht0 a ha) 
        rw [le_isGLB_iff (hinf_x y0 hy0), mem_lowerBounds]
        simpa only [mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro x hx
      by_contra hx'
      push_neg at hx'
      rw [Set.eq_empty_iff_forall_not_mem] at hes
      apply hes x
      simp only [mem_iInter, mem_setOf_eq, X', forall₂_and]
      exact ⟨fun _ _ ↦ hx, hx'⟩
    suffices hfyt : ∀ y : Y, ∃ vy : Set E, IsClosed vy ∧ X' y = X ∩ vy by
      let v : Y → Set E := fun y ↦ Exists.choose (hfyt y)
      have hv : ∀ y, IsClosed (v y) ∧ X' y = X ∩ v y := fun y ↦ (hfyt y).choose_spec
      suffices hsZ : _ by
        obtain ⟨s, hs⟩ := kX.elim_finite_subfamily_closed v (fun y => (hv y).1) hsZ
        have hs_ne : s.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hs_e
          simp only [hs_e, Finset.not_mem_empty, iInter_of_empty, iInter_univ, inter_univ] at hs
          rw [Set.nonempty_iff_ne_empty] at ne_X
          exact ne_X hs
        use (Subtype.val : Y → F) '' (s : Set Y)
        constructor
        · exact Subtype.coe_image_subset Y ↑s
        · constructor
          · apply s.finite_toSet.image
          · rw [Set.eq_empty_iff_forall_not_mem] at hs ⊢
            intro x hx
            simp only [mem_image, Finset.mem_coe, SetCoe.exists, Subtype.coe_mk, exists_and_right,
              exists_eq_right, iInf_eq_iInter, iInter_exists, mem_iInter, mem_sep_iff] at hx
            apply hs x
            rw [iInter_coe_set, mem_inter_iff, mem_iInter]
            constructor
            · obtain ⟨⟨j, hj⟩, hjs⟩ := hs_ne
              exact (hx j hj hjs).1
            · intro y
              rw [mem_iInter]
              intro hy
              rw [mem_iInter]
              intro hy'
              apply Set.inter_subset_right
              rw [← (hv (⟨y, hy⟩ : Y)).2]
              simp only [Subtype.coe_mk, mem_sep_iff]
              exact hx y hy hy'
      · -- hsZ
        rw [← not_le] at ht
        rw [Set.eq_empty_iff_forall_not_mem]
        intro x hx
        apply ht
        rw [mem_inter_iff, mem_iInter] at hx
        trans sup_y x
        · exact hinf_sup.1 ⟨x, hx.1, rfl⟩
        · rw [isLUB_le_iff (hsup_y x hx.1), mem_upperBounds]
          simp
          intro y hy
          suffices x ∈ X' y by
            exact this.2
          rw [(hv ⟨y, hy⟩).2]
          exact ⟨hx.1, hx.2 ⟨y, hy⟩⟩
    · -- hfyt
      rintro ⟨y, hy⟩
      specialize hfy y hy
      simp_rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfy
      obtain ⟨v, v_closed, hv⟩ := hfy t
      use v, v_closed
      simp only [← hv]; rfl

theorem _root_.IsMinOn.isGLB {α β : Type*} [Preorder β] {f : α → β} {s : Set α} {a :α}
  (hfsa : IsMinOn f s a) : IsGLB {f x | x ∈ s} (f a) := sorry

theorem _root_.IsMaxOn.isLUB {α β : Type*} [Preorder β]  {f : α → β} {s : Set α} {a :α}
  (hfsa : IsMaxOn f s a) : IsLUB {f x | x ∈ s} (f a) := sorry

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The Sion-von Neumann minimax theorem (saddle point form) -/
theorem exists_saddlePointOn :
    ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  -- Lemmes généraux de fonctions sci, scs qui remplacent
  have hmin_x (y) (hy : y ∈ Y) : ∃ x ∈ X, IsMinOn (f · y) X x := (hfy y hy).exists_isMinOn ne_X kX
  have hmax_y (x) (hx : x ∈ X) : ∃ y ∈ Y, IsMaxOn (f x) Y y := (hfx x hx).exists_isMaxOn ne_Y kY
  choose! ξ ξ_mem ξ_min using hmin_x
  choose! η η_mem η_max using hmax_y
  suffices hlsc : LowerSemicontinuousOn (fun x => f x (η x)) X by
    -- obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_iInf_of_isCompact ne_X kX hlsc
    obtain ⟨a, ha, ha'⟩ : ∃ a ∈ X, IsMinOn (fun x ↦ f x (η x)) X a := hlsc.exists_isMinOn ne_X kX
      -- hlsc: cette fonction  est semicontinue inférieurement en x
      -- X est compact, elle atteint son minimum
    use a, ha
    suffices husc : UpperSemicontinuousOn (fun y => f (ξ y) y) Y by
      obtain ⟨b, hb, hb'⟩ : ∃ b ∈ Y, IsMaxOn (fun y ↦ f (ξ y) y) Y b := husc.exists_isMaxOn ne_Y kY 
      -- obtain ⟨b, hb, hb'⟩ := UpperSemicontinuousOn.exists_iSup_of_isCompact ne_Y kY husc
      use b, hb
      intro x hx y hy
      trans f a (η a)
      · simp only [isMaxOn_iff] at η_max
        exact η_max a ha y hy
      trans f (ξ b) b
      · apply le_of_eq
        exact minimax X ne_X cX kX Y cY f hfx hfx' hfy hfy'
          (fun x ↦ f x (η x)) (fun x hx ↦ (η_max x hx).isLUB) (f a (η a)) ha'.isGLB
          (fun y ↦ f (ξ y) y) (fun y hy ↦ (ξ_min y hy).isGLB) (f (ξ b) b) hb'.isLUB 
      · simp only [isMinOn_iff] at ξ_min
        exact ξ_min b hb x hx
    -- husc
    intro y hy
    apply upperSemicontinuousWithinAt_iInf₂ ne_X kX _ (hfy y hy)
    intro x hx; exact hfx x hx y hy
  -- hlsc
  intro x hx
  apply lowerSemicontinuousWithinAt_iSup₂ ne_Y kY _ (hfx x hx)
  intro y hy; exact hfy y hy x hx


end general

section complete

namespace Complete

variable (f : E → F → β)
  [CompleteLinearOrder β] [DenselyOrdered β]

variable (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

variable (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
  (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

include ne_X cX cY kX hfx hfx' hfy hfy' in
theorem minimax : (⨅ x ∈ X, ⨆ y ∈ Y, f x y) = ⨆ y ∈ Y, ⨅ x ∈ X, f x y := by
  apply symm
  apply le_antisymm
  -- the obvious inclusion
  · exact iSup₂_iInf₂_le_iInf₂_iSup₂ X Y f
  -- the delicate inclusion
  · rw [← forall_lt_iff_le]
    intro t ht
    let X' (y : F) := ({x ∈ X | f x y ≤ t} : Set E)

    suffices hs : ∃ s : Set F, s ⊆ Y ∧ s.Finite ∧ (⋂ y ∈ s, X' y) = ∅ by
      obtain ⟨s, hsY, hs, hes⟩ := hs
      suffices hst : ∀ x ∈ X, ∃ y ∈ s, t < f x y by
        obtain ⟨y0, hy0, ht0⟩ := exists_lt_iInf_of_lt_iInf_of_finite
          X ne_X cX kX Y cY f hfx hfx' hfy hfy' hs hst hsY
        simp only [lt_iSup_iff, exists_prop]
        use y0, hy0
        -- TODO : make automatic for semicontinuous
        obtain ⟨a, ha, h⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact
          ne_X kX (hfy y0 hy0)
        exact lt_of_lt_of_le (ht0 a ha) (le_iInf₂_iff.mpr h)
      intro x hx
      by_contra hx'
      push_neg at hx'
      rw [Set.eq_empty_iff_forall_not_mem] at hes
      apply hes x
      simp only [mem_iInter, mem_setOf_eq, X', forall₂_and]
      exact ⟨fun _ _ ↦ hx, hx'⟩
    suffices hfyt : ∀ y : Y, ∃ vy : Set E, IsClosed vy ∧ X' y = X ∩ vy by
      let v : Y → Set E := fun y ↦ Exists.choose (hfyt y)
      have hv : ∀ y, IsClosed (v y) ∧ X' y = X ∩ v y := fun y ↦ (hfyt y).choose_spec
      suffices hsZ : _ by
        obtain ⟨s, hs⟩ := kX.elim_finite_subfamily_closed v (fun y => (hv y).1) hsZ
        have hs_ne : s.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hs_e
          simp only [hs_e, Finset.not_mem_empty, iInter_of_empty, iInter_univ, inter_univ] at hs
          rw [Set.nonempty_iff_ne_empty] at ne_X
          exact ne_X hs
        use (Subtype.val : Y → F) '' (s : Set Y)
        constructor
        · exact Subtype.coe_image_subset Y ↑s
        · constructor
          · apply s.finite_toSet.image
          · rw [Set.eq_empty_iff_forall_not_mem] at hs ⊢
            intro x hx
            simp only [mem_image, Finset.mem_coe, SetCoe.exists, Subtype.coe_mk, exists_and_right,
              exists_eq_right, iInf_eq_iInter, iInter_exists, mem_iInter, mem_sep_iff] at hx
            apply hs x
            rw [iInter_coe_set, mem_inter_iff, mem_iInter]
            constructor
            · obtain ⟨⟨j, hj⟩, hjs⟩ := hs_ne
              exact (hx j hj hjs).1
            · intro y
              rw [mem_iInter]
              intro hy
              rw [mem_iInter]
              intro hy'
              apply Set.inter_subset_right
              rw [← (hv (⟨y, hy⟩ : Y)).2]
              simp only [Subtype.coe_mk, mem_sep_iff]
              exact hx y hy hy'
      · -- hsZ
        rw [← not_le] at ht
        rw [Set.eq_empty_iff_forall_not_mem]
        intro x hx
        apply ht
        rw [mem_inter_iff, mem_iInter] at hx
        apply iInf₂_le_of_le x _ _
        exact hx.1
        simp only [iSup_le_iff]
        intro y hy
        suffices x ∈ X' y by
          exact this.2
        rw [(hv ⟨y, hy⟩).2]
        exact ⟨hx.1, hx.2 ⟨y, hy⟩⟩
    · -- hfyt
      rintro ⟨y, hy⟩
      specialize hfy y hy
      simp_rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfy
      obtain ⟨v, v_closed, hv⟩ := hfy t
      use v, v_closed
      simp only [← hv]; rfl

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The Sion-von Neumann minimax theorem (saddle point form) -/
theorem exists_saddlePointOn :
    ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  suffices hlsc : LowerSemicontinuousOn (fun x => ⨆ y ∈ Y, f x y) X by
    obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_iInf_of_isCompact ne_X kX hlsc
    use a, ha
    suffices husc : UpperSemicontinuousOn (fun y => ⨅ x ∈ X, f x y) Y by
      obtain ⟨b, hb, hb'⟩ := UpperSemicontinuousOn.exists_iSup_of_isCompact ne_Y kY husc
      use b, hb
      rw [isSaddlePointOn_iff' ha hb]
      rw [ha']
      rw [minimax X ne_X cX kX Y cY f hfx hfx' hfy hfy']
      rw [← hb']
    -- husc
    intro y hy
    apply upperSemicontinuousWithinAt_iInf₂ ne_X kX _ (hfy y hy)
    intro x hx; exact hfx x hx y hy
  -- hlsc
  intro x hx
  apply lowerSemicontinuousWithinAt_iSup₂ ne_Y kY _ (hfx x hx)
  intro y hy; exact hfy y hy x hx

end complete

end ERealSion

end EReal

-- JUSQU'ICI, TOUT VA BIEN…
-- IL RESTE À TRAITER LE CAS DES FONCTIONS À VALEURS RÉELLES
-- TODO : Remplacer ℝ et EReal par un type général convenable

section Real

namespace Sion

variable (f : E → F → ℝ)

variable (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

variable (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
  (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

/- The theorem is probably wrong without the additional hypothesis
that Y is compact. Indeed, if the image of (λ y, f x y) is not bounded above,
then supr is defined as 0, while the theorem should interpret it as infinity.

Possibilities :

- add hypotheses that guarantee the bdd_above condition
- replace the infimum on (x : X) by the infimum on the subtype of X
consisting of x such that (λ y, f x y) is bounded above.
(If that subtype is empty, the left hand side is +infinity for mathematicians,
but 0 for Lean… what about the rhs?)

-/

example : Monotone (Real.toEReal) := EReal.coe_strictMono.monotone

example : Continuous (Real.toEReal) := by exact continuous_coe_real_ereal

/- Here, one will need compactness on Y — otherwise, no hope that
the saddle point exists… -/
include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The minimax theorem, in the saddle point form -/
theorem existsSaddlePointOn :
  ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  -- Reduce to the cae of EReal-valued functions
  let φ : E → F → EReal := fun x y ↦ (f x y).toEReal
  -- suffices : ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y φ a b
  have hφx : ∀ x ∈ X, UpperSemicontinuousOn (fun y ↦ φ x y) Y := fun x hx ↦
    continuous_coe_real_ereal.comp_upperSemicontinuousOn (hfx x hx) EReal.coe_strictMono.monotone
  have hφx' : ∀ (x : E), x ∈ X → QuasiconcaveOn ℝ Y fun y ↦ φ x y := fun x hx ↦
    by convert (hfx' x hx).monotone_comp EReal.coe_strictMono.monotone
  have hφy : ∀ (y : F), y ∈ Y → LowerSemicontinuousOn (fun x ↦ φ x y) X := fun y hy ↦
    continuous_coe_real_ereal.comp_lowerSemicontinuousOn (hfy y hy) EReal.coe_strictMono.monotone
  have hφy': ∀ (y : F), y ∈ Y → QuasiconvexOn ℝ X fun x ↦ φ x y := fun y hy ↦
    by convert (hfy' y hy).monotone_comp EReal.coe_strictMono.monotone
  obtain ⟨a, ha, b, hb, hab⟩ :=
    ERealSion.exists_saddlePointOn X ne_X cX kX Y ne_Y cY kY φ hφx hφx' hφy hφy'
  use a, ha, b, hb
  intro x hx y hy
  simp only [← EReal.coe_le_coe_iff]
  exact hab x hx y hy

#print axioms existsSaddlePointOn

end Sion

end Real

#exit

section

namespace Order

def Complete (β : Type*) := WithBot (WithTop β)

local instance [LE β]: LE (Complete β) := WithBot.le

local instance [LinearOrder β] : LinearOrder (Complete β) := WithBot.linearOrder

-- TODO : start from a LinearOrder, DenselyOrdered and add with_top, with_bot
-- Problem : not Densely Ordered if it has min or sup…
#check eventually_nhdsSet_iff_forall
example (f : E → β) (hf : LowerSemicontinuousOn f X)
    {γ : Type*} [LinearOrder γ] (h : β → γ) (hh: StrictMono h) :
    LowerSemicontinuousOn (h ∘ f) X := by
  intro x hx c hc
  suffices ∃ (b : β), b < f x ∧ c ≤ h b by
    obtain ⟨b, hb, hcb⟩ := this
    exact Filter.Eventually.mono (hf x hx b hb) (fun _ hby ↦ lt_of_le_of_lt hcb (hh hby))
  sorry

example (f : E → β) (hf : LowerSemicontinuousOn f X) :
    LowerSemicontinuousOn (fun x ↦ some (some (f x)) : WithBot (WithTop β)) X := by
  intro x hx c hc
  suffices ∃ (b : β), b < f x ∧ c ≤ h b by
    obtain ⟨b, hb, hcb⟩ := this
    exact Filter.Eventually.mono (hf x hx b hb) (fun _ hby ↦ lt_of_le_of_lt hcb (hh hby))

  sorry

section noncomplete

#check IsLUB
variable (f : E → F → β) [LinearOrder β] [DenselyOrdered β]

variable (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

variable (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
  (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

noncomputable def φ₁ (y : Y) :
    { a ∈ X | ∀ x ∈ X, f a y ≤ f x y} := by
  choose a ha hmin using LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_X kX (hfy y y.prop)
  exact ⟨a, ha, hmin⟩

example : UpperSemicontinuous (fun (y : Y) ↦ f (φ₁ X ne_X kX Y f hfy y).1 y) := by
  intro y b hby
  set A := (φ₁ X ne_X kX Y f hfy y) with hA
  rcases A with ⟨a, ha, ha'⟩
  simp only [mem_setOf_eq, ← hA] at hby
  specialize hfx a ha y y.prop b hby
  rw [eventually_nhdsWithin_iff] at hfx
  rw [nhds_subtype_eq_comap]
  simp only [mem_setOf_eq, Filter.eventually_comap, Subtype.forall]
  apply Filter.Eventually.mono hfx
  rintro x hx' x' hx ⟨rfl⟩
  set A' := φ₁ X ne_X kX Y f hfy ⟨x, hx⟩ with hA'
  rcases A' with ⟨a', ha'mem, ha'min⟩
  specialize hx' hx; simp only at hx'
  simp only [gt_iff_lt]
  simp only at ha'min
  apply lt_of_le_of_lt _ hx'
  apply ha'min a ha


end noncomplete
