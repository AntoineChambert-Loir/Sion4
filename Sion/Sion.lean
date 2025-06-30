-- import Mathlib.Topology.Instances.EReal
-- import Mathlib.Data.Real.Basic

import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Instances.EReal.Lemmas
import Sion.Concavexity
import Sion.ForMathlib.Misc
import Sion.SaddlePoint
import Sion.Semicontinuous
import Sion.Semicontinuous
import Sion.Sublevel

/-! # Formalization of the von Neumann Sion theorem

## Statements

`Sinon.exists_isSaddlePointOn` :
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

## Remark on implementation
  * The essential part of the proof holds for a function
  `f : X → Y → β`, where `β` is a complete dense linear order.
  * We have written part of it for just a dense linear order,

  * On the other hand, if the theorem holds for such `β`,
  it must hold for any linear order, for the reason that
  any linear order embeds into a complete dense linear order.
  However, this result does not seem to be known to Mathlib.
  * When `β` is `ℝ`, one can use `Real.toEReal` and one gets a proof for `ℝ`.

## TODO

Explicit the classical particular cases (in particular, von Neumann)

## References

- Neumann, John von (1928). « Zur Theorie der Gesellschaftsspiele ».
Mathematische Annalen 100 (1): 295‑320.  https://doi.org/10.1007/BF01448847.

- Sion, Maurice (1958). « On general minimax theorems ».
Pacific Journal of Mathematics 8 (1): 171‑76.

- Komiya, Hidetoshi (1988). « Elementary Proof for Sion’s Minimax Theorem ».
Kodai Mathematical Journal 11 (1). https://doi.org/10.2996/kmj/1138038812.

-/

open Set

namespace Sion

section LinearOrder

variable {E F : Type*} {β : Type*} [LinearOrder β]
    (X : Set E) (Y : Set F) (f : E → F → β)

/-- The familywise sublevel sets of `f` -/
def C (b : β) (z : F) : Set X :=
  (fun x => f x z) ∘ (fun x ↦ ↑x)⁻¹' Iic b

variable {X Y f}

theorem mem_C_iff {b : β} {y : Y} {x : X} :
    x ∈ C X f b y ↔ f x y ≤ b := by simp [C]

-- private
theorem monotone_C {u v : β} (y : Y) (h : u ≤ v) :
    C X f u y ⊆ C X f v y :=
  fun _ hxu ↦ le_trans hxu h

variable (X Y f) in
def J [AddCommGroup F] [Module ℝ F]
    (b b' : β) (y y' : Y) : Set (segment ℝ y.val y'.val) :=
    {z | C X f b z ⊆ C X f b' y}

theorem mem_J_iff [AddCommGroup F] [Module ℝ F]
    {b b' : β} {y y' : Y} {z : segment ℝ y.val y'.val} :
    z ∈ J X Y f b b' y y' ↔ C X f b z ⊆ C X f b' y := by
  simp only [mem_setOf_eq, J]

-- unused?
theorem y_mem_J  [AddCommGroup F] [Module ℝ F]
    {b b' : β} {y y' : Y} (hbb' : b ≤ b') :
    (⟨y.val, left_mem_segment ℝ y.val y'.val⟩ : segment ℝ y.val y'.val) ∈ J X Y f b b' y y' :=
  monotone_C _ hbb'

-- private
theorem disjoint_C {a : E} {b : β} {y y' : Y}
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y') :
    Disjoint (C X f b y) (C X f b y') := by
  rw [Set.disjoint_iff]
  rintro ⟨x, hx⟩ ⟨hx1, hx2⟩
  simp only [mem_empty_iff_false]
  apply not_le_of_gt hb
  apply le_trans (ha x hx)
  simp only [sup_le_iff]
  exact ⟨hx1, hx2⟩

theorem nonempty_C [TopologicalSpace E]
    (ne_X : X.Nonempty) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (y : Y) {b : β} (h : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ b) :
    (C X f b y).Nonempty := by
  rcases y with ⟨y, hy⟩
  obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_X kX (hfy y hy)
  obtain ⟨x', hx', hx'b⟩ := h y hy
  exact ⟨⟨x, hx⟩, le_trans (hx_le x' hx') hx'b⟩

theorem isClosed_C [TopologicalSpace E]
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (b : β) (y : Y) :
    IsClosed (C X f b y) := by
  specialize hfy y.val y.prop
  rw [lowerSemicontinuousOn_iff_restrict] at hfy
  rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy
  exact hfy b

-- private
theorem isPreconnected_C [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E]
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x ↦ f x y)
    (b : β) (y : Y) :
    IsPreconnected (C X f b y) :=
  (hfy' y.val y.prop).isPreconnected_preimage

-- private
theorem C_subset_union [AddCommGroup F] [Module ℝ F]
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)
    (b : β) (y y' : Y) (z : segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∪ C X f b y' := fun x hx ↦ by
    simp only [Set.mem_union, mem_C_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y ⊓ f x y')
    rw [convex_iff_segment_subset] at hfx'
    specialize hfx' ⟨y.prop, inf_le_left⟩ ⟨y'.prop, inf_le_right⟩ z.prop
    exact le_trans hfx'.2 hx

-- private
theorem C_subset_or [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
    (cY : Convex ℝ Y)
    (a : E) (b : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y')
    (z : segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∨ C X f b z ⊆ C X f b y' := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_C hfy' b ⟨z, cY.segment_subset y.prop y'.prop z.prop⟩)
    _ _ (isClosed_C hfy b y) (isClosed_C hfy b y')
    (C_subset_union hfx' b y y' z)
  rw [Set.disjoint_iff_inter_eq_empty.mp (disjoint_C ha hb),
    Set.inter_empty]

theorem C_subset_or'
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (cY : Convex ℝ Y)
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)
    (a : E) (b : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y')
    (z : Y) (hz : z.val ∈ segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∨ C X f b z ⊆ C X f b y' := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_C hfy' b ⟨z, cY.segment_subset y.prop y'.prop hz⟩)
    _ _ (isClosed_C hfy b y) (isClosed_C hfy b y')
    (C_subset_union hfx' b y y' ⟨z, hz⟩)
  rw [Set.disjoint_iff_inter_eq_empty.mp (disjoint_C ha hb),
    Set.inter_empty]

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (ne_X : X.Nonempty) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (cY : Convex ℝ Y) (kY : IsCompact Y)
    (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

-- private
include ne_X kX hfx hfx' cY hfy hfy' in
omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
theorem isClosed_J
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
    apply Or.resolve_right (C_subset_or hfx' hfy hfy' cY a b' y y' ha hb' z')
    intro hz'2
    have hz'Y :=(convex_iff_segment_subset.mp cY) y.prop y'.prop z'.prop
    apply (nonempty_C ne_X kX hfy ⟨z', hz'Y⟩ hb).not_subset_empty
    simp only [← disjoint_iff_inter_eq_empty.mp (disjoint_C ha hb')]
    apply Set.subset_inter hz'
    apply subset_trans (monotone_C _ hbb'.le) hz'2

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
    apply Filter.Eventually.of_forall
    intro z hzt'
    rintro ⟨hz, hz'⟩
    exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩

variable [DenselyOrdered β]

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
      ⟨z, hz⟩ ∈ J1 ↔ C X f t z ⊆ C X f t' y1 :=
    fun z _ ↦ by simp [J1, J]
  let φ : segment ℝ y1 y2 ≃ₜ segment ℝ y2 y1 := by
    apply Homeomorph.subtype (Homeomorph.refl F)
    intro x
    rw [segment_symm ℝ y2 y1]
    simp only [Homeomorph.refl_apply, id_eq]
  let J2 := φ ⁻¹' (J X Y f t t' ⟨y2, hy2⟩ ⟨y1, hy1⟩)
  have mem_J2_iff (z) (hz : z ∈ segment ℝ y1 y2) :
      ⟨z, hz⟩ ∈ J2 ↔ C X f t z ⊆ C X f t' y2 := by
    simp [J2, J, φ, segment_symm ℝ y2 y1, hz]
  have hJ1J2 : J1 ∩ J2 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    simp only [mem_inter_iff, not_and]
    rintro ⟨z, hz⟩ hz1 hz2
    simp only [mem_J1_iff] at hz1
    simp only [mem_J2_iff] at hz2
    have hz_mem_Y : z ∈ Y := cY.segment_subset hy1 hy2 hz
    apply Set.Nonempty.not_subset_empty (nonempty_C ne_X kX hfy ⟨z, hz_mem_Y⟩ hinfi_le)
    rw [Set.subset_empty_iff, ← bot_eq_empty, ← disjoint_self]
    exact Set.disjoint_of_subset hz1 hz2 (disjoint_C (y := ⟨y1, hy1⟩) (y' := ⟨y2, hy2⟩) ha' ht')
  have hJ1_union_J2 : J1 ∪ J2 = segment ℝ y1 y2 := by
    ext z
    constructor
    · rintro ⟨⟨z, hz⟩, _, rfl⟩
      exact hz
    · intro hz
      have hz_mem_Y : z ∈ Y := cY.segment_subset hy1 hy2 hz
      use ⟨z, hz⟩
      refine ⟨?_, rfl⟩
      rcases C_subset_or hfx' hfy hfy' cY a t' ⟨y1, hy1⟩ ⟨y2, hy2⟩ ha' ht' ⟨z, hz⟩ with (h1 | h2)
      · left
        simp only [mem_J1_iff]
        exact subset_trans (monotone_C ⟨z, hz_mem_Y⟩ htt'.le) h1
      · right
        simp only [mem_J2_iff]
        exact subset_trans (monotone_C ⟨z, hz_mem_Y⟩ htt'.le) h2
  suffices IsPreconnected (Set.univ : Set (segment ℝ y1 y2)) by
    rw [isPreconnected_iff_subset_of_disjoint_closed] at this
    rw [Set.eq_empty_iff_forall_notMem] at hJ1J2
    rcases this J1 J2 ?_ ?_ ?_ ?_ with (h1 | h2)
    · apply hJ1J2 ⟨y2, right_mem_segment ℝ y1 y2⟩
      rw [Set.mem_inter_iff]
      refine ⟨h1 (Set.mem_univ _), ?_⟩
      rw [mem_J2_iff]
      apply monotone_C ⟨y2, hy2⟩ htt'.le
    · apply hJ1J2 ⟨y1, left_mem_segment ℝ y1 y2⟩
      rw [Set.mem_inter_iff]
      refine ⟨?_, h2 (Set.mem_univ _)⟩
      rw [mem_J1_iff]
      apply monotone_C ⟨y1, hy1⟩ htt'.le
  · rw [← Set.eq_empty_iff_forall_notMem] at hJ1J2
    simp only [hJ1J2, inter_empty]
  · -- is preconnected
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]
    exact Convex.isPreconnected (convex_segment y1 y2)
  · -- is closed J1
    exact isClosed_J ne_X kX hfy hfy' cY hfx hfx' a t t' ⟨y1, hy1⟩ ⟨y2, hy2⟩ ha' hinfi_le ht' htt'
  · -- is closed J2
    rw [Homeomorph.isClosed_preimage]
    simp only [sup_comm (f _ y1)] at ha' ht'
    refine isClosed_J ne_X kX hfy hfy' cY hfx hfx' a t t' ⟨y2, hy2⟩ ⟨y1, hy1⟩ ha' hinfi_le ht' htt'
  · -- univ ⊆ J1 ∪ J2
    rintro ⟨z, hz⟩ _
    rw [← hJ1_union_J2] at hz
    rcases hz with ⟨⟨z, hz'⟩, hz'', rfl⟩
    exact hz''

variable (cX : Convex ℝ X)

include ne_X cX cY kX hfx hfx' hfy hfy' in
theorem exists_lt_iInf_of_lt_iInf_of_finite
    {s : Set F} (hs : s.Finite) (hsY : s ⊆ Y)
    {t : β} (ht : ∀ x ∈ X, ∃ y ∈ s, t < f x y) :
    ∃ y0 ∈ Y, ∀ x ∈ X, t < f x y0 := by
  induction s, hs using Set.Finite.induction_on
    generalizing X with
  | empty => -- empty case
    obtain ⟨x, hx⟩ := id ne_X
    exfalso
    simpa using ht x hx
  | @insert b s _ hs hrec =>  -- insert case
    have hb : (b ∈ Y) := hsY (mem_insert b s)
    let X' := LeSublevelOn X (fun x ↦ f x b) t
    rcases Set.eq_empty_or_nonempty X' with X'_e | X'_ne
    · simp only [X', leSublevelOn_empty_iff] at X'_e
      use b, hb
    -- the nonempty case
    have hX'X : X' ⊆ X := leSublevelOn_subset
    have kX' : IsCompact X' := isCompact_leSublevelOn (hfy b hb) kX
    have cX' : Convex ℝ X' := hfy' b hb t
    specialize hrec X'_ne kX'
      (fun y hy ↦ LowerSemicontinuousOn.mono (hfy y hy) hX'X)
      (fun y hy ↦ cX'.quasiconvexOn_restrict (hfy' y hy) hX'X)
      (fun x hx' ↦ hfx x (hX'X hx'))
      (fun x hx' ↦ hfx' x (hX'X hx'))
      cX'
    have ht_lt : ∀ x ∈ X', ∃ y ∈ s, t < f x y := by
        /- sinon, si  infi x ∈ X', supr y ∈ s f x y ≤ t
          pour tout t' > t, il existe x ∈ X', supr y ∈ s f x y ≤ t',
          comme x ∈ X' et t ≤ t', on  a supr y ∈ insert b s f x y  ≤ t',
          donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t',
          donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t -/
      intro x hx
      obtain ⟨y, hy, h⟩ := ht x hx.1
      rcases hy with hy | hy
      · exfalso
        rw [hy, ← not_le] at h
        exact h hx.2
      · exact ⟨y, hy, h⟩
    obtain ⟨y1, hy1, hty1⟩ := hrec (subset_trans (subset_insert b s) hsY) ht_lt
    apply exists_lt_iInf_of_lt_iInf_of_sup ne_X kX hfy hfy' cY hfx hfx' hb hy1
    intro x hx
    by_cases hx' : x ∈ X'
    · exact lt_of_lt_of_le (hty1 x hx') (le_sup_right)
    · apply lt_of_lt_of_le _ (le_sup_left)
      rw [← not_le]
      exact fun h ↦ hx' ⟨hx, h⟩

    -- hsup_y : ∀ x ∈ X, sup_y x = sup [y ∈ Y] f x y
    -- hinf_x : ∀ y ∈ Y, inf_x y = inf [x ∈ X] f x y
    -- hinf_sup : inf_sup = inf [x ∈ X] sup_y x
    -- hsup_inf : sup_inf = sup [y ∈ Y] inf_x y
include ne_X cX cY kX hfx hfx' hfy hfy' in
/-- A minimax theorem without completeness, using `IsGLB` and `IsULB`. -/
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
  rcases eq_empty_or_nonempty Y with ⟨rfl⟩ | ne_Y
  · -- the case when `Y` is empty is trivial
    simp only [mem_empty_iff_false, IsEmpty.forall_iff, implies_true, false_and, exists_const,
      setOf_false, isLUB_empty_iff] at *
    replace hsup_y : ∀ x ∈ X,  sup_y x = sup_inf :=
      fun x hx ↦ le_antisymm (hsup_y x hx sup_inf) (hsup_inf (sup_y x))
    simp only [isGLB_iff_le_iff] at hinf_sup
    have : {t | ∃ x ∈ X, sup_y x = t} = {sup_inf} := by
      ext t
      simp only [mem_setOf_eq, mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, hxt⟩
        rw [← hxt, hsup_y x hx]
      · intro ht
        obtain ⟨x, hx⟩ := ne_X
        exact ⟨x, hx, ht ▸ hsup_y x hx⟩
    simp [this] at hinf_sup
    rw [← hinf_sup]
  -- when `Y` is not empty
  rw [← forall_lt_iff_le]
  intro t ht
  have : ⋂ y ∈ Y, LeSublevelOn X (fun x ↦ f x y) t = ∅ := by
    rw [inter_leSublevelOn_empty_iff ne_Y]
    intro x hx
    by_contra! H
    rw [lt_isGLB_iff hinf_sup] at ht
    obtain ⟨c, hc, htc⟩ := ht
    simp [mem_lowerBounds] at hc
    specialize hc x hx
    apply not_le.mpr  htc (le_trans hc _)
    simpa [isLUB_le_iff (hsup_y x hx), mem_upperBounds] using H
  rw [inter_leSublevelOn_empty_iff_exists_finset_inter ne_Y kX hfy] at this
  obtain ⟨s, hs⟩ := this
  have hs' (x) (hx : x ∈ X) :
      ∃ y ∈ Subtype.val '' (s : Set Y), t < f x y := by
    obtain ⟨i, hi, hi'⟩ := hs x hx
    use i.val
    simp [hi, hi']
  choose y0 hy0 ht0 using exists_lt_iInf_of_lt_iInf_of_finite
        ne_X kX hfy hfy' cY hfx hfx' cX
        (t := t)
        (toFinite _) (Subtype.coe_image_subset Y ↑s)
  simp [lt_isLUB_iff hsup_inf]
  use y0 hs', hy0 hs'
  specialize ht0 hs'
  obtain ⟨a, ha, h⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact
        ne_X kX (hfy (y0  hs') (hy0 hs'))
  apply lt_of_lt_of_le (ht0 a ha)
  simpa [le_isGLB_iff (hinf_x (y0 hs') (hy0 hs')), mem_lowerBounds]

variable (ne_Y : Y.Nonempty) (kY : IsCompact Y)
include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The Sion-von Neumann minimax theorem (saddle point form) -/
theorem exists_isSaddlePointOn' :
    ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  have hmax_y (x) (hx : x ∈ X) : ∃ y ∈ Y, IsMaxOn (f x) Y y := (hfx x hx).exists_isMaxOn ne_Y kY
  choose! η η_mem η_max using hmax_y
  have hlsc : LowerSemicontinuousOn (fun x => f x (η x)) X :=
    lowerSemicontinuousOn_of_forall_isMaxOn_and_mem hfy η_mem η_max
  obtain ⟨a, ha, ha'⟩ : ∃ a ∈ X, IsMinOn (fun x ↦ f x (η x)) X a := hlsc.exists_isMinOn ne_X kX
  use a, ha
  have hmin_x (y) (hy : y ∈ Y) : ∃ x ∈ X, IsMinOn (f · y) X x := (hfy y hy).exists_isMinOn ne_X kX
  choose! ξ ξ_mem ξ_min using hmin_x
  have husc := upperSemicontinuousOn_of_forall_isMinOn_and_mem hfx ξ_mem ξ_min
  obtain ⟨b, hb, hb'⟩ : ∃ b ∈ Y, IsMaxOn (fun y ↦ f (ξ y) y) Y b := husc.exists_isMaxOn ne_Y kY
  use b, hb
  intro x hx y hy
  trans f a (η a)
  · simp only [isMaxOn_iff] at η_max
    exact η_max a ha y hy
  trans f (ξ b) b
  · apply le_of_eq
    apply minimax ne_X kX hfy hfy' cY hfx hfx' cX
      (fun x ↦ f x (η x))
      (fun x hx ↦ (η_max x hx).isLUB (η_mem x hx))
      (f a (η a))
      (ha'.isGLB ha)
      (fun y ↦ f (ξ y) y)
      (fun y hy ↦ (ξ_min y hy).isGLB (ξ_mem y hy))
      (f (ξ b) b)
      (hb'.isLUB hb)
  · simp only [isMinOn_iff] at ξ_min
    exact ξ_min b hb x hx

end LinearOrder

section CompleteLinearOrder

variable {E F β : Type*} [CompleteLinearOrder β] [DenselyOrdered β]
variable {X : Set E} {Y : Set F} {f : E → F → β}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E ↦ f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  (cY : Convex ℝ Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
  (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

include ne_X cX cY kX hfx hfx' hfy hfy' in
/-- A minimax theorem in inf-sup form, for complete linear orders. -/
theorem minimax' : (⨅ x ∈ X, ⨆ y ∈ Y, f x y) = ⨆ y ∈ Y, ⨅ x ∈ X, f x y := by
  apply symm
  apply le_antisymm
  -- the obvious inclusion
  · exact iSup₂_iInf₂_le_iInf₂_iSup₂ X Y f
  -- the delicate inclusion
  rcases eq_empty_or_nonempty Y with ⟨rfl⟩ | ne_Y
  · simp [biInf_const ne_X]
  rw [← forall_lt_iff_le]
  intro t ht
  have : ⋂ y ∈ Y, LeSublevelOn X (fun x ↦ f x y) t = ∅ := by
    rw [inter_leSublevelOn_empty_iff ne_Y]
    intro x hx
    by_contra! H
    rw [lt_iInf_iff] at ht
    obtain ⟨c, htc, hc⟩ := ht
    apply not_le.mpr htc
    simp only [le_iInf_iff] at hc
    apply le_trans (hc x hx)
    simpa only [iSup_le_iff]
  rw [inter_leSublevelOn_empty_iff_exists_finset_inter ne_Y kX hfy] at this
  obtain ⟨s, hs⟩ := this
  have hs' (x) (hx : x ∈ X) :
      ∃ y ∈ Subtype.val '' (s : Set Y), t < f x y := by
    obtain ⟨i, hi, hi'⟩ := hs x hx
    use i.val
    simp [hi, hi']
  choose y0 hy0 ht0 using exists_lt_iInf_of_lt_iInf_of_finite
        ne_X kX hfy hfy' cY hfx hfx' cX
        (t := t)
        (toFinite _) (Subtype.coe_image_subset Y ↑s)
  simp only [lt_iSup_iff]
  use y0 hs', hy0 hs'
  specialize ht0 hs'
  obtain ⟨a, ha, h⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact
        ne_X kX (hfy (y0  hs') (hy0 hs'))
  apply lt_of_lt_of_le (ht0 a ha)
  simpa only [le_iInf_iff]

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The Sion-von Neumann minimax theorem (saddle point form),
case of complete linear orders. -/
theorem exists_saddlePointOn' :
    ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  have hlsc : LowerSemicontinuousOn (fun x => ⨆ y ∈ Y, f x y) X := by
    intro x hx
    apply lowerSemicontinuousWithinAt_iSup₂ ne_Y kY _ (hfx x hx)
    intro y hy; exact hfy y hy x hx
  have husc : UpperSemicontinuousOn (fun y => ⨅ x ∈ X, f x y) Y := by
    intro y hy
    apply upperSemicontinuousWithinAt_iInf₂ ne_X kX _ (hfy y hy)
    intro x hx; exact hfx x hx y hy
  obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_iInf_of_isCompact ne_X kX hlsc
  obtain ⟨b, hb, hb'⟩ := UpperSemicontinuousOn.exists_iSup_of_isCompact ne_Y kY husc
  use a, ha, b, hb
  rw [isSaddlePointOn_iff' ha hb, ha', minimax' ne_X cX kX hfy hfy' cY hfx hfx', ← hb']

end CompleteLinearOrder

section Real

variable {E F : Type*}
variable {X : Set E} {Y : Set F} {f : E → F → ℝ}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E ↦ f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  (cY : Convex ℝ Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
  (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The minimax theorem, in the saddle point form -/
theorem exists_isSaddlePointOn :
  ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  -- Reduce to the cae of EReal-valued functions
  let φ : E → F → EReal := fun x y ↦ (f x y).toEReal
  -- suffices : ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y φ a b
  have hφx (x) (hx : x ∈ X) : UpperSemicontinuousOn (fun y ↦ φ x y) Y := by
    convert Continuous.comp_upperSemicontinuousOn continuous_coe_real_ereal (hfx x hx) EReal.coe_strictMono.monotone
  have hφx' (x) (hx : x ∈ X) : QuasiconcaveOn ℝ Y fun y ↦ φ x y := by
    convert (hfx' x hx).monotone_comp EReal.coe_strictMono.monotone
  have hφy (y) (hy : y ∈ Y) : LowerSemicontinuousOn (fun x ↦ φ x y) X := by
    convert Continuous.comp_lowerSemicontinuousOn continuous_coe_real_ereal (hfy y hy) EReal.coe_strictMono.monotone
  have hφy' (y) (hy : y ∈ Y) : QuasiconvexOn ℝ X fun x ↦ φ x y := by
    convert (hfy' y hy).monotone_comp EReal.coe_strictMono.monotone
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_isSaddlePointOn' ne_X kX hφy hφy' cY kY hφx hφx' cX ne_Y
  use a, ha, b, hb
  intro x hx y hy
  simp only [← EReal.coe_le_coe_iff]
  exact hab x hx y hy

end Real

end Sion

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


