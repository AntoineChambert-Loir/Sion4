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


section SaddlePoint

variable {E F : Type _} {β : Type _} 
variable (X : Set E) (Y : Set F) (f : E → F → β)

/-- The trivial minimax inequality -/
theorem iSup₂_iInf₂_le_iInf₂_iSup₂ [CompleteLinearOrder β]: 
  (⨆ y ∈ Y, ⨅ x ∈ X, f x y) ≤ ⨅ x ∈ X, ⨆ y ∈ Y, f x y := by
  rw [iSup₂_le_iff]; intro y hy
  rw [le_iInf₂_iff]; intro x hx
  exact iInf₂_le_of_le x hx (le_iSup₂_of_le y hy (le_refl _))
#align ereal_sion.supr₂_infi₂_le_infi₂_supr₂ iSup₂_iInf₂_le_iInf₂_iSup₂

-- [Hiriart-Urruty, (4.1.4)]
/-- The pair (a,b) is a saddle point of f on X × Y 
  (does not enforce that a ∈ X and b ∈ Y) -/
def IsSaddlePointOn  [Preorder β] 
    (a : E) (b : F) :=
  ∀ x ∈ X, ∀ y ∈ Y, f a y ≤ f x b
#align is_saddle_point_on IsSaddlePointOn

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
    suffices : f a y ≤ f a b
    · apply le_trans this
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

variable (f : E → F → β) [CompleteLinearOrder β] [DenselyOrdered β]
  
  -- [CompleteLinearOrderedAddCommMonoid β] [OrderedAddCommMonoid β] [DenselyOrdered β]
  
-- has to be removed from the definition of Quasiconcave / Quasiconvex

variable (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

variable (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
  (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

theorem exists_lt_iInf_of_lt_iInf_of_sup {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y) {t : β}
    (ht : t < ⨅ x ∈ X, f x y1 ⊔ f x y2) : ∃ y0 ∈ Y, t < ⨅ x ∈ X, f x y0 :=
  by
  by_contra' hinfi_le
  obtain ⟨t', htt', ht'⟩ := 
  -- : t < t', ht' : t' < ⨅ x ∈ X, f x y1 ⊔ f x y2⟩ := 
    exists_between ht
  let C : β → F → Set X := 
    fun u z => (fun x => f x z) ∘ (fun x ↦ ↑x)⁻¹' Iic u
  have C_eq : ∀ (u : β) (z : F), 
    C u z = (fun x ↦ f x z) ∘ (fun (x : X) ↦ ↑x) ⁻¹' (Iic u) := by
    intro u z
    rfl
  have mem_C_iff : ∀ (u z) (x : X), x ∈ C u z ↔ f x z ≤ u := by 
    intro u z x; rfl
  have hC : ∀ u v z, u ≤ v → C u z ⊆ C v z :=
    by
    intro u v z h
    rintro x hxu
    rw [mem_C_iff] at hxu ⊢
    exact le_trans hxu h
  -- Uses that X is compact and nonempty !
  have hC_ne : ∀ z ∈ Y, (C t z).Nonempty := by
    intro z hz
    obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_X kX (hfy z hz)
    use ⟨x, hx⟩
    rw [mem_C_iff, Subtype.coe_mk]
    refine' le_trans _ (hinfi_le z hz)
    rw [le_iInf₂_iff]; intro x' hx'; exact hx_le x' hx'
  have hC_closed : ∀ u, ∀ {z}, z ∈ Y → IsClosed (C u z) :=  by
    intro u z hz 
    specialize hfy z hz
    rw [lowerSemicontinuousOn_iff_restrict] at hfy 
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy 
    exact hfy u
  have hC_preconnected : ∀ u, ∀ {z}, z ∈ Y → IsPreconnected (C u z) := by
    intro u z hz
    rw [C_eq]
    exact (hfy' z hz).isPreconnected_preimage
  have hC_disj : Disjoint (C t' y1) (C t' y2) :=
    by
    refine' Set.disjoint_iff.mpr 
      fun (x : X) hx => not_lt_of_le (iInf₂_le_of_le (x : E) _ _) ht'
    · exact x.2
    · exact sup_le_iff.mpr hx
  have hC_subset : ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∪ C t' y2 := by
    intro z hz x hx
    simp only [Set.mem_union, mem_C_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y1 ⊓ f x y2)
    rw [convex_iff_segment_subset] at hfx' 
    specialize hfx' ⟨hy1, inf_le_left⟩ ⟨hy2, inf_le_right⟩ hz
    exact le_trans hfx'.2 hx
  have hC_subset_or : 
    ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∨ C t' z ⊆ C t' y2 := by
    intro z hz
    apply isPreconnected_iff_subset_of_disjoint_closed.mp
      (hC_preconnected _ (cY.segment_subset hy1 hy2 hz)) 
      _ _  (hC_closed _ hy1) (hC_closed _ hy2) (hC_subset _ hz)
    rw [Set.disjoint_iff_inter_eq_empty.mp hC_disj, Set.inter_empty]
  /- have segment_subset : segment ℝ y1 y2 ⊆ Y := 
    convex_iff_segment_subset.mp cY hy1 hy2 -/
  let J1 := {z : segment ℝ y1 y2 | C t z ⊆ C t' y1}
  -- do we really need this ? (I can't do without it)
  have mem_J1_iff : ∀ z : segment ℝ y1 y2, z ∈ J1 ↔ C t z ⊆ C t' y1 := by intro z; rfl

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
    suffices : ∃ z ∈ J1, x ∈ C t' (z : F)
    obtain ⟨z, hz, hxz⟩ := this
    suffices : C t' z ⊆ C t' y1; exact this hxz
    apply Or.resolve_right (hC_subset_or z z.2)
    intro hz2
    apply Set.Nonempty.not_subset_empty (hC_ne z ((convex_iff_segment_subset.mp cY) hy1 hy2 z.2))
    rw [← disjoint_iff_inter_eq_empty.mp hC_disj]
    apply Set.subset_inter hz
    exact subset_trans (hC t t' z (le_of_lt htt')) hz2
    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [UpperSemicontinuousOn, UpperSemicontinuousWithinAt] at hfx 
    specialize hfx x.val x.prop y (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt')
    -- We rewrite h into an ∃ᶠ form
    rw [Filter.clusterPt_principal_subtype_iff_frequently (cY.segment_subset hy1 hy2)] at h 
    suffices this :
      ∀ᶠ z : F in nhdsWithin y Y,
        (∃ hz : z ∈ segment ℝ y1 y2, (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1) →
          ∃ hz : z ∈ segment ℝ y1 y2, x ∈ C t' z ∧ (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1
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
  -- bizarrely, this is necessary to add this lemma, 
  -- rien du genre  rw set.mem_sep_iff ne marche…
  have mem_J2_iff : ∀ z : segment ℝ y1 y2, z ∈ J2 ↔ C t z ⊆ C t' y2 := by 
    intro z; rfl 
  have hy2_mem_J2 : (⟨y2, right_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J2 := by
    simp only [mem_setOf_eq] -- rw [mem_J2_iff]
    apply hC
    exact le_of_lt htt'
  have hJ2_closed : IsClosed J2 := by
    rw [isClosed_iff_clusterPt]
    intro y h x hx
    suffices : ∃ z ∈ J2, x ∈ C t' (z : F)
    obtain ⟨z, hz, hxz⟩ := this
    suffices : C t' z ⊆ C t' y2; exact this hxz
    apply Or.resolve_left (hC_subset_or z z.2)
    intro hz2
    apply Set.Nonempty.not_subset_empty (hC_ne z ((convex_iff_segment_subset.mp cY) hy1 hy2 z.2))
    rw [← disjoint_iff_inter_eq_empty.mp hC_disj]
    refine' Set.subset_inter (subset_trans (hC t t' z (le_of_lt htt')) hz2) hz
    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [UpperSemicontinuousOn, UpperSemicontinuousWithinAt] at hfx 
    specialize hfx x.val x.prop y (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt')
    -- We rewrite h into an ∃ᶠ form
    rw [Filter.clusterPt_principal_subtype_iff_frequently (cY.segment_subset hy1 hy2)] at h 
    suffices this :
      ∀ᶠ z : F in nhdsWithin y Y,
        (∃ hz : z ∈ segment ℝ y1 y2, (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J2) →
          ∃ hz : z ∈ segment ℝ y1 y2, x ∈ C t' z ∧ (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J2
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
    apply Set.Nonempty.not_subset_empty (hC_ne z (cY.segment_subset hy1 hy2 z.prop))
    rw [Set.subset_empty_iff, ← bot_eq_empty, ← disjoint_self]
    exact Set.disjoint_of_subset hz1 hz2 hC_disj
  have hJ1_union_J2 : J1 ∪ J2 = Set.univ :=
    by
    rw [← Set.top_eq_univ, eq_top_iff]
    intro z _
    rw [Set.mem_union, mem_J1_iff, mem_J2_iff]
    cases' hC_subset_or z z.prop with h1 h2
    left; exact Set.Subset.trans (hC t t' z (le_of_lt htt')) h1
    right; exact Set.Subset.trans (hC t t' z (le_of_lt htt')) h2
  suffices this : IsPreconnected (Set.univ : Set (segment ℝ y1 y2))
  · rw [isPreconnected_iff_subset_of_disjoint_closed] at this 
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
#align ereal_sion.exists_lt_infi_of_lt_infi_of_sup ERealSion.exists_lt_iInf_of_lt_iInf_of_sup

theorem exists_lt_iInf_of_lt_iInf_of_finite {s : Set F} (hs : s.Finite) {t : β}
    (ht : t < ⨅ x ∈ X, ⨆ y ∈ s, f x y) : 
  s ⊆ Y → ∃ y0 ∈ Y, t < ⨅ x ∈ X, f x y0 :=
  by
  revert X
  --  
  refine' Set.Finite.induction_on hs _ _
  · -- empty case
    intro X ne_X _ _ _ _ _ _ 
    haveI : Nonempty X := nonempty_coe_sort.mpr ne_X
    simp only [biInf_const ne_X, mem_empty_iff_false, ciSup_false, ciSup_const,
      not_lt_bot, IsEmpty.forall_iff]
  · -- insert case
    intro b s _ _ hrec X ne_X _ kX hfx hfx' hfy hfy' ht hs'Y
    have hb : (b ∈ Y) := hs'Y (mem_insert b s)
    -- obtain ⟨t' : ereal, htt', ht'_lt_infi_supr⟩ :=  exists_between ht,
    let X' := {x ∈ X | f x b ≤ t}
    cases' Set.eq_empty_or_nonempty X' with X'_e X'_ne
    · -- X' = ∅,
      use b; constructor; apply hs'Y; exact mem_insert b s
      rw [← not_le]
      intro h
      rw [Set.eq_empty_iff_forall_not_mem] at X'_e 
      obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_X kX (hfy b hb)
      specialize X'_e x
      apply X'_e; simp only [Set.mem_sep_iff]
      exact ⟨hx, le_trans (by simp only [le_iInf_iff]; exact hx_le) h⟩
    -- the nonempty case
    suffices hX'X : X' ⊆ X
    suffices kX' : IsCompact X'
    have cX' : Convex ℝ X' := hfy' b hb t
    --suffices lt_of : ∀ (f g : E → ereal) (hg : lower_semicontinuous_on g X)(hf_le_g : ∀ x ∈ X, f x ≤ g x), ⨅ x ∈ X', f x  < ⨅ x ∈ X, g x,
    · specialize hrec X' X'_ne cX' kX' 
        (fun x hx' ↦ hfx x (hX'X hx'))
        (fun x hx' ↦ hfx' x (hX'X hx'))
        (fun y hy ↦ LowerSemicontinuousOn.mono (hfy y hy) hX'X)
        (fun y hy ↦ cX'.quasiconvexOn_restrict (hfy' y hy) hX'X) 
      
      suffices hlt : _
      suffices hsY : _
      specialize hrec hlt hsY

      obtain ⟨y1, hy1, hty1⟩ := hrec

      · refine' exists_lt_iInf_of_lt_iInf_of_sup X ne_X kX Y cY f hfx hfx' hfy hfy' hb hy1 _
        suffices : LowerSemicontinuousOn (fun x => f x b ⊔ f x y1) X
        obtain ⟨a, ha, hfa_eq_inf⟩ := LowerSemicontinuousOn.exists_iInf_of_isCompact ne_X kX this
        rw [← hfa_eq_inf]
        by_cases ha' : a ∈ X'
        · refine' lt_of_lt_of_le hty1 _
          refine' le_trans _ le_sup_right
          refine' (iInf₂_le_of_le a ha') (le_refl _)
        · simp only [mem_sep_iff, not_and, not_le] at ha' 
          exact lt_of_lt_of_le (ha' ha) le_sup_left
        · -- the semicontinuity
          apply LowerSemicontinuousOn.sup
          exact hfy b hb; exact hfy y1 hy1
      · apply subset_trans (subset_insert b s) hs'Y 
      · /- sinon, si  infi x ∈ X', supr y ∈ s f x y ≤ t
                pour tout t' > t, il existe x ∈ X', supr y ∈ s f x y ≤ t',
                comme x ∈ X' et t ≤ t', on  a supr y ∈ insert b s f x y  ≤ t', 
                donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t',
                donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t    
              -/
        rw [← not_le, infi₂_le_iff] at ht ⊢
        push_neg at ht ⊢
        obtain ⟨t', ht', htt'⟩ := ht
        use t'; apply And.intro _ htt'
        intro x hx
        specialize ht' x (hX'X hx)
        simp only [Set.insert_eq] at ht' 
        rw [iSup_union] at ht' 
        simp only [mem_singleton_iff, iSup_iSup_eq_left, le_sup_iff] at ht' 
        apply Or.resolve_left ht'
        rw [not_le]
        apply lt_of_le_of_lt _ htt'
        exact hx.2 
    · -- X' is compact
      suffices this : X' = Subtype.val '' (Subtype.val ⁻¹' X' : Set X)
      rw [this]; rw [inducing_subtype_val.isCompact_iff]
      haveI : CompactSpace X := isCompact_iff_compactSpace.mp kX
      apply IsClosed.isCompact
      rw [inducing_subtype_val.isClosed_iff]
      specialize hfy b hb
      rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfy 
      obtain ⟨v, hv, hv'⟩ := hfy t
      use v
      apply And.intro hv
      rw [Subtype.preimage_coe_eq_preimage_coe_iff]
      rw [← hv']
      ext x;
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_sep_iff, and_congr_left_iff, iff_and_self]
      exact fun w _ => w
      rw [Set.image_preimage_eq_inter_range]
      simp only [ge_iff_le, Subtype.range_coe_subtype, setOf_mem_eq]
      rw [Set.inter_eq_self_of_subset_left hX'X]

    · -- X' ⊆ X 
      intro x; simp only [mem_sep_iff]; exact And.left
#align ereal_sion.exists_lt_infi_of_lt_infi_of_finite ERealSion.exists_lt_iInf_of_lt_iInf_of_finite

example {a b : ℝ} : a ≤ b ↔ ∀ c : ℝ, c < a → c < b :=
  forall_lt_iff_le.symm

theorem minimax : (⨅ x ∈ X, ⨆ y ∈ Y, f x y) = ⨆ y ∈ Y, ⨅ x ∈ X, f x y := by
  apply symm
  apply le_antisymm
  -- the obvious inclusion
  · exact iSup₂_iInf₂_le_iInf₂_iSup₂ X Y f
  -- the delicate inclusion
  · rw [← forall_lt_iff_le]
    intro t ht
    let X' (y : F) := ({x ∈ X | f x y ≤ t} : Set E)
     
    suffices hs : ∃ s : Set F, s ⊆ Y ∧ s.Finite ∧ (⨅ y ∈ s, X' y) = ∅
    obtain ⟨s, hsY, hs, hes⟩ := hs
    suffices hst : t < ⨅ (x ∈ X), ⨆ (y ∈ s), f x y
    obtain ⟨y0, hy0, ht0⟩ :=
      exists_lt_iInf_of_lt_iInf_of_finite X ne_X cX kX Y f hfx hfx' hfy hfy' hs hst hsY
    apply lt_of_lt_of_le ht0
    apply le_iSup₂_of_le y0 hy0 (le_refl _)
    · -- hst
      suffices hlsc : LowerSemicontinuousOn (fun x => ⨆ y ∈ s, f x y) X
      obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_iInf_of_isCompact ne_X kX hlsc
      rw [← ha']; dsimp
      rw [← not_le]
      rw [iSup₂_le_iff]
      intro hes'
      rw [Set.eq_empty_iff_forall_not_mem] at hes 
      apply hes a
      simp only [ge_iff_le, iInf_eq_iInter, mem_iInter, mem_setOf_eq]
      intro y hy
      exact ⟨ha, hes' y hy⟩
      apply lowerSemicontinuousOn_supr₂ hs fun i hi => hfy i (hsY hi)
    · suffices hfyt : ∀ y : Y, ∃ vy : Set E, IsClosed vy ∧ X' y = vy ∩ X
      let v : Y → Set E := fun y ↦ Exists.choose (hfyt y)
      have hv : ∀ y, IsClosed (v y) ∧ X' y = v y ∩ X := fun y ↦ (hfyt y).choose_spec
      suffices hsZ : _
      obtain ⟨s, hs⟩ := 
        kX.elim_finite_subfamily_closed v (fun y => (hv y).1) hsZ
      have hs_ne : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro hs_e
        simp only [hs_e, Finset.not_mem_empty, iInter_of_empty, iInter_univ, inter_univ] at hs
        rw [Set.nonempty_iff_ne_empty] at ne_X ; exact ne_X hs
      use (Subtype.val : Y → F) '' ↑s
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
            apply Set.inter_subset_left _ X
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
        suffices : x ∈ X' y
        exact this.2
        rw [(hv ⟨y, hy⟩).2]
        constructor
        · exact hx.2 ⟨y, hy⟩
        · exact hx.1
      · -- hfyt
        rintro ⟨y, hy⟩
        specialize hfy y hy
        simp_rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfy 
        obtain ⟨v, v_closed, hv⟩ := hfy t
        use v; apply And.intro v_closed
        rw [← hv]
        ext x; simp only [Subtype.coe_mk, mem_sep_iff, mem_inter_iff, mem_preimage, mem_Iic];
        rw [and_comm]
#align ereal_sion.minimax ERealSion.minimax

/-- The Sion-von Neumann minimax theorem (saddle point form) -/
theorem exists_saddlePointOn :
  ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  suffices hlsc : LowerSemicontinuousOn (fun x => ⨆ y ∈ Y, f x y) X
  obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_iInf_of_isCompact ne_X kX hlsc
  use a
  use ha
  suffices husc : UpperSemicontinuousOn (fun y => ⨅ x ∈ X, f x y) Y
  obtain ⟨b, hb, hb'⟩ := UpperSemicontinuousOn.exists_iSup_of_isCompact ne_Y kY husc
  use b 
  use hb
  rw [isSaddlePointOn_iff' ha hb]
  rw [ha']
  rw [minimax X ne_X cX kX Y f hfx hfx' hfy hfy']
  rw [← hb']
  · -- hlsc
    intro y hy
    apply upperSemicontinuousWithinAt_iInf₂ ne_X kX _ (hfy y hy)
    intro x hx; exact hfx x hx y hy
  · -- husc
    intro x hx
    apply lowerSemicontinuousWithinAt_iSup₂ ne_Y kY _ (hfx x hx)
    intro y hy; exact hfy y hy x hx


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

-- TODO : start from a LinearOrder, DenselyOrdered and add with_top, with_bot
-- Problem : not Densely Ordered if it has min or sup…

example : Monotone (Real.toEReal) := EReal.coe_strictMono.monotone

example : Continuous (Real.toEReal) := by exact continuous_coe_real_ereal

/- Here, one will need compactness on Y — otherwise, no hope that
the saddle point exists… -/
/-- The minimax theorem, in the saddle point form -/
theorem existsSaddlePointOn :
  ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  -- Reduce to the cae of EReal-valued functions
  let φ : E → F → EReal := fun x y ↦ (f x y)
  -- suffices : ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y φ a b
  suffices hφx : ∀ x ∈ X, UpperSemicontinuousOn (fun y ↦ φ x y) Y 
  suffices hφx' : ∀ (x : E), x ∈ X → QuasiconcaveOn ℝ Y fun y ↦ φ x y
  suffices hφy : ∀ (y : F), y ∈ Y → LowerSemicontinuousOn (fun x ↦ φ x y) X
  suffices hφy': ∀ (y : F), y ∈ Y → QuasiconvexOn ℝ X fun x ↦ φ x y
  obtain ⟨a, ha, b, hb, hab⟩ := 
    ERealSion.exists_saddlePointOn X ne_X cX kX Y ne_Y kY φ hφx hφx' hφy hφy'
  use a
  use ha
  use b
  use hb
  intro x hx y hy
  simp only [← EReal.coe_le_coe_iff]
  exact hab x hx y hy
  · -- hφy'
    intro y hy
    convert (hfy' y hy).monotone_comp EReal.coe_strictMono.monotone
  · -- hφy
    intro y hy
    exact continuous_coe_real_ereal.comp_lowerSemicontinuousOn (hfy y hy) EReal.coe_strictMono.monotone
  · -- hφx'
    intro x hx
    convert (hfx' x hx).monotone_comp EReal.coe_strictMono.monotone
  · -- hφy'
    intro x hx
    exact continuous_coe_real_ereal.comp_upperSemicontinuousOn (hfx x hx) EReal.coe_strictMono.monotone

end Sion

end Real

