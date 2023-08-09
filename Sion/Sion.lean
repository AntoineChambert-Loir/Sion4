-- import Mathlib.Topology.Instances.Ereal
import Mathlib.Data.Real.Ereal

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

variable {E : Type _} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousSMul ℝ E]

variable {F : Type _} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [TopologicalAddGroup F]
  [ContinuousSMul ℝ F]

variable (X : Set E) (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)

variable (Y : Set F) (ne_Y : Y.Nonempty) (cY : Convex ℝ Y)

def IsSaddlePointOn {β : Type _} [Preorder β] (f : E → F → β) {a : E} (_ : a ∈ X) {b : F}
    (_ : b ∈ Y) :=
  (∀ x ∈ X, f a b ≤ f x b) ∧ ∀ y ∈ Y, f a y ≤ f a b
#align is_saddle_point_on IsSaddlePointOn

section EReal

namespace ErealSion

variable (f : E → F → EReal)

/-- The trivial minimax inequality -/
theorem supr₂_infi₂_le_infi₂_supr₂ : (⨆ y ∈ Y, ⨅ x ∈ X, f x y) ≤ ⨅ x ∈ X, ⨆ y ∈ Y, f x y :=
  by
  rw [iSup₂_le_iff]; intro y hy
  rw [le_iInf₂_iff]; intro x hx
  exact iInf₂_le_of_le x hx (le_iSup₂_of_le y hy (le_refl _))
#align ereal_sion.supr₂_infi₂_le_infi₂_supr₂ ErealSion.supr₂_infi₂_le_infi₂_supr₂

variable (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

variable (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
  (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

-- Question pour Antoine : Y-a-t-il une raison pour utiliser `⨅ (x : X), foo x` au lieu de `⨅ x ∈ X, foo x`
-- (le deuxième évite des coercions) ? Dans `ℝ` ce sera important de faire la distinction parce 
-- que ça ne donne pas le même résultat (`⨅ x ∈ X, foo x` devient `⨅ (x : E), ⨅ (hx : x ∈ X), foo x` et
-- l'inf sur l'ensemble vide ne donne rien sur `ℝ`), mais autant profiter à fond de `ereal`, non ?
-- Réponse : a priori, aucune, je ne sais même pas pourquoi j'entre l'une et pas l'autre. 
-- Question : quelle est la différence dans ℝ ?
-- (à part que l'inf sur l'ensemble vide est alors 0 et pas + infini !)
---- TODO: trouver un meilleur nom :)
---- penser `p := C t z ⊆ A`, `p' := C t' z ⊆ A`, `q := C t z ⊆ B`, `q' := C t' z ⊆ B`
--lemma logic_lemma {p p' q q' : Prop} (hp : p' → p) (hq : q' → q) (h : xor p' q')
theorem exists_lt_iInf_of_lt_iInf_of_sup {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y) {t : EReal}
    (ht : t < ⨅ x ∈ X, f x y1 ⊔ f x y2) : ∃ y0 ∈ Y, t < ⨅ x ∈ X, f x y0 :=
  by
  by_contra' hinfi_le
  obtain ⟨t' : EReal, htt' : t < t', ht' : t' < ⨅ x ∈ X, f x y1 ⊔ f x y2⟩ := exists_between ht
  let C : EReal → F → Set X := 
    fun u z => (fun x => f x z) ∘ (fun x ↦ ↑x)⁻¹' Iic u
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
  have hC_closed : ∀ u, ∀ {z}, z ∈ Y → IsClosed (C u z) :=
    by
    intro u z hz 
    specialize hfy z hz
    rw [lowerSemicontinuousOn_iff_restrict] at hfy 
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy 
    exact hfy u
  have hC_preconnected : ∀ u, ∀ {z}, z ∈ Y → IsPreconnected (C u z) :=
    by
    intro u z hz
    exact (hfy' z hz).isPreconnected_preimage
  have hC_disj : Disjoint (C t' y1) (C t' y2) :=
    by
    --  from set.disjoint_iff.mpr (λ x hx, not_lt_of_le (infi_le_of_le x $ sup_le_iff.mpr hx) ht'),
    -- marchait avant que je change en ⨅ x ∈ X……
    refine' Set.disjoint_iff.mpr fun (x : X) hx => not_lt_of_le (iInf₂_le_of_le (x : E) _ _) ht'
    · exact x.2
    · exact sup_le_iff.mpr hx
  have hC_subset : ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∪ C t' y2 :=
    by
    intro z hz x hx
    simp only [Set.mem_union, mem_C_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y1 ⊓ f x y2)
    rw [convex_iff_segment_subset] at hfx' 
    specialize hfx' ⟨hy1, inf_le_left⟩ ⟨hy2, inf_le_right⟩ hz
    exact le_trans hfx'.2 hx
  have hC_subset_or : ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∨ C t' z ⊆ C t' y2 :=
    by
    intro z hz
    apply
      isPreconnected_iff_subset_of_disjoint_closed.mp
        (hC_preconnected _ (cY.segment_subset hy1 hy2 hz)) _ _ (hC_closed _ hy1) (hC_closed _ hy2)
        (hC_subset _ hz)
    rw [Set.disjoint_iff_inter_eq_empty.mp hC_disj, Set.inter_empty]
  --have hC_subset_xor : ∀ z ∈ segment ℝ y1 y2, xor (C t' z ⊆ C t' y1) (C t' z ⊆ C t' y2), 
  --{ sorry },
  have segment_subset : segment ℝ y1 y2 ⊆ Y := convex_iff_segment_subset.mp cY hy1 hy2
  let J1 := {z : segment ℝ y1 y2 | C t z ⊆ C t' y1}
  -- do we really need this ? (I can't do without it)
  have mem_J1_iff : ∀ z : segment ℝ y1 y2, z ∈ J1 ↔ C t z ⊆ C t' y1 := by intro z; rfl
  have hJ1_closed : IsClosed J1 := by
    rw [isClosed_iff_clusterPt]
    -- Let `y` be a cluster point of `J1`, let's show it's in `J1`, i.e `C t y ⊆ C t' y1`.
    -- Let `x ∈ C t y`, and let's find some `z ∈ J1` such that `x ∈ C t z ⊆ C t' y1`.
    intro y h x hx
    replace hfx : UpperSemicontinuous fun y' : segment ℝ y1 y2 => f x y'
    · rw [← upperSemicontinuousOn_univ_iff]
      apply (hfx x x.2).comp continuous_subtype_val.continuousOn 
        (fun y' _ => segment_subset y'.2)
    suffices : ∃ z ∈ J1, x ∈ C t' (z : F)
    obtain ⟨z, hz, hxz⟩ := this
    suffices : C t' z ⊆ C t' y1
    exact this hxz
    apply Or.resolve_right (hC_subset_or z z.2)
    intro hz2
    apply Set.Nonempty.not_subset_empty (hC_ne z (segment_subset z.2))
    rw [← disjoint_iff_inter_eq_empty.mp hC_disj]
    apply Set.subset_inter hz
    exact subset_trans (hC t t' z (le_of_lt htt')) hz2
    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [UpperSemicontinuous, UpperSemicontinuousAt] at hfx 
    specialize hfx y t' (lt_of_le_of_lt hx htt')
    rw [clusterPt_principal_iff_frequently] at h 
    suffices this : ∀ᶠ z : segment ℝ y1 y2 in nhds y, z ∈ J1 → x ∈ C t' z ∧ z ∈ J1
    obtain ⟨z, hxz, hxz'⟩ := Filter.Frequently.exists (Filter.Frequently.mp h this)
    exact ⟨z, ⟨hxz', hxz⟩⟩
    · -- this
      apply Filter.Eventually.mp hfx
      apply Filter.eventually_of_forall
      intro z hzt'
      rintro hz
      exact ⟨le_of_lt hzt', hz⟩
  have hJ1_closed : IsClosed J1 := by
    rw [isClosed_iff_clusterPt]
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
    rw [← Set.top_eq_univ]; rw [eq_top_iff]; intro z hz
    rw [Set.mem_union]; rw [mem_J1_iff]; rw [mem_J2_iff]
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
#align ereal_sion.exists_lt_infi_of_lt_infi_of_sup ErealSion.exists_lt_iInf_of_lt_iInf_of_sup

/- lemma exists_lt_infi_of_lt_infi_of_finite {s : set F} (hs : s.finite) {t : ℝ} (ht : (t : ereal) < infi (λ x : X, supr (λ y : s, f x y))) :
  s ⊆ Y → ∃ y0 ∈ Y,  (t : ereal) < infi (λ x : X, f x y0) :=
begin
  revert X, 
--  
--  revert ht,
  apply hs.induction_on, 
  { -- empty case 
    intros X ne_X cX kX hfx hfx' hfy hfy', 
    haveI : nonempty X := nonempty.coe_sort ne_X,  
    simp only [csupr_of_empty, cinfi_const, not_lt_bot, is_empty.forall_iff], },

  intros b s has hs hrec X ne_X cX kX hfx hfx' hfy hfy' ht hs'Y, 
  have hb : b ∈ Y := hs'Y (mem_insert b s), 
  -- obtain ⟨t' : ereal, htt', ht'_lt_infi_supr⟩ :=  exists_between ht, 
  let X' := { x ∈ X | f x b ≤ t },
  cases set.eq_empty_or_nonempty X' with X'_e X'_ne,
  { -- X' = ∅, 
    use b, split, apply hs'Y, exact mem_insert b s,

/-    apply lt_of_lt_of_le htt',  
  rw le_infi_iff,
    
    rintro ⟨x, hx⟩,
    suffices : x ∉ X', 
    simp only [mem_sep_iff, not_and, not_le] at this,
    exact le_of_lt (this hx), 
    rw X'_e, exact not_mem_empty x, -/
  
    -- version d'avant, lorsqu'on avait t'=t
    rw ← not_le,
    intro h, 
    rw set.eq_empty_iff_forall_not_mem  at X'_e,
    
    obtain ⟨x, hx, hx_le⟩ := lower_semicontinuous.exists_forall_le_of_is_compact ne_X kX (hfy b hb), 
    specialize X'_e x, 
    apply X'_e, simp only [set.mem_sep_iff], 
    apply and.intro hx, 
    refine le_trans _ h,
    rw le_infi_iff, 
    rintro ⟨x, hx⟩, exact hx_le x hx, },
  
  suffices kX' : is_compact X',
  suffices cX' : convex ℝ X', 
  suffices hX'X : X' ⊆ X, 
  suffices lt_of : ∀ (f g : E → ereal) (hg : lower_semicontinuous_on g X)
    (hf_le_g : ∀ x ∈ X, f x ≤ g x), ⨅ x ∈ X', f x  < ⨅ x ∈ X, g x, 

  { 
    specialize hrec X' X'_ne cX' kX', 
    obtain ⟨y1, hy1, hty1⟩ := hrec _ _ _ _ _ _,
    { refine exists_lt_infi_of_lt_infi_of_two X ne_X cX kX Y cY f hfx hfx' hfy hfy' hb hy1 _, 

      suffices : lower_semicontinuous_on (λ x, f x b ⊔ f x y1) X,
      obtain ⟨a, ha, hfa_le⟩ := lower_semicontinuous.exists_forall_le_of_is_compact ne_X kX this,
      suffices : infi (λ x : X, f x b ⊔ f x y1) = f a b ⊔ f a y1,
      rw this,
      by_cases ha' : a ∈ X',
      { refine lt_of_lt_of_le hty1 _, 
        refine le_trans _ (le_sup_right),
        refine infi_le _ (⟨a, ha'⟩ : X'), },
      { simp only [mem_sep_iff, not_and, not_le] at ha', 
        exact lt_of_lt_of_le (ha' ha) (le_sup_left), },
      
      { apply le_antisymm, 
        apply infi_le _ (⟨a, ha⟩ : X),
        rw le_infi_iff, rintros ⟨x, hx⟩, exact hfa_le x hx, },
      { apply lower_semicontinuous_on_sup, 
        exact hfy b hb, exact hfy y1 hy1, }, },
    { intros x hx', exact hfx x (hX'X hx'), },
    { intros x hx', exact hfx' x (hX'X hx'), },
    { intros y hy, apply lower_semicontinuous_on.mono (hfy y hy) hX'X, },
    { intros y hy, exact cX'.quasiconvex_on_restrict (hfy' y hy) hX'X, },
    { suffices : lower_semicontinuous_on (λ x, ⨆ y ∈ s, f x y) X',
      obtain ⟨a, ha, hfa_le⟩:= lower_semicontinuous.exists_infi_of_is_compact X'_ne kX' this,

    sorry,
    sorry, },
    { apply subset.trans (subset_insert b s) hs'Y, }, },
  sorry, -- peut-être à virer
  { intros x, simp only [mem_sep_iff], exact and.elim_left, },

  { sorry, },
  { sorry, },
end
 -/
theorem exists_lt_iInf_of_lt_iInf_of_finite {s : Set F} (hs : s.Finite) {t : EReal}
    (ht : t < ⨅ x ∈ X, ⨆ y ∈ s, f x y) : s ⊆ Y → ∃ y0 ∈ Y, t < ⨅ x ∈ X, f x y0 :=
  by
  revert X
  --  
  --  revert ht,
  refine' Set.Finite.induction_on hs _ _
  · -- empty case
    intro X ne_X cX kX hfx hfx' hfy hfy'
    haveI : Nonempty X := nonempty_coe_sort.mpr ne_X
    -- intro ht, exfalso,
    simp only [biInf_const ne_X, mem_empty_iff_false, ciSup_false, ciSup_const, not_lt_bot,
      IsEmpty.forall_iff]
  intro b s has hs hrec X ne_X cX kX hfx hfx' hfy hfy' ht hs'Y
  have hb : b ∈ Y := hs'Y (mem_insert b s)
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
  suffices hX'X : X' ⊆ X
  suffices kX' : IsCompact X'
  have cX' : Convex ℝ X' := hfy' b hb t
  --suffices lt_of : ∀ (f g : E → ereal) (hg : lower_semicontinuous_on g X)(hf_le_g : ∀ x ∈ X, f x ≤ g x), ⨅ x ∈ X', f x  < ⨅ x ∈ X, g x,
  · specialize hrec X' X'_ne cX' kX'
    obtain ⟨y1, hy1, hty1⟩ := hrec _ _ _ _ _ _
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
      · apply LowerSemicontinuousOn.sup
        exact hfy b hb; exact hfy y1 hy1
    -- · intro x hx'; exact hfx x (hX'X hx')
    -- · intro x hx'; exact hfx' x (hX'X hx')
    -- · intro y hy; apply LowerSemicontinuousOn.mono (hfy y hy) hX'X
    -- · intro y hy; exact cX'.quasiconvex_on_restrict (hfy' y hy) hX'X
    /- · /- sinon, si  infi x ∈ X', supr y ∈ s f x y ≤ t
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
      exact hx.2 -/
--    · apply subset.trans (subset_insert b s) hs'Y 
  · suffices this : X' = Subtype.val '' (Subtype.val ⁻¹' X' : Set X)
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
    exact fun w z => w
    rw [Set.image_preimage_eq_inter_range]
    simp only [ge_iff_le, Subtype.range_coe_subtype, setOf_mem_eq]
    rw [Set.inter_eq_self_of_subset_left hX'X]
  · intro x; simp only [mem_sep_iff]; exact And.left
#align ereal_sion.exists_lt_infi_of_lt_infi_of_finite ErealSion.exists_lt_iInf_of_lt_iInf_of_finite

example {a b : ℝ} : a ≤ b ↔ ∀ c : ℝ, c < a → c < b :=
  forall_lt_iff_le.symm

theorem minimax : (⨅ x ∈ X, ⨆ y ∈ Y, f x y) = ⨆ y ∈ Y, ⨅ x ∈ X, f x y := by
  apply symm
  apply le_antisymm
  -- the obvious inclusion
  · exact supr₂_infi₂_le_infi₂_supr₂ X Y f
  -- the delicate inclusion
  · rw [← forall_lt_iff_le]
    intro t ht
    let X' (y : F) := ({x ∈ X | f x y ≤ t} : Set E)
     
  -- have hX' : ∀ y, X' y = {x ∈ X | f x y ≤ t}
    --   suffices kX' : ∀ y ∈ Y, is_compact (X' y),
    suffices hs : ∃ s : Set F, s ⊆ Y ∧ s.Finite ∧ (⨅ y ∈ s, X' y) = ∅
    obtain ⟨s, hsY, hs, hes⟩ := hs
    suffices hst : t < ⨅ (x : E) (H : x ∈ X), ⨆ (y : F) (H : y ∈ s), f x y
    obtain ⟨y0, hy0, ht0⟩ :=
      exists_lt_iInf_of_lt_iInf_of_finite X Y f hs hst hsY
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
      obtain ⟨s, hs⟩ := 
        kX.elim_finite_subfamily_closed v (fun y => (hfyt y).choose_spec.1) _
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
          simp only [iInter_coe_set, mem_inter_iff, mem_iInter]
          constructor
          · obtain ⟨⟨j, hj⟩, hjs⟩ := hs_ne
            exact (hx j hj hjs).1
          · intro y hy hy'
            apply Set.inter_subset_left
            rw [← (hfyt (⟨y, hy⟩ : Y)).choose_spec.2]
            simp only [Subtype.coe_mk, mem_sep_iff]
            exact hx y hy hy'
      · rintro ⟨y, hy⟩
        specialize hfy y hy
        simp_rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfy 
        obtain ⟨v, v_closed, hv⟩ := hfy t
        use v; apply And.intro v_closed
        rw [← hv]
        ext x; simp only [Subtype.coe_mk, mem_sep_iff, mem_inter_iff, mem_preimage, mem_Iic];
        rw [and_comm]

    /-  · rw [← not_le] at ht 
        rw [Set.eq_empty_iff_forall_not_mem]
        intro x hx
        simp only [infi_eq_Inter, mem_Inter, mem_sep_iff] at hx 
        apply ht
        apply iInf₂_le_of_le x _ _
        suffices : Y.nonempty
        obtain ⟨j, hj⟩ := this
        exact (hx j hj).1
        rw [Set.nonempty_iff_ne_empty]; intro hY_e
        apply ht; rw [hY_e]; simp only [mem_empty_iff_false, ciSup_false, ciSup_const]
        obtain ⟨i, hi⟩ := ne_X
        apply iInf₂_le_of_le i hi _; exact bot_le
        rw [iSup₂_le_iff]; exact fun i hi => (hx i hi).2 
      · suffices eX' : (⨅ y ∈ Y, X' y) = ∅
        -- eX' : intersection de fermés du compact X est vide

        · simp [Set.eq_empty_iff_forall_not_mem] at eX' 
          -- rw [Set.eq_empty_iff_forall_not_mem] at eX' ⊢
          intro x hx
          simp only [Subtype.coe_mk, mem_inter_iff] at hx 
          apply eX' x
          simp only [infi_eq_Inter, mem_Inter]
          intro y hy
          rw [← Subtype.coe_mk y hy]
          rw [(hfyt (⟨y, hy⟩ : Y)).choose_spec.2]
          apply And.intro _ hx.1
          apply Inter_subset fun i => Exists.choose (hfyt i)
          exact hx.2 
        -/
  
#align ereal_sion.minimax ErealSion.minimax

end ErealSion

end EReal

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
theorem minimax :
    (iInf fun x : X => iSup fun y : Y => f x y) = iSup fun y : Y => iInf fun x : X => f x y :=
  sorry
#align sion.minimax Sion.minimax

/- Here, one will need compactness on Y — otherwise, no hope that
the saddle point exists… -/
/-- The minimax theorem, in the saddle point form -/
theorem exists_saddle_point :
    ∃ (a : E) (ha : a ∈ X) (b : F) (hb : b ∈ Y), IsSaddlePointOn X Y f ha hb :=
  sorry
#align sion.exists_saddle_point Sion.exists_saddle_point

-- include ne_X ne_Y cX cY kX
/- There are some `sorry` 
*  we need to add the proofs that relevant functions are bounded on X Y 
* We also need to add the proofs that forall `infi` and `supr` appearing in the statement, the corresponding function is indeed bounded from below / from above -/
/-- The minimax theorem, in the inf-sup equals sup-inf form -/
theorem minimax' :
    (iInf fun x : X => iSup fun y : Y => f x y) = iSup fun y : Y => iInf fun x : X => f x y :=
  by
  haveI : Nonempty X := ne_X.coe_sort
  haveI : Nonempty Y := ne_Y.coe_sort
  /- 
    obtain ⟨m, hm⟩ := sion.is_bdd_below X ne_X cX kX Y ne_Y cY f hfx hfx' hfy hfy',
    obtain ⟨M, hM⟩ := sion.is_bdd_above X ne_X cX kX Y ne_Y cY f hfx hfx' hfy hfy',
    simp only [lower_bounds, upper_bounds, set.mem_range, prod.exists, set_coe.exists, subtype.coe_mk, exists_prop,
    forall_exists_index, and_imp, set.mem_set_of_eq] at hm hM,
    -/
  apply le_antisymm
  · obtain ⟨a, ha, b, hb, hax, hby⟩ :=
      Sion.exists_saddle_point X ne_X cX kX Y ne_Y cY f hfx hfx' hfy hfy'
    suffices : f a b ≤ iSup fun y : Y => iInf fun x : X => f x y
    apply le_trans _ this
    refine' le_trans (ciInf_le _ (⟨a, ha⟩ : X)) _
    -- bdd_below is not automatic :-(
    sorry
    apply ciSup_le
    rintro ⟨y, hy⟩; exact hby y hy
    · refine' le_trans _ (le_ciSup _ (⟨b, hb⟩ : Y))
      apply le_ciInf
      rintro ⟨x, hx⟩; exact hax x hx
      -- bdd_above is not automatic :-(
      sorry
  · -- This is the trivial inequality
    -- except that we need to check that some stuff is bounded
    apply ciSup_le; rintro ⟨y, hy⟩
    apply le_ciInf; rintro ⟨x, hx⟩
    refine' le_trans (ciInf_le _ (⟨x, hx⟩ : X)) _
    sorry
    -- bdd_below is not automatic
    --    rw subtype.coe_mk,
    refine' @le_ciSup _ _ _ (fun t : Y => f x t) _ (⟨y, hy⟩ : Y)
    sorry
#align sion.minimax' Sion.minimax'

-- bdd_above is not automatic
end Sion

end Real

