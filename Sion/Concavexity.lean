import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Topology.Semicontinuous
import Mathlib.Data.Real.EReal

open Set

section Restriction

variable {𝕜 E β : Type _} [OrderedSemiring 𝕜] [AddCommMonoid E] [OrderedAddCommMonoid β] [SMul 𝕜 E]

variable {s : Set E} {f : E → β}

theorem Set.sep_of_subset {α : Type _} {s t : Set α} {p : α → Prop} (hst : s ⊆ t) :
    {x ∈ s | p x} = {x ∈ t | p x} ∩ s := by
  ext x; simp only [mem_sep_iff, mem_inter_iff]
  rw [and_assoc, and_comm]
  simp only [iff_and_self, and_imp]
  exact fun _ h' => hst h'
#align set.sep_of_subset Set.sep_of_subset

theorem Convex.quasiconvexOn_restrict {t : Set E} (hf : QuasiconvexOn 𝕜 s f) (hst : t ⊆ s)
    (ht : Convex 𝕜 t) : QuasiconvexOn 𝕜 t f :=
  by
  intro b
  rw [Set.sep_of_subset hst]
  exact Convex.inter (hf b) ht
#align convex.quasiconvex_on_restrict Convex.quasiconvexOn_restrict

theorem Convex.quasiconcaveOn_restrict {t : Set E} (hf : QuasiconcaveOn 𝕜 s f) (hst : t ⊆ s)
    (ht : Convex 𝕜 t) : QuasiconcaveOn 𝕜 t f :=
  by
  intro b
  rw [Set.sep_of_subset hst]
  exact Convex.inter (hf b) ht
#align convex.quasiconcave_on_restrict Convex.quasiconcaveOn_restrict

end Restriction

section Quasiconcave

/- We prove that a lsc quasiconcave function on a nonempty compact convex set 
is bounded above and attains its upper bound. 

Maybe the result is false, I don't know. 

-/
variable {E : Type _} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousSMul ℝ E]

variable {f : E → EReal}

/-- A quasiconcave and lower semicontinuous function attains 
  its upper bound on a nonempty compact set -/
theorem IsCompact.exists_forall_ge_of_quasiconcave {s : Set E} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hfs : LowerSemicontinuousOn f s) (hfc : QuasiconcaveOn ℝ s f) :
    ∃ a ∈ s, ∀ x ∈ s, f x ≤ f a :=
  sorry
#align is_compact.exists_forall_ge_of_quasiconcave IsCompact.exists_forall_ge_of_quasiconcave

/- 
let T = sup f x, for x ∈ s, 
assume f does not attain its upper bound
consider the sets  U t := f ⁻¹' (set.Ici t), for t < T.
Since f is lower semicontinuous, U t is closed

-/
/-- A quasiconcave and lower semicontinuous function is bounded above on a compact set -/
theorem BddAboveOn.isCompact_of_quasiconcave {s : Set E} (hs : IsCompact s)
    (hfs : LowerSemicontinuousOn f s) (hfc : QuasiconcaveOn ℝ s f) : BddAbove (f '' s) :=
  by
  cases' s.eq_empty_or_nonempty with e_s ne_s
  · rw [e_s]; simp only [Set.image_empty, bddAbove_empty]
  · obtain ⟨a, _, hax⟩ := IsCompact.exists_forall_ge_of_quasiconcave ne_s hs hfs hfc
    use f a; rintro t ⟨x, hx, rfl⟩; exact hax x hx
#align bdd_above_on.is_compact_of_quasiconcave BddAboveOn.isCompact_of_quasiconcave


theorem QuasiconcaveOn.isPreconnected_preimage {s : Set E} {t : EReal}
    (hfc : QuasiconcaveOn ℝ s f) : IsPreconnected (f ∘ (fun x ↦ ↑x) ⁻¹' Ici t : Set s) :=
  by
  rw [preimage_comp, ← inducing_subtype_val.isPreconnected_image, image_preimage_eq_inter_range,
    Subtype.range_coe, inter_comm]
  exact (hfc t).isPreconnected
#align quasiconcave_on.is_preconnected_preimage QuasiconcaveOn.isPreconnected_preimage

end Quasiconcave

section Quasiconvex

/- We prove that a usc quasiconvex function on a nonempty compact convex set 
is bounded below and attains its lower bound. 

Maybe the result is false, I don't know. 

-/
variable {E : Type _} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousSMul ℝ E]

variable {f : E → EReal}

/--
A quasiconvex and upper semicontinuous function attains its lower bound on a nonempty compact set -/
theorem IsCompact.exists_forall_le_of_quasiconvex {s : Set E} (ne_s : s.Nonempty) (hs : IsCompact s)
    (hfs : UpperSemicontinuousOn f s) (hfc : QuasiconvexOn ℝ s f) : ∃ a ∈ s, ∀ x ∈ s, f a ≤ f x :=
  sorry
#align is_compact.exists_forall_le_of_quasiconvex IsCompact.exists_forall_le_of_quasiconvex

/-- A quasiconvex and upper semicontinuous function is bounded below on a compact set -/
theorem BddBelowOn.isCompact_of_quasiconvex {s : Set E} (hs : IsCompact s)
    (hfs : UpperSemicontinuousOn f s) (hfc : QuasiconvexOn ℝ s f) : BddBelow (f '' s) :=
  by
  cases' s.eq_empty_or_nonempty with e_s ne_s
  · rw [e_s]; simp only [Set.image_empty, bddBelow_empty]
  · obtain ⟨a, _, hax⟩ := IsCompact.exists_forall_le_of_quasiconvex ne_s hs hfs hfc
    use f a; rintro t ⟨x, hx, rfl⟩; exact hax x hx
#align bdd_below_on.is_compact_of_quasiconvex BddBelowOn.isCompact_of_quasiconvex

theorem QuasiconvexOn.isPreconnected_preimage {s : Set E} {t : EReal} (hfc : QuasiconvexOn ℝ s f) :
    IsPreconnected (f ∘ (fun x ↦ ↑x) ⁻¹' Iic t : Set s) :=
  by
  rw [preimage_comp, ← inducing_subtype_val.isPreconnected_image, image_preimage_eq_inter_range,
    Subtype.range_coe, inter_comm]
  exact (hfc t).isPreconnected
#align quasiconvex_on.is_preconnected_preimage QuasiconvexOn.isPreconnected_preimage

end Quasiconvex

