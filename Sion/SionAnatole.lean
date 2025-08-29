import Mathlib.Topology.Instances.EReal
import Mathlib.Data.Real.EReal
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Semicontinuous

import Sion.SemicontinuousClean
import Sion.ForMathlib.Misc

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

open Topology Set

section Logic

-- not needed actually
lemma xor_iff_or_and_not_and {p q : Prop} : Xor' p q ↔ (p ∨ q) ∧ ¬(p ∧ q) := by
  rw [Xor']
  aesop

lemma Or.iff_of_imp_of_not_and {p p' q q' : Prop} (hpq : p ∨ q) (hpq' : ¬(p' ∧ q')) (hp : p → p') (hq : q → q') :
    (p ↔ p') ∧ (q ↔ q') := by
  aesop

end Logic

section Order

lemma forall_lt_le_iff_le {α : Type*} [LinearOrder α] [DenselyOrdered α] {a b : α} :
    (∀ c, a < c → b ≤ c) ↔ b ≤ a := by
  refine ⟨fun H ↦ ?_, fun hba _ hac ↦ hba.trans hac.le⟩
  by_contra! hab
  exact (exists_between hab).elim fun c ⟨hac, hcb⟩ ↦ not_le_of_gt hcb (H c hac)

end Order

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousSMul ℝ E]

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [TopologicalAddGroup F]
  [ContinuousSMul ℝ F]

variable {X : Set E} {Y : Set F}

variable {X : Set E} (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)

variable {Y : Set F} (ne_Y : Y.Nonempty) (cY : Convex ℝ Y) (kY : IsCompact Y)

variable {β : Type*} [LinearOrder β] {f : E → F → β}

variable (hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y (f x ·))

variable (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (f · y) X)
  (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X (f · y))

include hfx hfx' hfy hfy' cY in
theorem lemma0 {y₁ y₂ : F} (y₁_in : y₁ ∈ Y) (y₂_in : y₂ ∈ Y) {a b : β} (a_lt_b : a < b)
    (H : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ a) :
    ∃ x ∈ X, max (f x y₁) (f x y₂) ≤ b := by
  -- We only care about the subset `[y₁, y₂]` of `Y`, so we restrict some of our hypotheses
  -- for convenience
  set S : Set F := segment ℝ y₁ y₂
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace (convex_segment _ _ |>.isPreconnected)
  replace cY : S ⊆ Y := cY.segment_subset y₁_in y₂_in
  replace hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) S := fun x hx ↦ (hfx x hx).mono cY

  simp_rw [upperSemicontinuousOn_iff_restrict] at hfx
  simp_rw [lowerSemicontinuousOn_iff_restrict] at hfy

  set C : β → F → Set X := fun c y ↦ {x | f x y ≤ c}
  set D : β → F → Set X := fun c y ↦ {x | f x y < c}

  -- Start by some obvious observations on `C` and `D`
  have C_closed : ∀ c : β, ∀ y ∈ Y, IsClosed (C c y) :=
    fun c y hy ↦ hfy y hy |>.isClosed_preimage _
  have C_mono : ∀ y, Monotone (C · y) := fun y _ _ hle _ h ↦ le_trans h hle
  have CD_subset : ∀ y, C a y ⊆ D b y := fun y _ h ↦ h.trans_lt a_lt_b
  have DC_subset : ∀ y, D b y ⊆ C b y := fun y _ h ↦ h.le
  have C_preconnected : ∀ c, ∀ y ∈ Y, IsPreconnected (C c y) := fun c y hy ↦ by
    change IsPreconnected (Subtype.val ⁻¹' {x : E | f x y ≤ c})
    simp_rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_val]
    exact hfy' y hy c |>.isPreconnected

  -- Now, reformulate the goal as `C b y₁ ∩ C b y₂ ≠ ∅` and `H` as `∀ y ∈ Y, C a y = ∅`.
  suffices (C b y₁ ∩ C b y₂).Nonempty from
    this.elim fun x ⟨hxy₁, hxy₂⟩ ↦ ⟨x, x.2, sup_le hxy₁ hxy₂⟩
  replace H : ∀ y ∈ Y, (C a y).Nonempty :=
    fun y hy ↦ (H y hy).elim fun x ⟨x_in, hx⟩ ↦ ⟨⟨x, x_in⟩, hx⟩
  -- By contradiction, assume `C b y₁ ∩ C b y₂ = ∅`.
  by_contra!

  have C_cover_S : ∀ y ∈ S, C b y ⊆ C b y₁ ∪ C b y₂ := by
    rintro - ⟨u, v, hu, hv, huv, rfl⟩ x hx
    change f x y₁ ≤ b ∨ f x y₂ ≤ b
    rw [← min_le_iff]
    exact quasiconcaveOn_iff_min_le.mp (hfx' x x.2) |>.2 y₁_in y₂_in hu hv huv |>.trans hx

  have subset_or_subset : ∀ y ∈ S, (C b y ⊆ C b y₁) ∨ (C b y ⊆ C b y₂) := fun y hy ↦
    C_preconnected _ _ (cY hy) |>.subset_or_subset_of_closed
      (C_closed _ _ y₁_in) (C_closed _ _ y₂_in)
      (by simpa [disjoint_iff_inter_eq_empty] using this) (C_cover_S _ hy)

  have subset_nand_subset : ∀ y ∈ S, ¬(D b y ⊆ C b y₁ ∧ D b y ⊆ C b y₂) :=
    fun y hy ⟨H₁, H₂⟩ ↦ (H y (cY hy)).elim fun x hx ↦
      this.subset ⟨H₁ (CD_subset y hx), H₂ (CD_subset y hx)⟩

  have key : ∀ y ∈ S,
      (C b y ⊆ C b y₁ ↔ D b y ⊆ C b y₁) ∧ (C b y ⊆ C b y₂ ↔ D b y ⊆ C b y₂) :=
    fun y hy ↦ (subset_or_subset y hy).iff_of_imp_of_not_and (subset_nand_subset y hy)
      (subset_trans <| DC_subset y) (subset_trans <| DC_subset y)

  set I := {y : S | D b y ⊆ C b y₁}
  set J := {y : S | D b y ⊆ C b y₂}
  have I_eq : I = {y : S | C b y ⊆ C b y₁} := Set.ext fun y ↦ (key y y.2).1.symm
  have J_eq : J = {y : S | C b y ⊆ C b y₂} := Set.ext fun y ↦ (key y y.2).2.symm
  have mem_I : ⟨y₁, left_mem_segment _ _ _⟩ ∈ I := DC_subset _
  have mem_J : ⟨y₂, right_mem_segment _ _ _⟩ ∈ J := DC_subset _

  have IJ_cover_S : I ∪ J = univ := by
    simpa [I_eq, J_eq, eq_univ_iff_forall] using subset_or_subset

  have IJ_disj : Disjoint I J := by
    rw [Set.disjoint_iff]
    exact fun y ↦ subset_nand_subset y y.2

  have I_closed : IsClosed I := by
    have : I = ⋂ (x : X), {y : S | b ≤ f x y} ∪ {y | f x y₁ ≤ b} := by
      ext y
      simp_rw [I, subset_def, mem_iInter, mem_union, imp_iff_not_or, C, D, mem_setOf, not_lt]
    rw [this]
    exact isClosed_iInter fun x ↦ .union (hfx x x.2 |>.isClosed_preimage b) isClosed_const
  have J_closed : IsClosed J := by
    have : J = ⋂ (x : X), {y : S | b ≤ f x y} ∪ {y | f x y₂ ≤ b} := by
      ext y
      simp_rw [J, subset_def, mem_iInter, mem_union, imp_iff_not_or, C, D, mem_setOf, not_lt]
    rw [this]
    exact isClosed_iInter fun x ↦ .union (hfx x x.2 |>.isClosed_preimage b) isClosed_const

  rcases isPreconnected_univ.subset_or_subset_of_closed I_closed J_closed IJ_disj IJ_cover_S.ge
    with (I_cover|J_cover)
  · exact Set.disjoint_iff.mp IJ_disj ⟨I_cover trivial, mem_J⟩
  · exact Set.disjoint_iff.mp IJ_disj ⟨mem_I, J_cover trivial⟩

include ne_X kX cY hfy hfx hfx' hfy hfy' in
theorem lemma1 [DenselyOrdered β] {y₁ y₂ : F} (y₁_in : y₁ ∈ Y) (y₂_in : y₂ ∈ Y) {a : β}
    (H : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ a) :
    ∃ x ∈ X, max (f x y₁) (f x y₂) ≤ a := by
  -- We use compactness of `X` and semicontinuity of `f · y` to get some margin: it
  -- suffices to show that `∀ b > a, ∃ x ∈ X, max (f x y₁) (f x y₂) ≤ b`, whic is exactly
  -- `lemma0`.
  obtain ⟨x, x_in, hx⟩ : ∃ x ∈ X, IsMinOn (max (f · y₁) (f · y₂)) X x :=
    (hfy y₁ y₁_in |>.sup <| hfy y₂ y₂_in).exists_forall_le_of_isCompact ne_X kX
  use x, x_in
  refine forall_lt_le_iff_le.mp fun b hab ↦ ?_
  rcases lemma0 cY hfx hfx' hfy hfy' y₁_in y₂_in hab H with ⟨x', x'_in, hx'⟩
  exact (hx x'_in).trans hx'

include hfx hfx' hfy hfy' cY in
theorem lemma0' {y₁ y₂ : F} (y₁_in : y₁ ∈ Y) (y₂_in : y₂ ∈ Y) {a b : β} (a_lt_b : a < b)
    (H : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ a) :
    ∃ x ∈ X, max (f x y₁) (f x y₂) < b := by
  -- We only care about the subset `[y₁, y₂]` of `Y`, so we restrict some of our hypotheses
  -- for convenience
  set S : Set F := segment ℝ y₁ y₂
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace (convex_segment _ _ |>.isPreconnected)
  replace cY : S ⊆ Y := cY.segment_subset y₁_in y₂_in
  replace hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) S := fun x hx ↦ (hfx x hx).mono cY

  simp_rw [upperSemicontinuousOn_iff_restrict] at hfx
  simp_rw [lowerSemicontinuousOn_iff_restrict] at hfy

  set C : β → F → Set X := fun c y ↦ {x | f x y ≤ c}
  set D : β → F → Set X := fun c y ↦ {x | f x y < c}

  -- Start by some obvious observations on `C` and `D`
  have C_closed : ∀ c : β, ∀ y ∈ Y, IsClosed (C c y) :=
    fun c y hy ↦ hfy y hy |>.isClosed_preimage _
  have C_mono : ∀ y, Monotone (C · y) := fun y _ _ hle _ h ↦ le_trans h hle
  have CD_subset : ∀ y, C a y ⊆ D b y := fun y _ h ↦ h.trans_lt a_lt_b
  have DC_subset : ∀ y, D b y ⊆ C b y := fun y _ h ↦ h.le
  have C_preconnected : ∀ c, ∀ y ∈ Y, IsPreconnected (C c y) := fun c y hy ↦ by
    change IsPreconnected (Subtype.val ⁻¹' {x : E | f x y ≤ c})
    simp_rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_val]
    exact hfy' y hy c |>.isPreconnected
  have D_preconnected : ∀ c, ∀ y ∈ Y, IsPreconnected (D c y) := fun c y hy ↦ by
    change IsPreconnected (Subtype.val ⁻¹' {x : E | f x y < c})
    simp_rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_val]
    exact ((hfy' y hy).convex_lt c).isPreconnected
  have D_open : ∀ c : β, ∀ y ∈ Y, IsClosed (D c y) :=
    fun c y hy ↦ hfy y hy |>.isOpen_preimage _

  -- Now, reformulate the goal as `D b y₁ ∩ D b y₂ ≠ ∅` and `H` as `∀ y ∈ Y, C a y = ∅`.
  suffices (D b y₁ ∩ D b y₂).Nonempty from
    this.elim fun x ⟨hxy₁, hxy₂⟩ ↦ ⟨x, x.2, max_lt hxy₁ hxy₂⟩ -- sup_le hxy₁ hxy₂⟩
  replace H : ∀ y ∈ Y, (C a y).Nonempty :=
    fun y hy ↦ (H y hy).elim fun x ⟨x_in, hx⟩ ↦ ⟨⟨x, x_in⟩, hx⟩
  -- By contradiction, assume `D b y₁ ∩ D b y₂ = ∅`.
  by_contra!

  have C_cover_S : ∀ y ∈ S, C b y ⊆ C b y₁ ∪ C b y₂ := by
    rintro - ⟨u, v, hu, hv, huv, rfl⟩ x hx
    change f x y₁ ≤ b ∨ f x y₂ ≤ b
    rw [← min_le_iff]
    exact quasiconcaveOn_iff_min_le.mp (hfx' x x.2) |>.2 y₁_in y₂_in hu hv huv |>.trans hx

  have D_cover_S : ∀ y ∈ S, D b y ⊆ D b y₁ ∪ D b y₂ := by
    rintro - ⟨u, v, hu, hv, huv, rfl⟩ x hx
    change f x y₁ < b ∨ f x y₂ < b
    rw [← min_lt_iff]
    exact lt_of_le_of_lt ((quasiconcaveOn_iff_min_le.mp (hfx' x x.2)).2 y₁_in y₂_in hu hv huv) hx

  have subset_or_subset : ∀ y ∈ S, (D b y ⊆ D b y₁) ∨ (D b y ⊆ D b y₂) := fun y hy ↦
    D_preconnected _ _ (cY hy) |>.subset_or_subset_of_open
      (D_open _ _ y₁_in) (D_open _ _ y₂_in)
      (by simpa [disjoint_iff_inter_eq_empty] using this) (D_cover_S _ hy)

  have subset_nand_subset : ∀ y ∈ S, ¬(D b y ⊆ C b y₁ ∧ D b y ⊆ C b y₂) :=
    fun y hy ⟨H₁, H₂⟩ ↦ (H y (cY hy)).elim fun x hx ↦
      this.subset ⟨H₁ (CD_subset y hx), H₂ (CD_subset y hx)⟩

  have key : ∀ y ∈ S,
      (C b y ⊆ C b y₁ ↔ D b y ⊆ C b y₁) ∧ (C b y ⊆ C b y₂ ↔ D b y ⊆ C b y₂) :=
    fun y hy ↦ (subset_or_subset y hy).iff_of_imp_of_not_and (subset_nand_subset y hy)
      (subset_trans <| DC_subset y) (subset_trans <| DC_subset y)

  set I := {y : S | D b y ⊆ C b y₁}
  set J := {y : S | D b y ⊆ C b y₂}
  have I_eq : I = {y : S | C b y ⊆ C b y₁} := Set.ext fun y ↦ (key y y.2).1.symm
  have J_eq : J = {y : S | C b y ⊆ C b y₂} := Set.ext fun y ↦ (key y y.2).2.symm
  have mem_I : ⟨y₁, left_mem_segment _ _ _⟩ ∈ I := DC_subset _
  have mem_J : ⟨y₂, right_mem_segment _ _ _⟩ ∈ J := DC_subset _

  have IJ_cover_S : I ∪ J = univ := by
    simpa [I_eq, J_eq, eq_univ_iff_forall] using subset_or_subset

  have IJ_disj : Disjoint I J := by
    rw [Set.disjoint_iff]
    exact fun y ↦ subset_nand_subset y y.2

  have I_closed : IsClosed I := by
    have : I = ⋂ (x : X), {y : S | b ≤ f x y} ∪ {y | f x y₁ ≤ b} := by
      ext y
      simp_rw [I, subset_def, mem_iInter, mem_union, imp_iff_not_or, C, D, mem_setOf, not_lt]
    rw [this]
    exact isClosed_iInter fun x ↦ .union (hfx x x.2 |>.isClosed_preimage b) isClosed_const
  have J_closed : IsClosed J := by
    have : J = ⋂ (x : X), {y : S | b ≤ f x y} ∪ {y | f x y₂ ≤ b} := by
      ext y
      simp_rw [J, subset_def, mem_iInter, mem_union, imp_iff_not_or, C, D, mem_setOf, not_lt]
    rw [this]
    exact isClosed_iInter fun x ↦ .union (hfx x x.2 |>.isClosed_preimage b) isClosed_const

  rcases isPreconnected_univ.subset_or_subset_of_closed I_closed J_closed IJ_disj IJ_cover_S.ge
    with (I_cover|J_cover)
  · exact Set.disjoint_iff.mp IJ_disj ⟨I_cover trivial, mem_J⟩
  · exact Set.disjoint_iff.mp IJ_disj ⟨mem_I, J_cover trivial⟩

include ne_X kX cY hfy hfx hfx' hfy hfy' in
theorem lemma1' {y₁ y₂ : F} (y₁_in : y₁ ∈ Y) (y₂_in : y₂ ∈ Y) {a : β}
    (H : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ a) :
    ∃ x ∈ X, max (f x y₁) (f x y₂) ≤ a := by
  -- We use compactness of `X` and semicontinuity of `f · y` to get some margin: it
  -- suffices to show that `∀ b > a, ∃ x ∈ X, max (f x y₁) (f x y₂) ≤ b`, whic is exactly
  -- `lemma0`.
  obtain ⟨x, x_in, hx⟩ : ∃ x ∈ X, IsMinOn (max (f · y₁) (f · y₂)) X x :=
    (hfy y₁ y₁_in |>.sup <| hfy y₂ y₂_in).exists_forall_le_of_isCompact ne_X kX
  use x, x_in
  -- refine forall_lt_le_iff_le.mp fun b hab ↦ ?_
  have (b) (hab : a < b) : f x y₁ ⊔ f x y₂ ≤ b := by
    rcases lemma0 cY hfx hfx' hfy hfy' y₁_in y₂_in hab H with ⟨x', x'_in, hx'⟩
    exact (hx x'_in).trans hx'
  sorry
