import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Order.LowerUpperTopology

section Semicontinuity

/-!

- `LowerSemicontinuous.is_compact.exists_forall_le` :
  We prove that lower semicontinuous functions attain their lower bound
  on a nonempty compact set.

- `LowerSemicontinuous.bdd_below_on.is_compact` :
  As a consequence, a lower semicontinuous function
  on a compact set is bounded below.

We then prove the opposite results for upper semicontinuous functions :

- `UpperSemicontinuous.is_compact.exists_forall_ge`

- `bdd_above_on.is_compact`

The proofs follow Bourbaki, *General Topology*, chapter 4, §6, n°2.
I do them twice (copy paste worked well), without trying to get ones
from the other by passing to the opposite order on `β`.

However, they could also be done using the general machinery already in mathlib,
namely proving that a function `f: α → β` is upper semicontinuous iff it is continuous
when `β` is endowed with `with_lower_topology β`, and characterizing
the compact sets of `with_lower_topology β` as those which have a maximal element.

I tried to do so but quickly bumped on missing instances,
such as `complete_linear_order_topology (with_lower_topology β)`.
And indeed, `with_lower_topology β` does ***not*** satisfy `order_topology` !

In any case, `with_upper_topology` is missing, so we should also play with
the opposite order.

Another difficulty is the type of order we want to impose on β.
Ultimately, it has to be `conditionally_complete_linear_order β`, to allow for `ℝ`,
but it would simplify the proofs to do it for `complete_linear_order β`,
and adding `⊤` and `⊥` at the end if needed.
Inded, for `conditionally_complete_linear_order β`, the `supr` and `infi` only
do what one expects under additional `bdd_above` or `bdd_below` assumptions
which are painful to check each time.
(Moreover, the `simp` lemmas may be missing. )

-/
open scoped Filter Topology

open Set Filter

-- TODO : replace with mathlib's is_total.directed
theorem IsTotal.directed' {α : Type _} {ι : Sort _} (r : α → α → Prop) [IsTotal α r] (f : ι → α) :
    Directed r f := fun i j => by
  cases (total_of r (f i) (f j)) with
  | inl h => exact ⟨j, h, refl _⟩
  | inr h => exact ⟨i, refl _, h⟩

section LinearOrder

universe u v

variable {α : Type u} {β : Type v} [TopologicalSpace α] {f : α → β}

variable [LinearOrder β]

section LowerSemicontinuous

theorem LowerSemicontinuousWithinAt.sup {g : α → β} {s : Set α} {a : α}
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x => f x ⊔ g x) s a := by
  intro b hb
  simp only [lt_sup_iff] at hb ⊢
  cases' hb with hb hb
  · filter_upwards [hf b hb] with x using Or.intro_left _
  · filter_upwards [hg b hb] with x using Or.intro_right _

theorem LowerSemicontinuousAt.sup {g : α → β} {a : α} (hf : LowerSemicontinuousAt f a)
    (hg : LowerSemicontinuousAt g a) : LowerSemicontinuousAt (fun x => f x ⊔ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.sup hg

theorem LowerSemicontinuousOn.sup {s : Set α} {g : α → β} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun x => f x ⊔ g x) s := fun a ha =>
  (hf a ha).sup (hg a ha)

theorem LowerSemicontinuous.sup {g : α → β} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) : LowerSemicontinuous fun x => f x ⊔ g x := fun a =>
  (hf a).sup (hg a)

theorem LowerSemicontinuousWithinAt.inf {g : α → β} {s : Set α} {a : α}
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x => f x ⊓ g x) s a := by
  intro b hb
  simp only [lt_inf_iff] at hb ⊢
  exact Eventually.and (hf b hb.1) (hg b hb.2)

theorem LowerSemicontinuousAt.inf {g : α → β} {a : α} (hf : LowerSemicontinuousAt f a)
    (hg : LowerSemicontinuousAt g a) : LowerSemicontinuousAt (fun x => f x ⊓ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.inf hg

theorem LowerSemicontinuousOn.inf {g : α → β} {s : Set α} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun x => f x ⊓ g x) s := fun a ha =>
  (hf a ha).inf (hg a ha)

theorem LowerSemicontinuous.inf {g : α → β} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) : LowerSemicontinuous fun x => f x ⊓ g x := fun a =>
  (hf a).inf (hg a)

-- TODO : add same for upper_semicontinuous
theorem LowerSemicontinuousAt.comp {γ : Type _} [TopologicalSpace γ] {g : γ → α} {x : γ}
    (hf : LowerSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerSemicontinuousAt (f ∘ g) x := fun b hb => hg.eventually (hf b hb)

theorem LowerSemicontinuous.comp {γ : Type _} [TopologicalSpace γ] {g : γ → α}
    (hf : LowerSemicontinuous f) (hg : Continuous g) : LowerSemicontinuous (f ∘ g) := fun x =>
  (hf (g x)).comp hg.continuousAt

theorem LowerSemicontinuousWithinAt.comp {γ : Type _} [TopologicalSpace γ] {g : γ → α} {s : Set γ}
    {t : Set α} {x : γ} (hf : LowerSemicontinuousWithinAt f t (g x)) (hg : ContinuousWithinAt g s x)
    (hg' : MapsTo g s t) : LowerSemicontinuousWithinAt (f ∘ g) s x := fun b hb =>
  (hg.tendsto_nhdsWithin hg').eventually (hf b hb)

theorem LowerSemicontinuousOn.comp {γ : Type _} [TopologicalSpace γ] {g : γ → α} {s : Set γ}
    {t : Set α} (hf : LowerSemicontinuousOn f t) (hg : ContinuousOn g s) (hg' : MapsTo g s t) :
    LowerSemicontinuousOn (f ∘ g) s := fun x hx => (hf (g x) (hg' hx)).comp (hg x hx) hg'

theorem lowerSemicontinuousOn_iff_restrict {s : Set α} :
    LowerSemicontinuousOn f s ↔ LowerSemicontinuous (s.restrict f) := by
  rw [LowerSemicontinuousOn, LowerSemicontinuous, SetCoe.forall]
  refine' forall₂_congr fun a ha => forall₂_congr fun b _ => _
  simp only [nhdsWithin_eq_map_subtype_coe ha, eventually_map, restrict]

theorem lowerSemicontinuousOn_iff_preimage_Ioi {s : Set α} :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ u : Set α, IsOpen u ∧ s ∩ f ⁻¹' Set.Ioi b = s ∩ u := by
  simp only [lowerSemicontinuousOn_iff_restrict, restrict_eq,
    lowerSemicontinuous_iff_isOpen_preimage, preimage_comp, isOpen_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

theorem lowerSemicontinuousOn_iff_preimage_Iic {s : Set α} :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ v : Set α, IsClosed v ∧ s ∩ f ⁻¹' Set.Iic b = s ∩ v := by
  simp only [lowerSemicontinuousOn_iff_restrict, restrict_eq,
    lowerSemicontinuous_iff_isClosed_preimage, preimage_comp, isClosed_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set -/
theorem LowerSemicontinuousOn.exists_forall_le_of_isCompact {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuousOn f s) : ∃ a ∈ s, ∀ x ∈ s, f a ≤ f x := by
  haveI : Nonempty α := ⟨ne_s.choose⟩
  haveI : Nonempty s := ⟨⟨ne_s.choose, ne_s.choose_spec⟩⟩
  let φ : β → Filter α := fun b => 𝓟 (s ∩ f ⁻¹' Iic b)
  let ℱ : Filter α := ⨅ a : s, φ (f a)
  have : ℱ.NeBot := by
    refine' iInf_neBot_of_directed _ _
    · change Directed GE.ge (fun x ↦ (φ ∘ (fun (a : s) ↦ f ↑a)) x)
      refine' Directed.mono_comp GE.ge _ _
      · intro x y hxy
        refine'
          principal_mono.mpr (inter_subset_inter_right _ (preimage_mono <| Iic_subset_Iic.mpr hxy))
      · apply IsTotal.directed' GE.ge
    · intro x
      have : (pure x : Filter α) ≤ φ (f x) := le_principal_iff.mpr ⟨x.2, le_refl (f x)⟩
      exact neBot_of_le this
  have hℱs : ℱ ≤ 𝓟 s :=
    iInf_le_of_le ⟨ne_s.choose, ne_s.choose_spec⟩ (principal_mono.mpr <| inter_subset_left)
  have hℱ : ∀ x ∈ s, ∀ᶠ y in ℱ, f y ≤ f x := fun x hx =>
    mem_iInf_of_mem ⟨x, hx⟩ (by simp only [mem_principal]; apply inter_subset_right)
  obtain ⟨a, ha, h⟩ := hs hℱs
  letI : (𝓝 a ⊓ ℱ).NeBot := h
  refine' ⟨a, ha, fun x hx => le_of_not_lt fun hxa => _⟩
  suffices ∀ᶠ _ in 𝓝 a ⊓ ℱ, False by rwa [eventually_const] at this
  filter_upwards [(hf a ha (f x) hxa).filter_mono (inf_le_inf_left _ hℱs),
    (hℱ x hx).filter_mono (inf_le_right : 𝓝 a ⊓ ℱ ≤ ℱ)] using fun y h₁ h₂ => not_le_of_lt h₁ h₂

/-- A lower semicontinuous function is bounded above on a compact set. -/
theorem LowerSemicontinuousOn.bddBelow_of_isCompact [Nonempty β] {s : Set α} (hs : IsCompact s)
    (hf : LowerSemicontinuousOn f s) : BddBelow (f '' s) := by
  cases s.eq_empty_or_nonempty with
  | inl h =>
      simp only [h, Set.image_empty]
      exact bddBelow_empty
  | inr h =>
      obtain ⟨a, _, has⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact h hs hf
      use f a
      rintro b ⟨x, hx, rfl⟩; exact has x hx

end LowerSemicontinuous

section UpperSemicontinuous

theorem UpperSemicontinuousAt.comp {γ : Type _} [TopologicalSpace γ] {g : γ → α} {x : γ}
    (hf : UpperSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    UpperSemicontinuousAt (f ∘ g) x := fun b hb => hg.eventually (hf b hb)

theorem UpperSemicontinuous.comp {γ : Type _} [TopologicalSpace γ] {g : γ → α}
    (hf : UpperSemicontinuous f) (hg : Continuous g) : UpperSemicontinuous (f ∘ g) := fun x =>
  (hf (g x)).comp hg.continuousAt

theorem UpperSemicontinuousWithinAt.comp {γ : Type _} [TopologicalSpace γ] {g : γ → α} {s : Set γ}
    {t : Set α} {x : γ} (hf : UpperSemicontinuousWithinAt f t (g x)) (hg : ContinuousWithinAt g s x)
    (hg' : MapsTo g s t) : UpperSemicontinuousWithinAt (f ∘ g) s x := fun b hb =>
  (hg.tendsto_nhdsWithin hg').eventually (hf b hb)

theorem UpperSemicontinuousOn.comp {γ : Type _} [TopologicalSpace γ] {g : γ → α} {s : Set γ}
    {t : Set α} (hf : UpperSemicontinuousOn f t) (hg : ContinuousOn g s) (hg' : MapsTo g s t) :
    UpperSemicontinuousOn (f ∘ g) s := fun x hx => (hf (g x) (hg' hx)).comp (hg x hx) hg'

theorem upperSemicontinuousOn_iff_restrict {s : Set α} :
    UpperSemicontinuousOn f s ↔ UpperSemicontinuous (s.restrict f) :=
  lowerSemicontinuousOn_iff_restrict  (β := βᵒᵈ)

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set -/
theorem UpperSemicontinuousOn.exists_forall_ge_of_isCompact {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : ∃ a ∈ s, ∀ x ∈ s, f x ≤ f a := by
  apply LowerSemicontinuousOn.exists_forall_le_of_isCompact (β := βᵒᵈ) ne_s hs
  exact hf

/-- An upper semicontinuous function is bounded above on a compact set. -/
theorem UpperSemicontinuousOn.bddAbove_of_isCompact [Nonempty β] {s : Set α}
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : BddAbove (f '' s) :=
  LowerSemicontinuousOn.bddBelow_of_isCompact (β := βᵒᵈ) hs hf

end UpperSemicontinuous

end LinearOrder

section CompleteLinearOrder

variable {β α : Type _} [TopologicalSpace α] {f : α → β}

variable [CompleteLinearOrder β]

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set -/
theorem LowerSemicontinuousOn.exists_iInf_of_isCompact {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuousOn f s) : ∃ a ∈ s, f a = ⨅ x ∈ s, f x := by
  obtain ⟨a, ha, ha_le⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_s hs hf
  use a; apply And.intro ha
  apply le_antisymm
  rw [le_iInf₂_iff]; intro x hx; exact ha_le x hx
  exact iInf₂_le a ha

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set -/
theorem LowerSemicontinuous.exists_iInf_of_isCompact {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuous f) : ∃ a ∈ s, f a = ⨅ x ∈ s, f x :=
  (hf.lowerSemicontinuousOn s).exists_iInf_of_isCompact ne_s hs

theorem lowerSemicontinuousWithinAt_infi₂ {ι : Type _} {f : ι → α → β} {s : Set α} {a : α}
    {I : Set ι} (hf : ∀ i ∈ I, LowerSemicontinuousWithinAt (f i) s a) :
    LowerSemicontinuousWithinAt (fun x => ⨅ i ∈ I, f i x) s a :=
  sorry

theorem lowerSemicontinuousOn_infi₂ {ι : Type _} {f : ι → α → β} {s : Set α} {I : Set ι}
    (hf : ∀ i, LowerSemicontinuousOn (f i) s) : LowerSemicontinuousOn (fun x => ⨅ i ∈ I, f i x) s :=
  sorry

theorem lowerSemicontinuousAt_infi₂ {ι : Type _} {f : ι → α → β} {a : α} {I : Set ι}
    (hf : ∀ i, LowerSemicontinuousAt (f i) a) : LowerSemicontinuousAt (fun x => ⨅ i ∈ I, f i x) a :=
  sorry

theorem lowerSemicontinuous_infi₂ {ι : Type _} {f : ι → α → β} {I : Set ι}
    (hf : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x => ⨅ i ∈ I, f i x :=
  sorry

theorem lowerSemicontinuousWithinAt_supr₂ {ι : Type _} {f : ι → α → β} {s : Set α} {a : α}
    {I : Set ι} (hI : I.Finite) (hf : ∀ i ∈ I, LowerSemicontinuousWithinAt (f i) s a) :
    LowerSemicontinuousWithinAt (fun x => ⨆ i ∈ I, f i x) s a := by
  revert hf
  refine' Set.Finite.induction_on hI _ _
  · intro _
    simp only [mem_empty_iff_false, ciSup_false, iSup_bot]
    exact lowerSemicontinuousWithinAt_const
  intro j J _ _ hrec hf
  suffices ∀ x, (⨆ (i : ι) (_ : i ∈ insert j J), f i x) = f j x ⊔ ⨆ i ∈ J, f i x by
    rw [funext this]
    apply LowerSemicontinuousWithinAt.sup (hf j (Set.mem_insert j J))
    apply hrec
    intro i hi; exact hf i (Set.mem_insert_of_mem j hi)
  intro x
  simp only [Set.insert_eq]
  rw [iSup_union]
  apply congr_arg₂ _ _ rfl
  simp only [mem_singleton_iff, iSup_iSup_eq_left]



theorem lowerSemicontinuousOn_supr₂ {ι : Type _} {f : ι → α → β} {s : Set α} {I : Set ι}
    (hI : I.Finite) (hf : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x => ⨆ i ∈ I, f i x) s := fun a ha =>
  lowerSemicontinuousWithinAt_supr₂ hI fun i hi => hf i hi a ha

theorem lowerSemicontinuousAt_supr₂ {ι : Type _} {f : ι → α → β} {a : α} {I : Set ι} (hI : I.Finite)
    (hf : ∀ i, LowerSemicontinuousAt (f i) a) : LowerSemicontinuousAt (fun x => ⨆ i ∈ I, f i x) a :=
  sorry

theorem lowerSemicontinuous_supr₂ {ι : Type _} {f : ι → α → β} {I : Set ι} (hI : I.Finite)
    (hf : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x => ⨆ i ∈ I, f i x :=
  sorry

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set -/
theorem UpperSemicontinuousOn.exists_iSup_of_isCompact {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : ∃ a ∈ s, f a = ⨆ x ∈ s, f x := by
  apply LowerSemicontinuousOn.exists_iInf_of_isCompact (β := βᵒᵈ) ne_s hs hf

theorem upperSemicontinuousWithinAt_supr₂ {ι : Type _} {f : ι → α → β} {s : Set α} {a : α}
    {I : Set ι} (hf : ∀ i, UpperSemicontinuousWithinAt (f i) s a) :
    UpperSemicontinuousWithinAt (fun x => ⨅ i ∈ I, f i x) s a :=
  sorry

theorem upperSemicontinuousOn_supr₂ {ι : Type _} {f : ι → α → β} {s : Set α} {I : Set ι}
    (hf : ∀ i, UpperSemicontinuousOn (f i) s) : UpperSemicontinuousOn (fun x => ⨅ i ∈ I, f i x) s :=
  sorry

theorem upperSemicontinuousAt_supr₂ {ι : Type _} {f : ι → α → β} {a : α} {I : Set ι}
    (hf : ∀ i, UpperSemicontinuousAt (f i) a) : UpperSemicontinuousAt (fun x => ⨅ i ∈ I, f i x) a :=
  sorry

theorem upperSemicontinuous_supr₂ {ι : Type _} {f : ι → α → β} {I : Set ι}
    (hf : ∀ i, UpperSemicontinuous (f i)) : UpperSemicontinuous fun x => ⨅ i ∈ I, f i x :=
  sorry

-- Lemmas which depend on two topologies

theorem lowerSemicontinuousWithinAt_iSup₂ {ι : Type _} {f : ι → α → β}
    {s : Set α} {a : α}
    [TopologicalSpace ι] {I : Set ι} (ne_I : Set.Nonempty I) (hI : IsCompact I)
    (hf : ∀ i ∈ I, LowerSemicontinuousWithinAt (f i) s a)
    (hf' : UpperSemicontinuousOn (fun i ↦ f i a) I) :
    LowerSemicontinuousWithinAt (fun x => ⨆ i ∈ I, f i x) s a := by
  intro t ht
  dsimp at ht
  obtain ⟨i, hi, hi'⟩ := hf'.exists_iSup_of_isCompact ne_I hI
  rw [← hi'] at ht
  let h := hf i hi t ht
  dsimp
  apply Filter.Eventually.mp h
  apply Filter.eventually_of_forall
  intro x hx
  apply lt_of_lt_of_le hx
  apply le_iSup₂ i hi

theorem upperSemicontinuousWithinAt_iInf₂ {ι : Type _} {f : ι → α → β}
    {s : Set α} {a : α}
    [TopologicalSpace ι] {I : Set ι} (ne_I : Set.Nonempty I) (hI : IsCompact I)
    (hf : ∀ i ∈ I, UpperSemicontinuousWithinAt (f i) s a)
    (hf' : LowerSemicontinuousOn (fun i ↦ f i a) I) :
    UpperSemicontinuousWithinAt (fun x => ⨅ i ∈ I, f i x) s a :=
  lowerSemicontinuousWithinAt_iSup₂ (β := βᵒᵈ) ne_I hI hf hf'




end CompleteLinearOrder

end Semicontinuity

#exit

section Junk

/-
Attempts to do the job without reproving anything

but one gets to prove [complete_linear_order_topology (with_lower_topology β)]
-/
variable {α β : Type _} [TopologicalSpace α] [Preorder β] [TopologicalSpace β] [OrderTopology β]

variable (f : α → β)

open WithLowerTopology

namespace WithLowerTopology

theorem toLower_continous : Continuous (toLower : β → WithLowerTopology β) :=
  sorry
#align with_lower_topology.to_lower_continous WithLowerTopology.toLower_continous

theorem ofLower_upper_semicontinous : UpperSemicontinuous (ofLower : WithLowerTopology β → β) :=
  sorry
#align with_lower_topology.of_lower_upper_semicontinous WithLowerTopology.ofLower_upper_semicontinous

theorem upper_semicontinuous_iff_toLower_comp_continuousAt {a : α} :
    UpperSemicontinuousAt f a ↔ ContinuousAt (toLower ∘ f) a :=
  sorry
#align with_lower_topology.upper_semicontinuous_iff_to_lower_comp_continuous_at WithLowerTopology.upper_semicontinuous_iff_toLower_comp_continuousAt

theorem upperSemicontinuous_iff_toLower_comp_continuous :
    UpperSemicontinuous f ↔ Continuous (toLower ∘ f) :=
  sorry
#align with_lower_topology.upper_semicontinuous_iff_to_lower_comp_continuous WithLowerTopology.upperSemicontinuous_iff_toLower_comp_continuous

theorem upper_semicontinuous_iff_toLower_comp_continuousOn {s : Set α} :
    UpperSemicontinuousOn f s ↔ ContinuousOn (toLower ∘ f) s :=
  sorry
#align with_lower_topology.upper_semicontinuous_iff_to_lower_comp_continuous_on WithLowerTopology.upper_semicontinuous_iff_toLower_comp_continuousOn

end WithLowerTopology

end Junk
