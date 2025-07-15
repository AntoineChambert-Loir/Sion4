import Mathlib
-- import Mathlib.Topology.Semicontinuous
-- import Mathlib.Topology.Order.LowerUpperTopology
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

section Preorder

open Set

variable {a β : Type*} [Preorder β] {f : α → β} {s : Set α} {a : α}

-- move to [Mathlib.Order.Filter.Extr]
theorem _root_.IsMinOn.isGLB (ha : a ∈ s) (hfsa : IsMinOn f s a) :
    IsGLB {f x | x ∈ s} (f a) := by
  rw [isGLB_iff_le_iff]
  intro b
  simp only [mem_lowerBounds, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun hba x hx ↦ le_trans hba (hfsa hx), fun hb ↦ hb a ha⟩

theorem _root_.IsMaxOn.isLUB (ha : a ∈ s) (hfsa : IsMaxOn f s a) :
    IsLUB {f x | x ∈ s} (f a) := by
  rw [isLUB_iff_le_iff]
  intro b
  simp only [mem_upperBounds, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun hba x hx ↦ le_trans (hfsa hx) hba, fun hb ↦ hb a ha⟩

variable [TopologicalSpace α]

theorem LowerSemicontinuousWithinAt.congr
    (has : a ∈ s) (hfg : ∀ᶠ x in nhdsWithin a s, f x = g x) :
    LowerSemicontinuousWithinAt f s a ↔ LowerSemicontinuousWithinAt g s a := by
  unfold LowerSemicontinuousWithinAt
  apply forall_congr'
  intro b
  rw [Filter.EventuallyEq.eq_of_nhdsWithin hfg has]
  apply imp_congr Iff.rfl
  apply Filter.eventually_congr
  apply Filter.Eventually.mono hfg
  intro x hx
  rw [hx]

theorem UpperSemicontinuousWithinAt.congr
    (has : a ∈ s) (hfg : ∀ᶠ x in nhdsWithin a s, f x = g x) :
    UpperSemicontinuousWithinAt f s a ↔ UpperSemicontinuousWithinAt g s a :=
  LowerSemicontinuousWithinAt.congr (β := βᵒᵈ) has hfg

variable {γ : Type*} [TopologicalSpace γ] {g : γ → α} {x : γ} {t : Set γ}

theorem LowerSemicontinuousWithinAt.comp
    (hf : LowerSemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    LowerSemicontinuousWithinAt (f ∘ g) t x := fun b hb ↦
  (hg.tendsto_nhdsWithin hg').eventually (hf b hb)

theorem LowerSemicontinuousAt.comp
    (hf : LowerSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerSemicontinuousAt (f ∘ g) x := fun b hb ↦
  hg.eventually (hf b hb)

theorem LowerSemicontinuousOn.comp
    (hf : LowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    LowerSemicontinuousOn (f ∘ g) t := fun x hx ↦
  (hf (g x) (hg' hx)).comp (hg x hx) hg'

theorem LowerSemicontinuous.comp
    (hf : LowerSemicontinuous f) (hg : Continuous g) : LowerSemicontinuous (f ∘ g) := fun x ↦
  (hf (g x)).comp hg.continuousAt

theorem lowerSemicontinuousOn_iff_restrict :
    LowerSemicontinuousOn f s ↔ LowerSemicontinuous (s.restrict f) := by
  rw [LowerSemicontinuousOn, LowerSemicontinuous, SetCoe.forall]
  refine' forall₂_congr fun a ha ↦ forall₂_congr fun b _ ↦ _
  simp only [nhdsWithin_eq_map_subtype_coe ha, eventually_map, restrict]

theorem lowerSemicontinuousOn_iff_preimage_Ioi :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ u, IsOpen u ∧ s ∩ f ⁻¹' Set.Ioi b = s ∩ u := by
  simp only [lowerSemicontinuousOn_iff_restrict, restrict_eq,
    lowerSemicontinuous_iff_isOpen_preimage, preimage_comp, isOpen_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

variable {ι : Type*} {f : ι → α → β} {I : Set ι}

theorem lowerSemicontinuousOn_of_forall_isMaxOn_and_mem
    (hfy : ∀ i ∈ I, LowerSemicontinuousOn (f i) s)
    {M : α → ι}
    (M_mem : ∀ x ∈ s, M x ∈ I)
    (M_max : ∀ x ∈ s, IsMaxOn (fun y ↦ f y x) I (M x)) :
    LowerSemicontinuousOn (fun x ↦ f (M x) x) s := by
  intro x hx b hb
  apply Filter.Eventually.mp <| hfy (M x) (M_mem x hx) x hx b hb
  apply eventually_nhdsWithin_of_forall
  intro z hz h
  exact lt_of_lt_of_le h (M_max z hz (M_mem x hx))

theorem upperSemicontinuousOn_of_forall_isMinOn_and_mem
    (hfy : ∀ i ∈ I, UpperSemicontinuousOn (f i) s)
    {m : α → ι}
    (m_mem : ∀ x ∈ s, m x ∈ I)
    (m_min : ∀ x ∈ s, IsMinOn (fun i ↦ f i x) I (m x)) :
    UpperSemicontinuousOn (fun x ↦ f (m x) x) s :=
  lowerSemicontinuousOn_of_forall_isMaxOn_and_mem (β := βᵒᵈ) hfy m_mem m_min

end Preorder

section LinearOrder

variable {α : Type*} {β : Type*} [TopologicalSpace α] [LinearOrder β]
  {f g : α → β} {s : Set α} {a : α}

section LowerSemicontinuous

theorem lowerSemicontinuousOn_iff_preimage_Iic :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ v : Set α, IsClosed v ∧ s ∩ f ⁻¹' Set.Iic b = s ∩ v := by
  simp only [lowerSemicontinuousOn_iff_restrict, restrict_eq,
    lowerSemicontinuous_iff_isClosed_preimage, preimage_comp, isClosed_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

theorem LowerSemicontinuousWithinAt.sup
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x ↦ f x ⊔ g x) s a := by
  intro b hb
  simp only [lt_sup_iff] at hb ⊢
  rcases hb with hb | hb
  · filter_upwards [hf b hb] with x using Or.intro_left _
  · filter_upwards [hg b hb] with x using Or.intro_right _

theorem LowerSemicontinuousAt.sup
    (hf : LowerSemicontinuousAt f a) (hg : LowerSemicontinuousAt g a) :
    LowerSemicontinuousAt (fun x ↦ f x ⊔ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.sup hg

theorem LowerSemicontinuousOn.sup
    (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s := fun a ha ↦
  (hf a ha).sup (hg a ha)

theorem LowerSemicontinuous.sup
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun x ↦ f x ⊔ g x := fun a ↦
  (hf a).sup (hg a)

theorem LowerSemicontinuousWithinAt.inf
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x ↦ f x ⊓ g x) s a := by
  intro b hb
  simp only [lt_inf_iff] at hb ⊢
  exact Eventually.and (hf b hb.1) (hg b hb.2)

theorem LowerSemicontinuousAt.inf
    (hf : LowerSemicontinuousAt f a) (hg : LowerSemicontinuousAt g a) :
    LowerSemicontinuousAt (fun x ↦ f x ⊓ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.inf hg

theorem LowerSemicontinuousOn.inf
    (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun x ↦ f x ⊓ g x) s := fun a ha ↦
  (hf a ha).inf (hg a ha)

theorem LowerSemicontinuous.inf (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun x ↦ f x ⊓ g x := fun a ↦
  (hf a).inf (hg a)

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set. -/
theorem LowerSemicontinuousOn.exists_forall_le_of_isCompact {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuousOn f s) :
    ∃ a ∈ s, ∀ x ∈ s, f a ≤ f x := by
  haveI : Nonempty α := ⟨ne_s.choose⟩
  haveI : Nonempty s := ⟨⟨ne_s.choose, ne_s.choose_spec⟩⟩
  let φ : β → Filter α := fun b ↦ 𝓟 (s ∩ f ⁻¹' Iic b)
  let ℱ : Filter α := ⨅ a : s, φ (f a)
  have : ℱ.NeBot := by
    refine' iInf_neBot_of_directed _ _
    · change Directed GE.ge (fun x ↦ (φ ∘ (fun (a : s) ↦ f ↑a)) x)
      refine' Directed.mono_comp GE.ge _ _
      · intro x y hxy
        refine'
          principal_mono.mpr (inter_subset_inter_right _ (preimage_mono <| Iic_subset_Iic.mpr hxy))
      · apply IsTotal.directed
    · intro x
      have : (pure x : Filter α) ≤ φ (f x) := le_principal_iff.mpr ⟨x.2, le_refl (f x)⟩
      exact neBot_of_le this
  have hℱs : ℱ ≤ 𝓟 s :=
    iInf_le_of_le ⟨ne_s.choose, ne_s.choose_spec⟩ (principal_mono.mpr <| inter_subset_left)
  have hℱ : ∀ x ∈ s, ∀ᶠ y in ℱ, f y ≤ f x := fun x hx ↦
    mem_iInf_of_mem ⟨x, hx⟩ (by simp only [mem_principal]; apply inter_subset_right)
  obtain ⟨a, ha, h⟩ := hs hℱs
  letI : (𝓝 a ⊓ ℱ).NeBot := h
  refine' ⟨a, ha, fun x hx ↦ le_of_not_gt fun hxa ↦ _⟩
  suffices ∀ᶠ _ in 𝓝 a ⊓ ℱ, False by rwa [eventually_const] at this
  filter_upwards [(hf a ha (f x) hxa).filter_mono (inf_le_inf_left _ hℱs),
    (hℱ x hx).filter_mono (inf_le_right : 𝓝 a ⊓ ℱ ≤ ℱ)] using fun y h₁ h₂ ↦ not_le_of_gt h₁ h₂

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set. -/
theorem LowerSemicontinuousOn.exists_isMinOn {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuousOn f s) :
    ∃ a ∈ s, IsMinOn f s a :=
  hf.exists_forall_le_of_isCompact ne_s hs

/-- A lower semicontinuous function is bounded below on a compact set. -/
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

theorem UpperSemicontinuousWithinAt.inf
    (hf : UpperSemicontinuousWithinAt f s a) (hg : UpperSemicontinuousWithinAt g s a) :
    UpperSemicontinuousWithinAt (fun x ↦ f x ⊓ g x) s a :=
  LowerSemicontinuousWithinAt.sup (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousAt.inf
    (hf : UpperSemicontinuousAt f a) (hg : UpperSemicontinuousAt g a) :
    UpperSemicontinuousAt (fun x ↦ f x ⊓ g x) a :=
  LowerSemicontinuousAt.sup (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousOn.inf
    (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun x ↦ f x ⊓ g x) s :=
  LowerSemicontinuousOn.sup (β := βᵒᵈ) hf hg

theorem UpperSemicontinuous.inf (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous (fun x ↦ f x ⊓ g x) :=
  LowerSemicontinuous.sup (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousWithinAt.sup
    (hf : UpperSemicontinuousWithinAt f s a) (hg : UpperSemicontinuousWithinAt g s a) :
    UpperSemicontinuousWithinAt (fun x ↦ f x ⊔ g x) s a :=
  LowerSemicontinuousWithinAt.inf (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousAt.sup
    (hf : UpperSemicontinuousAt f a) (hg : UpperSemicontinuousAt g a) :
    UpperSemicontinuousAt (fun x ↦ f x ⊔ g x) a :=
  LowerSemicontinuousAt.inf (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousOn.sup
    (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun x ↦ f x ⊔ g x) s :=
  LowerSemicontinuousOn.inf (β := βᵒᵈ) hf hg

theorem UpperSemicontinuous.sup (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous fun x ↦ f x ⊔ g x :=
  LowerSemicontinuous.inf (β := βᵒᵈ) hf hg

variable {γ : Type*} [TopologicalSpace γ] {g : γ → α} {x : γ} {t : Set γ}

theorem UpperSemicontinuousWithinAt.comp
    (hf : UpperSemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    UpperSemicontinuousWithinAt (f ∘ g) t x :=
  LowerSemicontinuousWithinAt.comp (β := βᵒᵈ) hf hg hg'

theorem UpperSemicontinuousAt.comp
    (hf : UpperSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    UpperSemicontinuousAt (f ∘ g) x :=
  LowerSemicontinuousAt.comp (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousOn.comp
    (hf : UpperSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    UpperSemicontinuousOn (f ∘ g) t :=
  LowerSemicontinuousOn.comp (β := βᵒᵈ) hf hg hg'

theorem UpperSemicontinuous.comp
    (hf : UpperSemicontinuous f) (hg : Continuous g) : UpperSemicontinuous (f ∘ g) :=
  LowerSemicontinuous.comp (β := βᵒᵈ) hf hg

theorem upperSemicontinuousOn_iff_restrict {s : Set α} :
    UpperSemicontinuousOn f s ↔ UpperSemicontinuous (s.restrict f) :=
  lowerSemicontinuousOn_iff_restrict (β := βᵒᵈ)

theorem upperSemicontinuousOn_iff_preimage_Iio :
    UpperSemicontinuousOn f s ↔ ∀ b, ∃ u : Set α, IsOpen u ∧ s ∩ f ⁻¹' Set.Iio b = s ∩ u :=
  lowerSemicontinuousOn_iff_preimage_Ioi (β := βᵒᵈ)

theorem upperSemicontinuousOn_iff_preimage_Ici :
    UpperSemicontinuousOn f s ↔ ∀ b, ∃ v : Set α, IsClosed v ∧ s ∩ f ⁻¹' Set.Ici b = s ∩ v :=
  lowerSemicontinuousOn_iff_preimage_Iic (β := βᵒᵈ)

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set. -/
theorem UpperSemicontinuousOn.exists_forall_ge_of_isCompact {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : ∃ a ∈ s, ∀ x ∈ s, f x ≤ f a :=
  LowerSemicontinuousOn.exists_forall_le_of_isCompact (β := βᵒᵈ) ne_s hs hf

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set. -/
theorem UpperSemicontinuousOn.exists_isMaxOn {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) :
    ∃ a ∈ s, IsMaxOn f s a :=
  LowerSemicontinuousOn.exists_isMinOn (β := βᵒᵈ) ne_s hs hf

/-- An upper semicontinuous function is bounded above on a compact set. -/
theorem UpperSemicontinuousOn.bddAbove_of_isCompact [Nonempty β] {s : Set α}
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : BddAbove (f '' s) :=
  LowerSemicontinuousOn.bddBelow_of_isCompact (β := βᵒᵈ) hs hf

end UpperSemicontinuous

end LinearOrder

section CompleteLinearOrder

variable {β α : Type*} [TopologicalSpace α] {f : α → β} {s : Set α}

variable [CompleteLinearOrder β]

section LowerSemicontinuous

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set. -/
theorem LowerSemicontinuousOn.exists_iInf₂_of_isCompact (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuousOn f s) :
    ∃ a ∈ s, f a = ⨅ x ∈ s, f x := by
  obtain ⟨a, ha, ha_le⟩ := LowerSemicontinuousOn.exists_forall_le_of_isCompact ne_s hs hf
  use a, ha, le_antisymm (le_iInf₂_iff.mpr ha_le) (iInf₂_le a ha)

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set -/
theorem LowerSemicontinuous.exists_iInf₂_of_isCompact (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuous f) :
    ∃ a ∈ s, f a = ⨅ x ∈ s, f x :=
  (hf.lowerSemicontinuousOn s).exists_iInf₂_of_isCompact ne_s hs

variable {ι : Type*} {f : ι → α → β} {a : α} {I : Set ι}

theorem lowerSemicontinuousWithinAt_iSup₂
    (hf : ∀ i ∈ I, LowerSemicontinuousWithinAt (f i) s a) :
    LowerSemicontinuousWithinAt (fun x ↦ ⨆ i ∈ I, f i x) s a := by
  intro b hb
  simp only [lt_iSup_iff] at hb ⊢
  obtain ⟨i, hi, hb⟩ := hb
  apply Filter.Eventually.mp (hf i hi b hb)
  apply Filter.Eventually.of_forall
  intro x hx
  use i, hi, hx

theorem lowerSemicontinuousAt_iSup₂ (hf : ∀ i ∈ I, LowerSemicontinuousAt (f i) a) :
    LowerSemicontinuousAt (fun x ↦ ⨆ i ∈ I, f i x) a := by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_iSup₂ hf

theorem lowerSemicontinuousOn_iSup₂ (hf : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x ↦ ⨆ i ∈ I, f i x) s := fun a ha ↦
  lowerSemicontinuousWithinAt_iSup₂ (fun i hi ↦ hf i hi a ha)

theorem lowerSemicontinuous_iSup₂ (hf : ∀ i ∈ I, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x ↦ ⨆ i ∈ I, f i x := fun a ha ↦
  lowerSemicontinuousAt_iSup₂ (fun i hi ↦ hf i hi a) ha

theorem lowerSemicontinuousWithinAt_iInf₂ (hI : I.Finite)
    (hf : ∀ i ∈ I, LowerSemicontinuousWithinAt (f i) s a) :
    LowerSemicontinuousWithinAt (fun x ↦ ⨅ i ∈ I, f i x) s a := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp [lowerSemicontinuousWithinAt_const]
  | @insert i J hiJ hJ hrec =>
    simp only [iInf_insert]
    apply LowerSemicontinuousWithinAt.inf
    · exact hf i (by exact mem_insert i J)
    · apply hrec
      intro j hj
      apply hf j (mem_insert_of_mem i hj)

theorem lowerSemicontinuousAt_iInf₂ (hI : I.Finite)
    (hf : ∀ i ∈ I, LowerSemicontinuousAt (f i) a) :
    LowerSemicontinuousAt (fun x ↦ ⨅ i ∈ I, f i x) a := by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_iInf₂ hI hf

theorem lowerSemicontinuousOn_iInf₂
    (hI : I.Finite) (hf : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x ↦ ⨅ i ∈ I, f i x) s := fun a ha ↦
  lowerSemicontinuousWithinAt_iInf₂ hI (fun i hi ↦ hf i hi a ha)

theorem lowerSemicontinuous_iInf₂ (hI : I.Finite)
    (hf : ∀ i ∈ I, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x ↦ ⨅ i ∈ I, f i x := fun a ha ↦
  lowerSemicontinuousAt_iInf₂ hI (fun i hi ↦ hf i hi a) ha

end LowerSemicontinuous

section UpperSemicontinuous

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set. -/
theorem UpperSemicontinuousOn.exists_iSup₂_of_isCompact (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) :
    ∃ a ∈ s, f a = ⨆ x ∈ s, f x :=
  LowerSemicontinuousOn.exists_iInf₂_of_isCompact (β := βᵒᵈ) ne_s hs hf

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set. -/
theorem UpperSemicontinuous.exists_iSup₂_of_isCompact (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuous f) :
    ∃ a ∈ s, f a = ⨆ x ∈ s, f x :=
  LowerSemicontinuous.exists_iInf₂_of_isCompact (β := βᵒᵈ) ne_s hs hf

variable {ι : Type*} {f : ι → α → β} {s : Set α} {a : α} {I : Set ι}

theorem upperSemicontinuousWithinAt_iInf₂
    (hf : ∀ i ∈ I, UpperSemicontinuousWithinAt (f i) s a) :
    UpperSemicontinuousWithinAt (fun x ↦ ⨅ i ∈ I, f i x) s a :=
  lowerSemicontinuousWithinAt_iSup₂ (β := βᵒᵈ) hf

theorem upperSemicontinuousAt_iInf₂
    (hf : ∀ i ∈ I, UpperSemicontinuousAt (f i) a) :
    UpperSemicontinuousAt (fun x ↦ ⨅ i ∈ I, f i x) a :=
  lowerSemicontinuousAt_iSup₂ (β := βᵒᵈ) hf

theorem upperSemicontinuousOn_iInf₂
    (hf : ∀ i ∈ I, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x ↦ ⨅ i ∈ I, f i x) s :=
  lowerSemicontinuousOn_iSup₂ (β := βᵒᵈ) hf

theorem upperSemicontinuous_iInf₂
    (hf : ∀ i ∈ I, UpperSemicontinuous (f i)) :
    UpperSemicontinuous (fun x ↦ ⨅ i ∈ I, f i x) :=
  lowerSemicontinuous_iSup₂ (β := βᵒᵈ) hf

theorem upperSemicontinuousWithinAt_iSup₂ (hI : I.Finite)
    (hf : ∀ i ∈ I, UpperSemicontinuousWithinAt (f i) s a) :
    UpperSemicontinuousWithinAt (fun x ↦ ⨆ i ∈ I, f i x) s a :=
  lowerSemicontinuousWithinAt_iInf₂ (β := βᵒᵈ) hI hf

theorem upperSemicontinuousAt_iSup₂ (hI : I.Finite)
    (hf : ∀ i ∈ I, UpperSemicontinuousAt (f i) a) :
    UpperSemicontinuousAt (fun x ↦ ⨆ i ∈ I, f i x) a :=
  lowerSemicontinuousAt_iInf₂ (β := βᵒᵈ) hI hf

theorem upperSemicontinuousOn_iSup₂ (hI : I.Finite)
    (hf : ∀ i ∈ I, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x ↦ ⨆ i ∈ I, f i x) s :=
  lowerSemicontinuousOn_iInf₂ (β := βᵒᵈ) hI hf

theorem upperSemicontinuous_iSup₂ (hI : I.Finite)
    (hf : ∀ i ∈ I, UpperSemicontinuous (f i)) :
    UpperSemicontinuous (fun x ↦ ⨆ i ∈ I, f i x) :=
  lowerSemicontinuous_iInf₂ (β := βᵒᵈ) hI hf

end UpperSemicontinuous

-- Lemmas which depend on two topologies

section LowerSemicontinuous

variable {ι : Type*} {f : ι → α → β} {s : Set α} {a : α}
    [TopologicalSpace ι] {I : Set ι}

theorem lowerSemicontinuousOn_iInf₂_of_isProper
    {f : α → β}
    {γ : Type*} [TopologicalSpace γ] {g : α → γ} (hg : IsProperMap g)
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuousOn (fun z ↦ ⨅ x ∈ g ⁻¹' {z}, f x) (range g) := by
  intro z hz b hb
  dsimp at hb
  have hinf (z) (hz : z ∈ range g) :
    ∃ a ∈ g ⁻¹' {z}, f a = ⨅ x ∈ g ⁻¹' {z}, f x := by
    apply LowerSemicontinuousOn.exists_iInf₂_of_isCompact
    · exact hz
    · apply hg.isCompact_preimage isCompact_singleton
    · exact LowerSemicontinuous.lowerSemicontinuousOn hf (g ⁻¹' {z})
  have (a) (ha : a ∈ g ⁻¹' {z}) :
    ∃ u, IsOpen u ∧ a ∈ u ∧ ∀ x ∈ u, b < f x := by
    specialize hf a b ?_
    · obtain ⟨m, hm, hm'⟩ := hinf z hz
      apply lt_of_lt_of_le hb
      exact biInf_le f ha
    · rw [Filter.eventually_iff, mem_nhds_iff] at hf
      obtain ⟨u, hu, hu', hau⟩ := hf
      exact ⟨u, hu', hau, hu⟩
  let v := ⋃ (a : α) (ha : a ∈ g ⁻¹' {z}), (this a ha).choose
  have hv : IsOpen v := sorry
  have hvz : g ⁻¹' {z} ⊆ v := sorry
  have hv' : IsOpen (g '' vᶜ)ᶜ := sorry
  have hv'z : z ∈ (g '' vᶜ)ᶜ := sorry
  rw [Filter.eventually_iff, mem_nhdsWithin]
  use (g '' vᶜ)ᶜ, hv', hv'z
  rintro c ⟨hc, hc'⟩
  dsimp
  obtain ⟨m, hm, hm'⟩ := hinf c hc'
  rw [← hm']
  simp only [mem_preimage, mem_singleton_iff] at hm
  simp only [mem_compl_iff, mem_image, not_exists, not_and] at hc
  simp_rw [not_imp_not] at hc
  specialize hc m hm
  simp [v] at hc
  obtain ⟨i, hi, hc⟩ := hc
  exact ((this i hi).choose_spec.2.2 m hc)
  -- unfinished


theorem upperSemicontinuousOn_iSup₂_of_isProper
    {f : α → β}
    {γ : Type*} [TopologicalSpace γ] {g : α → γ} (hg : IsProperMap g)
    (hf : UpperSemicontinuous f) :
    UpperSemicontinuousOn (fun z ↦ ⨆ x ∈ g ⁻¹' {z}, f x) (range g) :=
  lowerSemicontinuousOn_iInf₂_of_isProper (β := βᵒᵈ) hg hf


end LowerSemicontinuous

end CompleteLinearOrder

end Semicontinuity


