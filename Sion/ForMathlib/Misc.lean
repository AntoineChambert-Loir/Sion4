import Mathlib.Data.Real.EReal
import Mathlib.Topology.Connected.Clopen

/-!

# Miscellaneous lemmas to add to mathlib

-/

-- order.complete_lattice
theorem iInf₂_le_iff {α β : Type _} [CompleteLattice β] {f : α → β} {s : Set α} {b : β} :
    (⨅ x ∈ s, f x) ≤ b ↔ ∀ b', (∀ x ∈ s, b' ≤ f x) → b' ≤ b := by
  simp_rw [iInf_le_iff, le_iInf_iff]

theorem le_iSup₂_iff {α β : Type _} [CompleteLattice β] {f : α → β} {s : Set α} {b : β} :
    (b ≤ ⨆ x ∈ s, f x) ↔ ∀ b', (∀ x ∈ s, f x ≤ b') → b ≤ b' :=
  @iInf₂_le_iff α βᵒᵈ _ _ _ _

/- -- data.real.ereal
instance : DenselyOrdered EReal :=
  WithBot.denselyOrdered -/

-- topology.connected
-- This is essentially `is_preconnected_iff_subset_of_disjoint_closed`
theorem IsPreconnected.subset_or_subset_of_closed {α : Type _} [TopologicalSpace α] {s u v : Set α}
    (hu : IsClosed u) (hv : IsClosed v) (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v)
    (hs : IsPreconnected s) : s ⊆ u ∨ s ⊆ v := by
  apply (isPreconnected_iff_subset_of_disjoint_closed.mp hs) u v hu hv hsuv
  rw [Set.disjoint_iff_inter_eq_empty.mp huv, Set.inter_empty]

-- filter
variable {α : Type _}

namespace Filter

theorem Frequently.congr {f : Filter α} {p q : α → Prop} (h' : ∃ᶠ x in f, p x)
    (h : ∀ᶠ x in f, p x ↔ q x) : ∃ᶠ x in f, q x :=
  h'.mp (h.mono fun _ hx => hx.mp)

-- (Anatole) Do we need this variant ?
theorem frequently_congr' {α : Type _} (f : Filter α) (p q : α → Prop)
    (h : ∀ᶠ a : α in f, p a ↔ q a) : (∃ᶠ a in f, p a) ↔ ∃ᶠ a in f, q a :=
  frequently_congr h

theorem clusterPt_principal_subtype_iff_frequently {α : Type _} [TopologicalSpace α] {s t : Set α}
    (hst : s ⊆ t) {J : Set s} {a : ↥s} :
    ClusterPt a (Filter.principal J) ↔ ∃ᶠ x in nhdsWithin a t, ∃ h : x ∈ s, (⟨x, h⟩ : s) ∈ J := by
  rw [nhdsWithin_eq_map_subtype_coe (hst a.prop), Filter.frequently_map,
    clusterPt_principal_iff_frequently, inducing_subtype_val.nhds_eq_comap, Filter.frequently_comap,
    inducing_subtype_val.nhds_eq_comap, Filter.frequently_comap, Subtype.coe_mk]
  apply frequently_congr
  apply eventually_of_forall
  intro x
  simp only [Subtype.coe_mk, SetCoe.exists, exists_and_left, exists_eq_left]
  exact ⟨fun ⟨h, hx⟩ => ⟨hst h, h, hx⟩, fun ⟨_, hx⟩ => hx⟩

/-
-- Ancienne version
example {α : Type _} [TopologicalSpace α] {s t : Set α} (hst : s ⊆ t) {J : Set s} {a : ↥s} :
    ClusterPt a (Filter.principal J) ↔ ∃ᶠ x in nhdsWithin a t, ∃ h : x ∈ s, (⟨x, h⟩ : s) ∈ J :=
  by
  simp only [clusterPt_principal_iff_frequently, Filter.Frequently, not_iff_not, Filter.Eventually,
    mem_nhds_iff, mem_nhdsWithin]
  simp only [exists_prop, not_exists]
  constructor
  · rintro ⟨v, hv_subset, hv_open, hav⟩
    obtain ⟨u, hu, hut⟩ := inducing_subtype_val.isOpen_iff.mp hv_open
    use u
    apply And.intro hu
    simp only [← hut, Set.mem_preimage] at hav
    apply And.intro hav
    intro x hx
    simp only [Set.mem_setOf_eq]
    intro hxs
    apply hv_subset
    rw [← hut]
    rw [Set.mem_preimage]
    rw [Set.mem_inter_iff] at hx ; exact hx.1
  · rintro ⟨u, hu_open, hat, hut_subset⟩
    use (fun x ↦ ↑x) ⁻¹' u
    constructor
    rintro ⟨x, hx⟩ hx'; rw [Set.mem_preimage] at hx'
    apply hut_subset
    exact ⟨hx', hst hx⟩
    exact ⟨isOpen_induced hu_open, hat⟩

-- Essayons de faire plus simple (pas convaincant!)
example {α : Type _} [TopologicalSpace α] (s t : Set α) (hst : s ⊆ t) (J : Set s) (a : ↥s) :
    ClusterPt a (Filter.principal J) ↔ ∃ᶠ x in nhdsWithin a t, ∃ h : x ∈ s, (⟨x, h⟩ : s) ∈ J :=
  by
  simp only [clusterPt_principal_iff_frequently, Filter.Frequently, not_iff_not, Filter.Eventually,
    mem_nhds_iff, mem_nhdsWithin]
  simp only [exists_prop, not_exists]
  simp_rw [inducing_subtype_val.isOpen_iff]
  simp_rw [and_comm]; simp_rw [← and_assoc]
  simp_rw [← exists_and_left]
  rw [exists_comm]
  apply exists_congr; intro u
  simp_rw [and_comm]; simp_rw [and_assoc]; simp_rw [exists_and_left]
  rw [and_congr_right_iff]
  intro hu_open
  constructor
  · rintro ⟨x, hux, hax, hx⟩
    simp only [← hux, Set.mem_preimage] at hax
    apply And.intro hax
    intro y hyut hys
    apply hx; simp only [← hux, Set.mem_preimage]; exact hyut.1
  · rintro ⟨hau, hut⟩
    use (fun x ↦ ↑x) ⁻¹' u
    apply And.intro rfl
    rw [Set.mem_preimage]; apply And.intro hau
    intro y; rw [Set.mem_preimage]; intro hy
    simp; rw [← Subtype.coe_eta y y.prop]
    apply hut
    exact ⟨hy, hst y.prop⟩

-- si on enlève le grand ensemble (c'est pas mieux)
theorem clusterPt_principal_subtype_iff_frequently' {α : Type _} [TopologicalSpace α] (s : Set α)
    (J : Set s) (a : ↥s) :
    ClusterPt a (Filter.principal J) ↔ ∃ᶠ x : α in nhdsWithin a s, ∃ h : x ∈ s, (⟨x, h⟩ : s) ∈ J :=
  by
  simp only [clusterPt_principal_iff_frequently, Filter.Frequently, not_iff_not, Filter.Eventually,
    mem_nhds_iff, mem_nhdsWithin]
  simp only [exists_prop, not_exists]
  constructor
  · rintro ⟨v, hv_subset, hv_open, hav⟩
    obtain ⟨u, hu, hut⟩ := inducing_subtype_val.isOpen_iff.mp hv_open
    use u
    apply And.intro hu
    simp only [← hut, Set.mem_preimage] at hav
    apply And.intro hav
    intro x hx
    simp only [Set.mem_setOf_eq]
    intro hxs
    apply hv_subset
    rw [← hut]
    rw [Set.mem_preimage]
    rw [Set.mem_inter_iff] at hx ; exact hx.1
  · rintro ⟨u, hu_open, hat, hut_subset⟩
    use coe ⁻¹' u
    constructor
    rintro ⟨x, hx⟩ hx'; rw [Set.mem_preimage] at hx'
    apply hut_subset
    exact ⟨hx', hx⟩
    exact ⟨isOpen_induced hu_open, hat⟩
#align filter.cluster_pt_principal_subtype_iff_frequently' Filter.clusterPt_principal_subtype_iff_frequently'
-/

end Filter

-- Not needed actually...
-- TODO: which file ?
theorem min_mem_of_mem {α : Type _} [LinearOrder α] {a b : α} {s : Set α} (ha : a ∈ s)
    (hb : b ∈ s) : min a b ∈ s := by rw [min_def] ; split_ifs <;> assumption

-- TODO: which file ?
theorem max_mem_of_mem {α : Type _} [LinearOrder α] {a b : α} {s : Set α} (ha : a ∈ s)
    (hb : b ∈ s) : max a b ∈ s := by rw [max_def] ; split_ifs <;> assumption

-- TODO: which file ?
theorem inf_mem_of_mem {α : Type _} [LinearOrder α] {a b : α} {s : Set α} (ha : a ∈ s)
    (hb : b ∈ s) : a ⊓ b ∈ s := min_mem_of_mem ha hb

-- TODO: which file ?
theorem sup_mem_of_mem {α : Type _} [LinearOrder α] {a b : α} {s : Set α} (ha : a ∈ s)
    (hb : b ∈ s) : a ⊔ b ∈ s := max_mem_of_mem ha hb
