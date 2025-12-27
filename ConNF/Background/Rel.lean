import Mathlib.Data.Rel
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Preorder.Chain
import VerifiedAgora.tagger

open Set
open scoped symmDiff

namespace Rel

variable {α β γ : Type _}

def field (r : Rel α α) : Set α := by sorry


@[mk_iff]
structure Injective (r : Rel α β) : Prop where
  injective : ∀ ⦃x₁ x₂ y⦄, r x₁ y → r x₂ y → x₁ = x₂

@[mk_iff]
structure Coinjective (r : Rel α β) : Prop where
  coinjective : ∀ ⦃y₁ y₂ x⦄, r x y₁ → r x y₂ → y₁ = y₂

@[mk_iff]
structure Surjective (r : Rel α β) : Prop where
  surjective : ∀ y, ∃ x, r x y

@[mk_iff]
structure Cosurjective (r : Rel α β) : Prop where
  cosurjective : ∀ x, ∃ y, r x y

@[mk_iff]
structure Functional (r : Rel α β) : Prop extends Coinjective r, Cosurjective r

@[mk_iff]
structure Cofunctional (r : Rel α β) : Prop extends Injective r, Surjective r

@[mk_iff]
structure OneOne (r : Rel α β) : Prop extends Injective r, Coinjective r

@[mk_iff]
structure Bijective (r : Rel α β) : Prop extends Functional r, Cofunctional r

@[mk_iff]
structure CodomEqDom (r : Rel α α) : Prop where
  codom_eq_dom : r.codom = r.dom

@[mk_iff]
structure Permutative (r : Rel α α) : Prop extends OneOne r, CodomEqDom r

theorem CodomEqDom.dom_union_codom {r : Rel α α} (h : r.CodomEqDom) :
    r.dom ∪ r.codom = r.dom := by
  rw [h.codom_eq_dom, union_self]

theorem CodomEqDom.mem_dom {r : Rel α α} (h : r.CodomEqDom) {x y : α} (hxy : r x y) :
    y ∈ r.dom := by
  rw [← h.codom_eq_dom]
  exact ⟨x, hxy⟩

theorem CodomEqDom.mem_codom {r : Rel α α} (h : r.CodomEqDom) {x y : α} (hxy : r x y) :
    x ∈ r.codom := by
  rw [h.codom_eq_dom]
  exact ⟨y, hxy⟩

/-- An elementary description of the property `CodomEqDom`. -/
theorem codomEqDom_iff' (r : Rel α α) :
    r.CodomEqDom ↔ (∀ x y, r x y → ∃ z, r y z) ∧ (∀ x y, r x y → ∃ z, r z x) := by
  constructor
  · rintro ⟨h⟩
    rw [Set.ext_iff] at h
    constructor
    · intro x y hxy
      exact (h y).mp ⟨x, hxy⟩
    · intro x y hxy
      exact (h x).mpr ⟨y, hxy⟩
  · rintro ⟨h₁, h₂⟩
    constructor
    ext x
    constructor
    · intro ⟨y, hxy⟩
      exact h₁ y x hxy
    · intro ⟨y, hxy⟩
      exact h₂ x y hxy

theorem OneOne.inv {r : Rel α β} (h : r.OneOne) : r.inv.OneOne :=
  ⟨⟨h.coinjective⟩, ⟨h.injective⟩⟩

@[target] theorem inv_apply {r : Rel α β} {x : α} {y : β} :
    r.inv y x ↔ r x y := by sorry


@[target] theorem inv_injective : Function.Injective (inv : Rel α β → Rel β α) := by
  sorry


@[target] theorem inv_inj {r s : Rel α β} : r.inv = s.inv ↔ r = s := by sorry


@[target] theorem inv_injective_iff {r : Rel α β} :
    r.inv.Injective ↔ r.Coinjective := by sorry


@[target] theorem inv_coinjective_iff {r : Rel α β} :
    r.inv.Coinjective ↔ r.Injective := by sorry


@[target] theorem inv_surjective_iff {r : Rel α β} :
    r.inv.Surjective ↔ r.Cosurjective := by sorry


@[target] theorem inv_cosurjective_iff {r : Rel α β} :
    r.inv.Cosurjective ↔ r.Surjective := by sorry


@[target] theorem inv_functional_iff {r : Rel α β} :
    r.inv.Functional ↔ r.Cofunctional := by sorry


@[target] theorem inv_cofunctional_iff {r : Rel α β} :
    r.inv.Cofunctional ↔ r.Functional := by sorry


@[target] theorem inv_dom {r : Rel α β} :
    r.inv.dom = r.codom := by sorry


@[target] theorem inv_codom {r : Rel α β} :
    r.inv.codom = r.dom := by sorry


@[target] theorem inv_image {r : Rel α β} {s : Set β} :
    r.inv.image s = r.preimage s := by sorry


@[target] theorem inv_preimage {r : Rel α β} {s : Set α} :
    r.inv.preimage s = r.image s := by sorry


theorem comp_inv {r : Rel α β} {s : Rel β γ} :
    (r.comp s).inv = s.inv.comp r.inv := by
  ext c a
  simp only [inv, flip, comp]
  tauto

theorem Injective.image_injective {r : Rel α β} (h : r.Injective) {s t : Set α}
    (hs : s ⊆ r.dom) (ht : t ⊆ r.dom) (hst : r.image s = r.image t) : s = t := by
  rw [Set.ext_iff] at hst ⊢
  intro x
  constructor
  · intro hx
    obtain ⟨y, hxy⟩ := hs hx
    obtain ⟨z, hz, hzy⟩ := (hst y).mp ⟨x, hx, hxy⟩
    cases h.injective hxy hzy
    exact hz
  · intro hx
    obtain ⟨y, hxy⟩ := ht hx
    obtain ⟨z, hz, hzy⟩ := (hst y).mpr ⟨x, hx, hxy⟩
    cases h.injective hxy hzy
    exact hz

@[target] theorem subset_image_of_preimage_subset {r : Rel α β} {s : Set β} (hs : s ⊆ r.codom) (t : Set α) :
    r.preimage s ⊆ t → s ⊆ r.image t := by
  sorry


theorem Injective.preimage_subset_of_subset_image {r : Rel α β} (h : r.Injective)
    (s : Set β) (t : Set α) :
    s ⊆ r.image t → r.preimage s ⊆ t := by
  rintro hst x ⟨y, hy, hxy⟩
  obtain ⟨z, hz, hzy⟩ := hst hy
  cases h.injective hzy hxy
  exact hz

theorem Injective.preimage_subset_iff_subset_image {r : Rel α β} (h : r.Injective)
    (s : Set β) (hs : s ⊆ r.codom) (t : Set α) :
    r.preimage s ⊆ t ↔ s ⊆ r.image t :=
  ⟨subset_image_of_preimage_subset hs t, preimage_subset_of_subset_image h s t⟩

theorem OneOne.preimage_eq_iff_image_eq {r : Rel α β} (h : r.OneOne)
    {s : Set β} (hs : s ⊆ r.codom) {t : Set α} (ht : t ⊆ r.dom) :
    r.preimage s = t ↔ r.image t = s := by
  have h₁ := h.preimage_subset_iff_subset_image s hs t
  have h₂ := h.inv.preimage_subset_iff_subset_image t ht s
  rw [preimage_inv, inv_image] at h₂
  rw [subset_antisymm_iff, subset_antisymm_iff, h₁, h₂, and_comm]

theorem CodomEqDom.inv {r : Rel α α} (h : r.CodomEqDom) : r.inv.CodomEqDom := by
  rw [codomEqDom_iff] at h ⊢
  exact h.symm

theorem Permutative.inv {r : Rel α α} (h : r.Permutative) : r.inv.Permutative :=
  ⟨h.toOneOne.inv, h.toCodomEqDom.inv⟩

theorem Permutative.inv_dom {r : Rel α α} (h : r.Permutative) : r.inv.dom = r.dom :=
  h.codom_eq_dom

theorem Injective.comp {r : Rel α β} {s : Rel β γ} (hr : r.Injective) (hs : s.Injective) :
    (r.comp s).Injective := by
  constructor
  rintro a₁ a₂ c ⟨b₁, hr₁, hs₁⟩ ⟨b₂, hr₂, hs₂⟩
  cases hs.injective hs₁ hs₂
  exact hr.injective hr₁ hr₂

theorem Coinjective.comp {r : Rel α β} {s : Rel β γ} (hr : r.Coinjective) (hs : s.Coinjective) :
    (r.comp s).Coinjective := by
  rw [← inv_injective_iff, comp_inv]
  exact Injective.comp (inv_injective_iff.mpr hs) (inv_injective_iff.mpr hr)

theorem Injective.mono {r s : Rel α β} (hs : s.Injective) (h : r ≤ s) :
    r.Injective := by
  constructor
  intro a₁ a₂ b h₁ h₂
  exact hs.injective (h a₁ b h₁) (h a₂ b h₂)

theorem Coinjective.mono {r s : Rel α β} (hs : s.Coinjective) (h : r ≤ s) :
    r.Coinjective := by
  constructor
  intro b₁ b₂ a h₁ h₂
  exact hs.coinjective (h a b₁ h₁) (h a b₂ h₂)

theorem OneOne.mono {r s : Rel α β} (hs : s.OneOne) (h : r ≤ s) :
    r.OneOne :=
  ⟨hs.toInjective.mono h, hs.toCoinjective.mono h⟩

/-- An alternative spelling of `Rel.graph` that is useful for proving inequalities of cardinals. -/
def graph' (r : Rel α β) : Set (α × β) :=
  r.uncurry

theorem le_of_graph'_subset {r s : Rel α β} (h : r.graph' ⊆ s.graph') :
    r ≤ s :=
  λ x y h' ↦ mem_of_subset_of_mem (a := (x, y)) h h'

theorem graph'_subset_of_le {r s : Rel α β} (h : r ≤ s) :
    r.graph' ⊆ s.graph' :=
  λ z ↦ h z.1 z.2

theorem graph'_subset_iff {r s : Rel α β} :
    r.graph' ⊆ s.graph' ↔ r ≤ s :=
  ⟨le_of_graph'_subset, graph'_subset_of_le⟩

theorem graph'_injective :
    Function.Injective (Rel.graph' : Rel α β → Set (α × β)) :=
  λ _ _ h ↦ le_antisymm (le_of_graph'_subset h.le) (le_of_graph'_subset h.symm.le)

@[target] theorem image_dom {r : Rel α β} :
    r.image r.dom = r.codom := by sorry


@[target] theorem preimage_codom {r : Rel α β} :
    r.preimage r.codom = r.dom := by sorry


@[target] theorem preimage_subset_dom (r : Rel α β) (t : Set β) :
    r.preimage t ⊆ r.dom := by
  sorry


@[target] theorem image_subset_codom (r : Rel α β) (s : Set α) :
    r.image s ⊆ r.codom := by sorry


@[target] theorem image_empty_of_disjoint_dom {r : Rel α β} {s : Set α} (h : Disjoint r.dom s) :
    r.image s = ∅ := by
  sorry


@[target] theorem image_eq_of_inter_eq {r : Rel α β} {s t : Set α} (h : s ∩ r.dom = t ∩ r.dom) :
    r.image s = r.image t := by
  sorry


theorem Injective.image_diff {r : Rel α β} (h : r.Injective) (s t : Set α) :
    r.image (s \ t) = r.image s \ r.image t := by
  ext y
  constructor
  · rintro ⟨x, hx₁, hx₂⟩
    refine ⟨⟨x, hx₁.1, hx₂⟩, ?_⟩
    rintro ⟨z, hz₁, hz₂⟩
    cases h.injective hx₂ hz₂
    exact hx₁.2 hz₁
  · rintro ⟨⟨x, hx₁, hx₂⟩, hy⟩
    refine ⟨x, ⟨hx₁, ?_⟩, hx₂⟩
    intro hx
    exact hy ⟨x, hx, hx₂⟩

theorem Injective.image_symmDiff {r : Rel α β} (h : r.Injective) (s t : Set α) :
    r.image (s ∆ t) = r.image s ∆ r.image t := by
  rw [Set.symmDiff_def, Set.symmDiff_def, image_union, h.image_diff, h.image_diff]

@[target] theorem image_eq_of_le_of_le {r s : Rel α β} (h : r ≤ s) {t : Set α} (ht : ∀ x ∈ t, s x ≤ r x) :
    r.image t = s.image t := by
  sorry


@[target] theorem sup_inv {r s : Rel α β} :
    (r ⊔ s).inv = r.inv ⊔ s.inv := by sorry


@[target] theorem sup_apply {r s : Rel α β} {x : α} {y : β} :
    (r ⊔ s) x y ↔ r x y ∨ s x y := by sorry


@[target] theorem sup_dom {r s : Rel α β} :
    (r ⊔ s).dom = r.dom ∪ s.dom := by
  sorry


@[target] theorem sup_codom {r s : Rel α β} :
    (r ⊔ s).codom = r.codom ∪ s.codom := by sorry


@[target] theorem sup_image {r s : Rel α β} (t : Set α) :
    (r ⊔ s).image t = r.image t ∪ s.image t := by
  sorry


@[target] theorem sup_injective {r s : Rel α β} (hr : r.Injective) (hs : s.Injective)
    (h : Disjoint r.codom s.codom) : (r ⊔ s).Injective := by
  sorry


@[target] theorem sup_coinjective {r s : Rel α β} (hr : r.Coinjective) (hs : s.Coinjective)
    (h : Disjoint r.dom s.dom) : (r ⊔ s).Coinjective := by sorry


@[target] theorem sup_oneOne {r s : Rel α β} (hr : r.OneOne) (hs : s.OneOne)
    (h₁ : Disjoint r.dom s.dom) (h₂ : Disjoint r.codom s.codom) : (r ⊔ s).OneOne := by sorry


@[target] theorem sup_codomEqDom {r s : Rel α α} (hr : r.CodomEqDom) (hs : s.CodomEqDom) :
    (r ⊔ s).CodomEqDom := by sorry


@[target] theorem sup_permutative {r s : Rel α α} (hr : r.Permutative) (hs : s.Permutative)
    (h : Disjoint r.dom s.dom) : (r ⊔ s).Permutative := by sorry


@[target] theorem inf_inv {r s : Rel α β} :
    (r ⊓ s).inv = r.inv ⊓ s.inv := by sorry


@[target] theorem inf_apply {r s : Rel α β} {x : α} {y : β} :
    (r ⊓ s) x y ↔ r x y ∧ s x y := by sorry


@[target] theorem inf_dom {r s : Rel α β} :
    (r ⊓ s).dom ⊆ r.dom ∩ s.dom := by
  sorry


@[target] theorem inf_codom {r s : Rel α β} :
    (r ⊓ s).codom ⊆ r.codom ∩ s.codom := by sorry


@[target] theorem inv_le_inv_iff {r s : Rel α β} :
    r.inv ≤ s.inv ↔ r ≤ s := by
  sorry


@[target] theorem iSup_apply_iff {T : Type _} {r : T → Rel α β} (x : α) (y : β) :
    (⨆ t, r t) x y ↔ ∃ t, r t x y := by
  sorry


@[target] theorem biSup_apply_iff {T : Type _} {r : T → Rel α β} {s : Set T} (x : α) (y : β) :
    (⨆ t ∈ s, r t) x y ↔ ∃ t ∈ s, r t x y := by
  sorry


@[target] theorem iSup_dom {T : Type _} (r : T → Rel α β) :
    (⨆ t, r t).dom = ⋃ t, (r t).dom := by
  sorry


@[target] theorem biSup_dom {T : Type _} (r : T → Rel α β) (s : Set T) :
    (⨆ t ∈ s, r t).dom = ⋃ t ∈ s, (r t).dom := by
  sorry


@[target] theorem isChain_inv {T : Type _} {r : T → Rel α β} (h : IsChain (· ≤ ·) (Set.range r)) :
    IsChain (· ≤ ·) (Set.range (λ t ↦ (r t).inv)) := by
  sorry


@[target] theorem iSup_inv {T : Type _} {r : T → Rel α β} :
    (⨆ t, (r t).inv) = (⨆ t, r t).inv := by
  sorry


@[target] theorem iSup_injective_of_isChain {T : Type _} {r : T → Rel α β}
    (h₁ : ∀ t, (r t).Injective) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Injective := by
  sorry


@[target] theorem iSup_coinjective_of_isChain {T : Type _} {r : T → Rel α β}
    (h₁ : ∀ t, (r t).Coinjective) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Coinjective := by
  sorry


@[target] theorem iSup_codomEqDom_of_isChain {T : Type _} {r : T → Rel α α} (h : ∀ t, (r t).CodomEqDom) :
    (⨆ t, r t).CodomEqDom := by
  sorry


@[target] theorem iSup_oneOne_of_isChain {T : Type _} {r : T → Rel α β}
    (h₁ : ∀ t, (r t).OneOne) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).OneOne := by sorry


@[target] theorem iSup_permutative_of_isChain {T : Type _} {r : T → Rel α α}
    (h₁ : ∀ t, (r t).Permutative) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Permutative := by sorry


@[target] theorem biSup_permutative_of_isChain {T : Type _} {r : T → Rel α α} {s : Set T}
    (h₁ : ∀ t ∈ s, (r t).Permutative) (h₂ : IsChain (· ≤ ·) (r '' s)) :
    (⨆ t ∈ s, r t).Permutative := by
  sorry


noncomputable def toFunction (r : Rel α β) (hr : r.Functional) : α → β :=
  λ a ↦ (hr.cosurjective a).choose

@[target] theorem toFunction_rel (r : Rel α β) (hr : r.Functional) (a : α) :
    r a (r.toFunction hr a) := by sorry


@[target] theorem toFunction_eq_iff (r : Rel α β) (hr : r.Functional) (a : α) (b : β) :
    r.toFunction hr a = b ↔ r a b := by
  sorry


noncomputable def toEquiv (r : Rel α β) (hr : r.Bijective) : α ≃ β where
  toFun := r.toFunction hr.toFunctional
  invFun := r.inv.toFunction (inv_functional_iff.mpr hr.toCofunctional)
  left_inv a := by
    rw [toFunction_eq_iff]
    exact toFunction_rel r _ a
  right_inv b := by
    rw [toFunction_eq_iff]
    exact toFunction_rel r.inv _ b

@[target] theorem toEquiv_rel (r : Rel α β) (hr : r.Bijective) (a : α) :
    r a (r.toEquiv hr a) := by sorry


@[target] theorem toEquiv_eq_iff (r : Rel α β) (hr : r.Bijective) (a : α) (b : β) :
    r.toEquiv hr a = b ↔ r a b := by sorry


@[target] theorem toFunction_image (r : Rel α β) (hr : r.Functional) (s : Set α) :
    r.toFunction hr '' s = r.image s := by
  sorry


@[target] theorem toEquiv_image (r : Rel α β) (hr : r.Bijective) (s : Set α) :
    r.toEquiv hr '' s = r.image s := by sorry


end Rel
