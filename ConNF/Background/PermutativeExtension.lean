import ConNF.Background.Cardinal
import ConNF.Background.Rel
import VerifiedAgora.tagger

noncomputable section
open Cardinal

namespace Rel

variable {α β : Type _}

/-- TODO: Fix the paper version of this. -/
structure OrbitRestriction (s : Set α) (β : Type _) where
  sandbox : Set α
  sandbox_disjoint : Disjoint s sandbox
  categorise : α → β
  catPerm : Equiv.Perm β
  le_card_categorise (b : β) : max ℵ₀ #s ≤ #(sandbox ∩ categorise ⁻¹' {b} : Set α)

@[target] theorem le_card_categorise {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β) :
    #((r.dom ∪ r.codom : Set α) × ℕ) ≤ #(R.sandbox ∩ R.categorise ⁻¹' {b} : Set α) := by
  sorry


def catInj {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β) :
    (r.dom ∪ r.codom : Set α) × ℕ ↪ (R.sandbox ∩ R.categorise ⁻¹' {b} : Set α) := by sorry


@[target] theorem catInj_mem_sandbox {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β)
    (x : (r.dom ∪ r.codom : Set α) × ℕ) :
    (catInj R b x : α) ∈ R.sandbox := by sorry


@[target] theorem categorise_catInj {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β)
    (x : (r.dom ∪ r.codom : Set α) × ℕ) :
    R.categorise (catInj R b x) = b := by sorry


@[target] theorem catInj_ne_of_mem {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β)
    (x : (r.dom ∪ r.codom : Set α) × ℕ) (a : α) (ha : a ∈ r.dom ∪ r.codom) :
    (catInj R b x : α) ≠ a := by
  sorry


theorem catInj_injective {r : Rel α α} {R : OrbitRestriction (r.dom ∪ r.codom) β}
    {b₁ b₂ : β} {x₁ x₂ : (r.dom ∪ r.codom : Set α) × ℕ}
    (h : (catInj R b₁ x₁ : α) = catInj R b₂ x₂) :
    b₁ = b₂ ∧ x₁ = x₂ := by
  have h₁ := categorise_catInj R b₁ x₁
  have h₂ := categorise_catInj R b₂ x₂
  rw [h, h₂] at h₁
  cases h₁
  rw [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] at h
  exact ⟨rfl, h⟩

@[target] theorem catInj_inj {r : Rel α α} {R : OrbitRestriction (r.dom ∪ r.codom) β}
    {b₁ b₂ : β} {a₁ a₂ : α} {h₁ : a₁ ∈ r.dom ∪ r.codom} {h₂ : a₂ ∈ r.dom ∪ r.codom} {n₁ n₂ : ℕ} :
    (catInj R b₁ (⟨a₁, h₁⟩, n₁) : α) = catInj R b₂ (⟨a₂, h₂⟩, n₂) ↔
      b₁ = b₂ ∧ a₁ = a₂ ∧ n₁ = n₂ := by
  sorry


inductive newOrbits {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) : Rel α α
  | left (a : α) (had : a ∈ r.dom) (hac : a ∉ r.codom) :
      newOrbits R (catInj R (R.catPerm.symm (R.categorise a)) (⟨a, Or.inl had⟩, 0)) a
  | leftStep (n : ℕ) (a : α) (had : a ∈ r.dom) (hac : a ∉ r.codom) :
      newOrbits R
        (catInj R (R.catPerm.symm^[n + 2] (R.categorise a)) (⟨a, Or.inl had⟩, n + 1))
        (catInj R (R.catPerm.symm^[n + 1] (R.categorise a)) (⟨a, Or.inl had⟩, n))
  | right (a : α) (had : a ∉ r.dom) (hac : a ∈ r.codom) :
      newOrbits R a (catInj R (R.catPerm (R.categorise a)) (⟨a, Or.inr hac⟩, 0))
  | rightStep (n : ℕ) (a : α) (had : a ∉ r.dom) (hac : a ∈ r.codom) :
      newOrbits R
        (catInj R (R.catPerm^[n + 1] (R.categorise a)) (⟨a, Or.inr hac⟩, n))
        (catInj R (R.catPerm^[n + 2] (R.categorise a)) (⟨a, Or.inr hac⟩, n + 1))

def permutativeExtension (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    Rel α α := by sorry


@[target] theorem le_permutativeExtension (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    r ≤ r.permutativeExtension R := by sorry


@[target] theorem dom_permutativeExtension_subset (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (r.permutativeExtension R).dom ⊆ r.dom ∪ r.codom ∪ R.sandbox := by
  sorry


theorem dom_permutativeExtension_subset' (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (r.permutativeExtension R).dom ⊆ (r.dom ∪ r.codom) ∪
      ((⋃ a ∈ r.dom, ⋃ n, Subtype.val '' Set.range
        (catInj R (R.catPerm.symm^[n + 1] (R.categorise a)))) ∪
      (⋃ a ∈ r.codom, ⋃ n, Subtype.val '' Set.range
        (catInj R (R.catPerm^[n + 1] (R.categorise a))))) := by
  rintro a₁ ⟨a₂, h | h⟩
  · exact Or.inl (Or.inl ⟨a₂, h⟩)
  cases h with
  | left _ had hac =>
    right; left
    simp only [Set.mem_iUnion]
    exact ⟨a₂, had, 0, _, ⟨_, rfl⟩, rfl⟩
  | leftStep n a had hac =>
    right; left
    simp only [Set.mem_iUnion]
    exact ⟨a, had, n + 1, _, ⟨_, rfl⟩, rfl⟩
  | right _ had hac => exact Or.inl (Or.inr hac)
  | rightStep n a had hac =>
    right; right
    simp only [Set.mem_iUnion]
    exact ⟨a, hac, n , _, ⟨_, rfl⟩, rfl⟩

@[target] theorem card_permutativeExtension (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β)
    (hr : r.Coinjective) :
    #(r.permutativeExtension R).dom ≤ max ℵ₀ #r.dom := by
  sorry


@[target] theorem categorise_newOrbits {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β)
    {a₁ a₂ : α} (h : newOrbits R a₁ a₂) :
    R.categorise a₂ = R.catPerm (R.categorise a₁) := by
  sorry


@[target] theorem categorise_permutativeExtension {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β)
    {a₁ a₂ : α} (h : r.permutativeExtension R a₁ a₂) :
    r a₁ a₂ ∨ R.categorise a₂ = R.catPerm (R.categorise a₁) := by sorry


@[target] theorem newOrbits_injective {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (newOrbits R).Injective := by
  sorry


@[target] theorem newOrbits_coinjective {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (newOrbits R).Coinjective := by
  sorry


@[target] theorem newOrbits_oneOne {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (newOrbits R).OneOne := by sorry


@[target] theorem permutativeExtension_codomEqDom {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (permutativeExtension r R).CodomEqDom := by
  sorry


@[target] theorem disjoint_newOrbits_dom {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    Disjoint r.dom (newOrbits R).dom := by
  sorry


theorem disjoint_newOrbits_codom {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    Disjoint r.codom (newOrbits R).codom := by
  rw [Set.disjoint_iff_forall_ne]
  rintro a₁ ha₁ a₂ ⟨a₃, h⟩
  cases h with
  | left => rintro rfl; contradiction
  | _ => exact (catInj_ne_of_mem R _ _ _ (Or.inr ha₁)).symm

theorem permutativeExtension_permutative {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β)
    (hr : r.OneOne) :
    (permutativeExtension r R).Permutative :=
  ⟨sup_oneOne hr (newOrbits_oneOne R) (disjoint_newOrbits_dom R) (disjoint_newOrbits_codom R),
    permutativeExtension_codomEqDom R⟩

/-- TODO: Strengthen statement in blueprint version. -/
/-- TODO: Strengthen statement in blueprint version. -/
@[target] theorem categorise_permutativeExtension_of_oneOne
    {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (hr : r.OneOne)
    {a₁ a₂ : α} (h : r.permutativeExtension R a₁ a₂) :
    r a₁ a₂ ∨ (a₁ ∉ r.dom ∧ a₂ ∉ r.codom ∧ R.categorise a₂ = R.catPerm (R.categorise a₁)) := by
  sorry


def permutativeExtension' (r : Rel α α) (hr : r.OneOne) (s : Set α)
    (hs₁ : s.Infinite) (hs₂ : #r.dom ≤ #s) (hs₃ : Disjoint (r.dom ∪ r.codom) s) :
    Rel α α :=
  r.permutativeExtension {
    sandbox := s
    sandbox_disjoint := hs₃
    categorise := λ _ ↦ Unit.unit
    catPerm := 1
    le_card_categorise := by
      intro
      simp only [Set.mem_singleton_iff, Set.preimage_const_of_mem, Set.inter_univ, max_le_iff,
        le_refl, and_true]
      rw [← Set.infinite_coe_iff, Cardinal.infinite_iff] at hs₁
      refine ⟨hs₁, ?_⟩
      apply (mk_union_le _ _).trans
      apply add_le_of_le hs₁ hs₂
      exact (card_codom_le_of_coinjective hr.toCoinjective).trans hs₂
  }

theorem le_permutativeExtension' {r : Rel α α} {hr : r.OneOne} {s : Set α}
    {hs₁ : s.Infinite} {hs₂ : #r.dom ≤ #s} {hs₃ : Disjoint (r.dom ∪ r.codom) s} :
    r ≤ r.permutativeExtension' hr s hs₁ hs₂ hs₃ :=
  r.le_permutativeExtension _

theorem permutativeExtension'_permutative {r : Rel α α} {hr : r.OneOne} {s : Set α}
    {hs₁ : s.Infinite} {hs₂ : #r.dom ≤ #s} {hs₃ : Disjoint (r.dom ∪ r.codom) s} :
    (r.permutativeExtension' hr s hs₁ hs₂ hs₃).Permutative :=
  permutativeExtension_permutative _ hr

theorem dom_permutativeExtension'_subset {r : Rel α α} {hr : r.OneOne} {s : Set α}
    {hs₁ : s.Infinite} {hs₂ : #r.dom ≤ #s} {hs₃ : Disjoint (r.dom ∪ r.codom) s} :
    (r.permutativeExtension' hr s hs₁ hs₂ hs₃).dom ⊆ r.dom ∪ r.codom ∪ s :=
  r.dom_permutativeExtension_subset _

end Rel
