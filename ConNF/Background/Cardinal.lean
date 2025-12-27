import Mathlib.SetTheory.Cardinal.Regular
import ConNF.Background.Rel
import VerifiedAgora.tagger

universe u v

namespace Function

open Cardinal

/-- An alternate spelling of `Function.graph`, useful in proving inequalities of cardinals. -/
def graph' {α β : Type _} (f : α → β) : Set (α × β) :=
  {(x, y) | y = f x}

theorem graph'_injective {α β : Type _} : Injective (graph' : (α → β) → Set (α × β)) := by
  intro f g h
  ext x
  have : (x, f x) ∈ graph' f := rfl
  rwa [h] at this

theorem card_graph'_eq {α β : Type _} (f : α → β) : #(f.graph') = #α := by
  rw [Cardinal.eq]
  refine ⟨⟨λ x ↦ x.val.1, λ x ↦ ⟨⟨x, f x⟩, rfl⟩, ?_, ?_⟩⟩
  · rintro ⟨⟨x, _⟩, rfl⟩
    rfl
  · intro x
    rfl

end Function

namespace Cardinal

@[target] theorem mul_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a * b ≤ c := by
  sorry


@[target] theorem mk_biUnion_le_of_le_lift {α : Type u} {β : Type v} {s : Set α} {f : ∀ x ∈ s, Set β}
    (c : Cardinal.{v}) (h : ∀ (x : α) (h : x ∈ s), #(f x h) ≤ c) :
    lift.{u} #(⋃ (x : α) (h : x ∈ s), f x h) ≤ lift.{v} #s * lift.{u} c := by
  sorry


@[target] theorem mk_biUnion_le_of_le {α β : Type _} {s : Set α} {f : ∀ x ∈ s, Set β}
    (c : Cardinal) (h : ∀ (x : α) (h : x ∈ s), #(f x h) ≤ c) :
    #(⋃ (x : α) (h : x ∈ s), f x h) ≤ #s * c := by
  sorry


@[target] theorem mk_iUnion_le_of_le_lift {α : Type u} {β : Type v} {f : α → Set β}
    (c : Cardinal.{v}) (h : ∀ (x : α), #(f x) ≤ c) :
    lift.{u} #(⋃ (x : α), f x) ≤ lift.{v} #α * lift.{u} c := by
  sorry


@[target] theorem mk_iUnion_le_of_le {α β : Type _} {f : α → Set β}
    (c : Cardinal) (h : ∀ (x : α), #(f x) ≤ c) :
    #(⋃ (x : α), f x) ≤ #α * c := by
  sorry


@[target] theorem lift_isRegular (c : Cardinal.{u}) (h : IsRegular c) : IsRegular (lift.{v} c) := by
  sorry


@[target] theorem le_of_le_add {c d e : Cardinal.{u}} (h : c ≤ d + e) (hc : ℵ₀ ≤ c) (he : e < c) : c ≤ d := by
  sorry


@[target] theorem mk_ne_zero_iff_nonempty {α : Type _} (s : Set α) :
    #s ≠ 0 ↔ s.Nonempty := by
  sorry


@[target] theorem compl_nonempty_of_mk_lt {α : Type _} {s : Set α} (h : #s < #α) : sᶜ.Nonempty := by
  sorry


theorem mk_pow_le_of_mk_lt_ord_cof {α β : Type _}
    (hα : (#α).IsStrongLimit) (hβ : #β < (#α).ord.cof) :
    #α ^ #β ≤ #α := by
  by_cases hβ' : #β = 0
  · rw [hβ', power_zero]
    exact one_le_iff_ne_zero.mpr hα.1
  have hαβ : #(β × α) = #α := by
    rw [mk_prod, lift_id, lift_id]
    apply mul_eq_right
    · exact aleph0_le_of_isSuccLimit hα.isSuccLimit
    · exact hβ.le.trans (Ordinal.cof_ord_le (#α))
    · exact hβ'
  have := mk_subset_mk_lt_cof (α := β × α) (hαβ ▸ hα.2)
  refine le_trans ?_ (this.trans hαβ).le
  rw [power_def]
  refine mk_le_of_injective (f := λ f ↦ ⟨f.graph', ?_⟩) ?_
  · rwa [hαβ, Function.card_graph'_eq]
  · intro f g h
    exact Function.graph'_injective (congr_arg Subtype.val h)

/-- If `c` is a strong limit and `d` is not "too large", then `c ^ d = c`.
By "too large" here, we mean large enough to be a counterexample by König's theorem on cardinals:
`c < c ^ c.ord.cof`. -/
/-- If `c` is a strong limit and `d` is not "too large", then `c ^ d = c`.
By "too large" here, we mean large enough to be a counterexample by König's theorem on cardinals:
`c < c ^ c.ord.cof`. -/
@[target] theorem pow_le_of_lt_ord_cof {c d : Cardinal} (hc : c.IsStrongLimit) (hd : d < c.ord.cof) :
    c ^ d ≤ c := by
  sorry


@[target] theorem mk_fun_le (α β : Type _) :
    #(α → β) ≤ #(Set (α × β)) := by sorry


@[target] theorem mk_power_le_two_power (α β : Type _) :
    #α ^ #β ≤ max ℵ₀ (max (2 ^ #α) (2 ^ #β)) := by
  -- Brutal case analysis - there's got to be a cleaner proof.
  sorry


@[target] theorem power_le_two_power (c d : Cardinal) :
    c ^ d ≤ max ℵ₀ (max (2 ^ c) (2 ^ d)) := by
  sorry


/-- Strong limit cardinals are closed under exponentials. -/
/-- Strong limit cardinals are closed under exponentials. -/
@[target] theorem pow_lt_of_lt {c d e : Cardinal} (hc : c.IsStrongLimit) (hd : d < c) (he : e < c) :
    d ^ e < c := by
  sorry


@[target] theorem card_codom_le_of_functional {α β : Type _} {r : Rel α β} (hr : r.Functional) :
    #r.codom ≤ #r.dom := by
  sorry


@[target] theorem card_codom_le_of_coinjective {α β : Type _} {r : Rel α β} (hr : r.Coinjective) :
    #r.codom ≤ #r.dom := by
  sorry


end Cardinal
