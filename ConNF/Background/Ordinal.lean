import ConNF.Background.WellOrder
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic
import VerifiedAgora.tagger

noncomputable section
universe u v

open Cardinal
open scoped InitialSeg

namespace Ordinal

def withBotOrderIso {α : Type u} [Preorder α] [IsWellOrder α (· < ·)] :
    ((· < ·) : WithBot α → WithBot α → Prop) ≃r
      Sum.Lex (EmptyRelation (α := PUnit)) ((· < ·) : α → α → Prop) where
  toFun := WithBot.recBotCoe (Sum.inl PUnit.unit) Sum.inr
  invFun := Sum.elim (λ _ ↦ ⊥) (λ x ↦ x)
  left_inv x := by sorry


@[target] theorem type_withBot {α : Type u} [Preorder α] [IsWellOrder α (· < ·)] :
    type ((· < ·) : WithBot α → WithBot α → Prop) = 1 + type ((· < ·) : α → α → Prop) := by
  sorry


@[target] theorem noMaxOrder_of_isLimit {α : Type u} [Preorder α] [IsWellOrder α (· < ·)]
    (h : (type ((· < ·) : α → α → Prop)).IsLimit) : NoMaxOrder α := by
  sorry


@[target] theorem isLimit_of_noMaxOrder {α : Type u} [Nonempty α] [Preorder α] [IsWellOrder α (· < ·)]
    (h : NoMaxOrder α) : (type ((· < ·) : α → α → Prop)).IsLimit := by
  sorry


@[target] theorem isLimit_iff_noMaxOrder {α : Type u} [Nonempty α] [Preorder α] [IsWellOrder α (· < ·)] :
    (type ((· < ·) : α → α → Prop)).IsLimit ↔ NoMaxOrder α := by sorry


@[target] theorem type_Iio_lt {α : Type u} [LtWellOrder α] (x : α) :
    type (Subrel ((· < ·) : α → α → Prop) (Set.Iio x)) < type ((· < ·) : α → α → Prop) := by sorry


def iicOrderIso {α : Type u} [LtWellOrder α] (x : α) :
    (Subrel ((· < ·) : α → α → Prop) (Set.Iic x)) ≃r
      Sum.Lex (Subrel ((· < ·) : α → α → Prop) (Set.Iio x)) (EmptyRelation (α := PUnit)) where
  toFun y := if h : y = x then Sum.inr PUnit.unit else Sum.inl ⟨y, y.prop.lt_of_ne h⟩
  invFun := Sum.elim (λ y ↦ ⟨y, y.prop.le⟩) (λ _ ↦ ⟨x, le_rfl⟩)
  left_inv y := by aesop
  right_inv y := by
    obtain (y | y) := y
    · simp only [Sum.elim_inl, Subtype.coe_eta, dite_eq_ite, ite_eq_right_iff, reduceCtorEq,
        imp_false]
      exact y.prop.ne
    · simp only [Sum.elim_inr, ↓reduceDIte]
  map_rel_iff' {y z} := by
    simp only [Equiv.coe_fn_mk, subrel_val, Subtype.coe_lt_coe]
    split_ifs with h h' h'
    · rw [Sum.lex_inr_inr, empty_relation_apply, false_iff, not_lt,
        Subtype.coe_injective (h.trans h'.symm)]
    · simp only [Sum.lex_inr_inl, false_iff, not_lt, ← Subtype.coe_le_coe, h]
      exact z.prop
    · simp only [Sum.Lex.sep, true_iff]
      rw [← Subtype.coe_lt_coe]
      exact lt_of_le_of_ne (y.prop.trans_eq h'.symm) (h'.trans_ne (Ne.symm h)).symm
    · simp only [Sum.lex_inl_inl, subrel_val, Subtype.coe_lt_coe]

theorem type_Iic_eq {α : Type u} [LtWellOrder α] (x : α) :
    type (Subrel ((· < ·) : α → α → Prop) (Set.Iic x)) =
    type (Subrel ((· < ·) : α → α → Prop) (Set.Iio x)) + 1 := by
  change _ = _ + type EmptyRelation
  rw [← type_sum_lex, type_eq]
  exact ⟨iicOrderIso x⟩

@[target] theorem type_Iic_lt {α : Type u} [LtWellOrder α] [NoMaxOrder α] (x : α) :
    type (Subrel ((· < ·) : α → α → Prop) (Set.Iic x)) < type ((· < ·) : α → α → Prop) := by
  sorry


instance ULift.isTrichotomous {α : Type u} {r : α → α → Prop} [IsTrichotomous α r] :
    IsTrichotomous (ULift.{v} α) (InvImage r ULift.down) := by
  constructor
  rintro ⟨a⟩ ⟨b⟩
  simp only [ULift.up_inj, InvImage]
  exact IsTrichotomous.trichotomous a b

instance ULift.isTrans {α : Type u} {r : α → α → Prop} [IsTrans α r] :
    IsTrans (ULift.{v} α) (InvImage r ULift.down) := by
  constructor
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
  simp only [InvImage]
  exact IsTrans.trans a b c

instance ULift.isWellOrder {α : Type u} {r : α → α → Prop} [IsWellOrder α r] :
    IsWellOrder (ULift.{v} α) (InvImage r ULift.down) :=
  ⟨⟩

theorem lift_typein_apply {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≼i s) (a : α) :
    Ordinal.lift.{max u v, v} (Ordinal.typein s (f a)) =
    Ordinal.lift.{max u v, u} (Ordinal.typein r a) := by
  symm
  apply Quotient.sound
  constructor
  refine RelIso.ofSurjective ⟨⟨λ x ↦ ⟨f x.down, ?_⟩, ?_⟩, ?_⟩ ?_
  · simp only [Set.mem_setOf_eq, f.map_rel_iff]
    exact x.down.prop
  · intro x y h
    apply ULift.down_injective
    apply Subtype.coe_injective
    simp only [ULift.up_inj, Subtype.mk.injEq,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact h
  · intro x y
    simp only [Order.Preimage, Function.Embedding.coeFn_mk, subrel_val]
    exact f.map_rel_iff
  · intro x
    obtain ⟨y, hy⟩ := f.mem_range_of_rel x.down.prop
    refine ⟨ULift.up ⟨y, ?_⟩, ?_⟩
    · have := x.down.prop
      rwa [← hy, f.map_rel_iff] at this
    · apply ULift.down_injective
      apply Subtype.coe_injective
      simp only [Set.mem_setOf_eq, Set.coe_setOf, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
      exact hy

/-!
## The additive structure on the set of ordinals below a cardinal
-/

@[target] theorem card_Iio (o : Ordinal.{u}) : #(Set.Iio o) = Cardinal.lift.{u + 1} o.card := by
  sorry


instance {o : Ordinal.{u}} : LtWellOrder (Set.Iio o) where

@[target] theorem type_Iio (o : Ordinal.{u}) :
    type ((· < ·) : Set.Iio o → Set.Iio o → Prop) = lift.{u + 1} o := by
  sorry


@[target] theorem typein_Iio {o : Ordinal.{u}} (x : Set.Iio o) :
    typein ((· < ·) : Set.Iio o → Set.Iio o → Prop) x = lift.{u + 1} x := by
  sorry


variable {c : Cardinal.{u}} (h : ℵ₀ ≤ c)

theorem add_lt_ord (h : ℵ₀ ≤ c) {x y : Ordinal.{u}}
    (hx : x < c.ord) (hy : y < c.ord) : x + y < c.ord := by
  rw [lt_ord] at hx hy ⊢
  rw [card_add]
  exact Cardinal.add_lt_of_lt h hx hy

def iioAdd : Add (Set.Iio c.ord) where
  add x y := by sorry


def iioSub (o : Ordinal) : Sub (Set.Iio o) where
  sub x y := by sorry


@[target] theorem ord_pos (h : ℵ₀ ≤ c) : 0 < c.ord := by
  sorry


def iioZero : Zero (Set.Iio c.ord) where
  zero := by sorry


@[target] theorem iioAdd_def (x y : Set.Iio c.ord) :
    letI := by sorry


def iioAddMonoid : AddMonoid (Set.Iio c.ord) where
  add_assoc x y z := by
    sorry


@[target] theorem nat_lt_ord (h : ℵ₀ ≤ c) (n : ℕ) : n < c.ord := by
  sorry


def iioOfNat (n : ℕ) : OfNat (Set.Iio c.ord) n where
  ofNat := by sorry


theorem iioOfNat_coe (n : ℕ) :
    letI := iioOfNat h
    ((OfNat.ofNat n : Set.Iio c.ord) : Ordinal) = n :=
  rfl

@[target] theorem iio_noMaxOrder (h : ℵ₀ ≤ c) : NoMaxOrder (Set.Iio c.ord) := by
  sorry


end Ordinal
