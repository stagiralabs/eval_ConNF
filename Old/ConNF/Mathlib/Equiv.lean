import Mathlib.GroupTheory.Perm.Basic
import VerifiedAgora.tagger

variable {α β γ : Type _}

namespace Equiv

@[simp]
theorem symm_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).symm = g.symm.trans f.symm :=
  rfl

end Equiv
