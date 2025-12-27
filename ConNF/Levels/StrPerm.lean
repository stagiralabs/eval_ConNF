import ConNF.Base.BasePerm
import ConNF.Levels.Tree
import VerifiedAgora.tagger

/-!
# Structural permutations

In this file, we define the type of structural permutations.

## Main declarations

* `ConNF.StrPerm`: The type of structural permutations.
-/

universe u

namespace ConNF

variable [Params.{u}] {α : TypeIndex}

abbrev StrPerm : TypeIndex → Type u :=
  Tree BasePerm

end ConNF
