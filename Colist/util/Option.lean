import Colist.util.Bool
import Mathlib.Tactic

namespace Option

instance {α : Type u} {as : Option α} : Decidable (as = none) :=
  decidableFromBool Option.isNone Option.isNone_iff_eq_none

theorem isSome_of_not_eq_none {α : Type u} {as : Option α} :
    ¬ as = none → isSome as = true := by
  match as with
  | some _ => intro _; rfl
  | none => intro _; contradiction
