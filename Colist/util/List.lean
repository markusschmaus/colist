import Colist.util.Bool
import Mathlib.Data.List.Basic

instance {α : Type u} {as : List α} : Decidable (as = []) :=
  decidableFromBool List.isEmpty List.isEmpty_iff_eq_nil
