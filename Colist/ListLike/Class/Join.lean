import Colist.ListLike.Class.Filtered

universe u v w

namespace ListLike

structure PartialBound (α α' : Type u) (β : α' → Type v) (β' : Type v)  where
  inst : (x : α') → ListLike α (β x)
  [inst' : ListLike α' β']
  f : (x : α') → β x
  index : α'
  instCurrent : ListLike α (β index)
  current : β index
  remaining : β'

namespace PartialBound
variable {α α' : Type u} {β : α' → Type v} {β' : Type v}

noncomputable abbrev getIndex (as : PartialBound α α' β β') (n : Nat) (not_nil : _) :=
    as.inst'.head ((as.inst'.tail)^[n] as.remaining) not_nil

noncomputable abbrev getListLike (as : PartialBound α α' β β') (n : Nat) (not_nil : _) :=
    as.f <|getIndex as n not_nil

noncomputable abbrev getInst (as : PartialBound α α' β β') (n : Nat) (not_nil : _) :=
    as.inst (PartialBound.getIndex as n not_nil)

end PartialBound

structure Bound (α α' : Type u) (β : α' → Type v) (β' : Type v)
    extends PartialBound α α' β β' where
  isNil_remaining_of_current : instCurrent.isNil current → inst'.isNil remaining
  not_isNil_of_remaining : ∀ n, ∀ (not_nil' : _),
      ¬ (PartialBound.getInst toPartialBound n not_nil').isNil
      (PartialBound.getListLike toPartialBound n not_nil')

namespace Bound
variable {α α' : Type u} {β : α' → Type v} {β' : Type v}

noncomputable abbrev getIndex (as : Bound α α' β β') (n : Nat) (not_nil : _) :=
    as.toPartialBound.getIndex n not_nil

noncomputable abbrev getListLike (as : Bound α α' β β') (n : Nat) (not_nil : _) :=
    as.toPartialBound.getListLike n not_nil

noncomputable abbrev getInst (as : Bound α α' β β') (n : Nat) (not_nil : _) :=
    as.toPartialBound.getInst n not_nil

instance instMembership : Membership α (Bound α α' β β') where
  mem a as := as.instCurrent.instMembership.mem a as.current ∨
    ∃ a', (as.inst a').instMembership.mem a (as.f a') ∧
    as.inst'.instMembership.mem a' as.remaining

namespace tailX.Property

structure FromCurrent (as : Bound α α' β β') (out : Bound α α' β β') : Prop where
  inst : out.inst = as.inst
  inst' : out.inst' = as.inst'
  f : out.f = as.f
  index : out.index = as.index
  instCurrent : out.instCurrent = index ▸ as.instCurrent
  current : out.current = index ▸ (as.instCurrent.tail as.current)
  remaining : out.remaining = as.remaining

structure FromRemaining (as : Bound α α' β β') (not_nil)
    (out : Bound α α' β β') : Prop where
  inst : out.inst = as.inst
  inst' : out.inst' = as.inst'
  f : out.f = as.f
  index : out.index = as.inst'.head as.remaining not_nil
  instCurrent : out.instCurrent = index ▸  (as.inst (as.inst'.head as.remaining not_nil))
  current : out.current = index ▸ (as.f (as.inst'.head as.remaining not_nil))
  remaining : out.remaining = as.inst'.tail as.remaining

end Property

inductive Property (as : Bound α α' β β') (out : Bound α α' β β') : Prop
  | current
    (current_long : ¬ as.instCurrent.isNil (as.instCurrent.tail as.current))
    (prop : Property.FromCurrent as out) : Property as out
  | remaining
    (current_short : as.instCurrent.isNil (as.instCurrent.tail as.current))
    (remaining_not_nil : ¬ as.inst'.isNil as.remaining)
    (prop : Property.FromRemaining as remaining_not_nil out) : Property as out
  | nil
    (current_short : as.instCurrent.isNil (as.instCurrent.tail as.current))
    (remaining_nil : as.inst'.isNil as.remaining)
    (prop : Property.FromCurrent as out) : Property as out

namespace Property
variable {as : Bound α α' β β'} {out : Bound α α' β β'}

@[simp]
theorem inst (prop : Property as out) :
    out.inst = as.inst := by
  induction prop with
  | current _ prop => exact prop.inst
  | remaining _ _ prop => exact prop.inst
  | nil _ _ prop => exact prop.inst

@[simp]
theorem inst' (prop : Property as out) :
    out.inst' = as.inst' := by
  induction prop with
  | current _ prop => exact prop.inst'
  | remaining _ _ prop => exact prop.inst'
  | nil _ _ prop => exact prop.inst'

@[simp]
theorem f (prop : Property as out) :
    out.f = as.f := by
  induction prop with
  | current _ prop => exact prop.f
  | remaining _ _ prop => exact prop.f
  | nil _ _ prop => exact prop.f

def fromCurrent (prop : Property as out)
    (h : ¬ as.instCurrent.isNil (as.instCurrent.tail as.current) ∨
      as.inst'.isNil as.remaining) :
    FromCurrent as out :=
  match prop with
  | current _ prop => prop
  | remaining _ _ _ =>
    False.elim <| by simp_all only [not_true_eq_false, or_self]
  | nil _ _ prop => prop

def fromRemaining (prop : Property as out)
    (h : as.instCurrent.isNil (as.instCurrent.tail as.current) ∧
      ¬ as.inst'.isNil as.remaining) :
    FromRemaining as h.right out :=
  match prop with
  | current _ _ =>
    have false : False := by simp_all only [not_false_eq_true, false_and]
    False.elim false
  | remaining _ _ prop => prop
  | nil _ _ _ =>
    have false : False := by simp_all only [not_true_eq_false, and_false]
    False.elim false

end tailX.Property

def nextCurrentX (as : Bound α α' β β')
    (not_nil : as.instCurrent.isNil (as.instCurrent.tail as.current) →
    as.inst'.isNil as.remaining) :
    Subtype (tailX.Property.FromCurrent as) :=
  have isNil_remaining_of_current := not_nil
  have not_isNil_of_remaining n not_nil' :=
    as.not_isNil_of_remaining n not_nil'

  Subtype.mk
    {inst := as.inst, inst' := as.inst', f := as.f, index := as.index,
      instCurrent := as.instCurrent, current := as.instCurrent.tail as.current,
      remaining := as.remaining,
      isNil_remaining_of_current := isNil_remaining_of_current,
      not_isNil_of_remaining := not_isNil_of_remaining}
    <| by
      constructor
      all_goals simp only [heq_eq_eq]

def nextRemainingX (as : Bound α α' β β') (not_nil : ¬ as.inst'.isNil as.remaining) :
    Subtype (tailX.Property.FromRemaining as not_nil) :=
  let new_index := as.inst'.head as.remaining not_nil
  let new_instCurrent := as.inst new_index
  let new_current := as.f new_index
  let new_remaining := as.inst'.tail as.remaining

  have isNil_remaining_of_current nil_head := by
    have := as.not_isNil_of_remaining 0 not_nil
    simp_all only [not_not, PartialBound.getIndex, Function.iterate_zero, id_eq,
      PartialBound.getListLike, not_true_eq_false]
  have not_isNil_of_remaining n not_nil' := by
    unfold_let at *
    have := as.not_isNil_of_remaining n.succ <| by
      simp_all only [not_not, Function.iterate_succ, Function.comp_apply,
        not_false_eq_true]
    simp_all only [not_not, id_eq, PartialBound.getIndex, Function.iterate_succ,
      Function.comp_apply, PartialBound.getListLike, not_false_eq_true]

  Subtype.mk
    { inst := as.inst, inst' := as.inst', f := as.f, index := new_index,
      instCurrent := new_instCurrent, current := new_current,
      remaining := new_remaining,
      isNil_remaining_of_current := isNil_remaining_of_current,
      not_isNil_of_remaining := not_isNil_of_remaining}
    <| by
      constructor
      all_goals simp only [heq_eq_eq]

def tailX (as : Bound α α' β β') : Subtype (tailX.Property as) :=
    let head := as.instCurrent.tail as.current
    if not_nil : ¬ as.instCurrent.isNil head then
      let result := nextCurrentX as fun a => (not_nil a).elim

      Subtype.mk result.val <| by
          apply tailX.Property.current
          · simp_all only [IsEmpty.forall_iff, not_false_eq_true]
          exact result.property

    else if not_nil_remaining : ¬ as.inst'.isNil as.remaining then
      let result := nextRemainingX as not_nil_remaining
      Subtype.mk result.val <| by
          apply tailX.Property.remaining
          case current_short =>
            simp_all only [not_not]
          case remaining_not_nil =>
            exact not_nil_remaining
          exact result.property

    else
      let result := nextCurrentX as <| by
        simp_all only [not_not, forall_true_left]

      Subtype.mk result.val <| by
          apply tailX.Property.nil
          case current_short =>
            simp only [not_not] at not_nil
            exact not_nil
          case remaining_nil =>
            simp only [not_not] at not_nil_remaining
            exact not_nil_remaining
          exact result.property

instance instPartialListLike : PartialListLike α (Bound α α' β β') where
  isNil as := as.instCurrent.isNil as.current
  head as := as.instCurrent.head as.current
  tail as := tailX as

def tail_property (as : Bound α α' β β') :
    tailX.Property as (PartialListLike.tail as) :=
  (tailX as |>.property)

theorem isNil_eqRec {index : α'} {index' : α'}
    {inst : ListLike α (β index)} {inst' : ListLike α (β index')}
    (eq_index : index = index') (eq_inst : inst = eq_index ▸ inst')
    {as : β index} {as' : β index'}
    (as_eq : as = eq_index ▸ as' ) : inst.isNil as ↔ inst'.isNil as' := by
  aesop

theorem length_eqRec {index : α'} {index' : α'}
    {inst : ListLike α (β index)} {inst' : ListLike α (β index')}
    (eq_index : index = index') (eq_inst : inst = eq_index ▸ inst')
    {as : β index} {as' : β index'}
    (as_eq : as = eq_index ▸ as' ) : inst.length as = inst'.length as' := by
  aesop

namespace tailX.Property.FromCurrent

theorem isNil_current {as : Bound α α' β β'}
    {out : Bound α α' β β'} (prop : FromCurrent as out) :
    out.instCurrent.isNil out.current  = as.instCurrent.isNil (as.instCurrent.tail as.current) := by
  have := isNil_eqRec prop.index prop.instCurrent prop.current
  simp_all only [prop.instCurrent, prop.current]

theorem length_current {as : Bound α α' β β'}
    {out : Bound α α' β β'} (prop : FromCurrent as out) :
    out.instCurrent.length out.current  = (as.instCurrent.length as.current).pred := by
  have := length_eqRec prop.index prop.instCurrent prop.current
  simp_all only [prop.instCurrent, prop.current, length_tail]

theorem length_remaining {as : Bound α α' β β'}
    {out : Bound α α' β β'} (prop : FromCurrent as out) :
    out.inst'.length out.remaining  = as.inst'.length as.remaining := by
  simp_all only [prop.inst', prop.remaining]

end FromCurrent

namespace FromRemaining

theorem length_remaining {as : Bound α α' β β'} {not_nil}
    {out : Bound α α' β β'} (prop : FromRemaining as not_nil out) :
    out.inst'.length out.remaining  = (as.inst'.length as.remaining).pred := by
  simp_all only [prop.inst', prop.remaining, length_tail]

end tailX.Property.FromRemaining

noncomputable abbrev lengthCurrent (as : Bound α α' β β') : Nat :=
  as.instCurrent.length as.current

noncomputable abbrev lengthRemaining (as : Bound α α' β β') : Nat :=
  as.inst'.length as.remaining

@[simp]
theorem decreasing_length_current_remaining {as : Bound α α' β β'}
    (not_nil : ¬ PartialListLike.isNil as):
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂)
    (lengthRemaining (PartialListLike.tail as), lengthCurrent (PartialListLike.tail as))
    (lengthRemaining as, lengthCurrent as) := by
  induction as.tail_property
  case current _ prop =>
    apply Prod.Lex.right'
    · simp only [prop.length_remaining, le_refl]
    simp only [prop.length_current]
    apply Nat.pred_lt
    apply length_zero_iff_isNil.not.mpr
    simp_all only [PartialListLike.isNil, not_false_eq_true]
  case remaining _ r_not_nil prop =>
    apply Prod.Lex.left
    simp only [lengthRemaining, prop.inst', prop.remaining, length_tail]
    apply Nat.pred_lt
    apply length_zero_iff_isNil.not.mpr
    exact r_not_nil
  case nil _ _ prop =>
    apply Prod.Lex.right'
    · simp only [prop.length_remaining, le_refl]
    simp only [prop.length_current]
    apply Nat.pred_lt
    apply length_zero_iff_isNil.not.mpr
    simp_all only [PartialListLike.isNil, not_false_eq_true]

noncomputable def length (as : Bound α α' β β') :
    Subtype fun n : Nat => PartialListLike.isNil (PartialListLike.tail^[n] as) :=
  let rec go n current (h : current = PartialListLike.tail^[n] as) :=
    if nil : PartialListLike.isNil current then
      Subtype.mk n <| by
        simp_all only
    else
      go n.succ (PartialListLike.tail current) <| by
        simp_all only [h, Function.iterate_succ', Function.comp_apply, not_false_eq_true]
  termination_by (current.lengthRemaining, current.lengthCurrent)
  decreasing_by
    simp_wf
    simp_all only [not_false_eq_true, decreasing_length_current_remaining]

  go 0 as <| by
    simp only [Function.iterate_zero, id_eq]

-- noncomputable def find (as : Bound α α' β β') :
--     Subtype fun n : Nat => PartialListLike.isNil (PartialListLike.tail^[n] as) :=
--   let rec go n current (h : current = PartialListLike.tail^[n] as) :=
--     if nil : PartialListLike.isNil current then
--       Subtype.mk n <| by
--         simp_all only
--     else
--       go n.succ (PartialListLike.tail current) <| by
--         simp_all only [h, Function.iterate_succ', Function.comp_apply, not_false_eq_true]
--   termination_by (current.lengthRemaining, current.lengthCurrent)
--   decreasing_by
--     simp_wf
--     simp_all only [not_false_eq_true, decreasing_length_current_remaining]

--   go 0 as <| by
--     simp only [Function.iterate_zero, id_eq]


instance instListLike : ListLike α (Bound α α' β β') where
  toPartialListLike := instPartialListLike
  terminal_isNil as is_nil := by
    induction as.tail_property
    · simp_all only [PartialListLike.isNil, ProductiveListLike.isNil_tail, not_true_eq_false]
    · have := as.isNil_remaining_of_current
      simp_all only [PartialListLike.isNil, forall_true_left]
    case nil _ _ prop =>
      simp_all only [PartialListLike.isNil, ProductiveListLike.isNil_tail, prop.isNil_current]
  consistent_mem a as := by
    constructor
    · simp only [PartialListLike.Mem, Membership.mem]
      intro ⟨n, not_nil, h⟩

      sorry
    ·
      sorry
  finite as := by
    let n := as.length
    use n.val
    exact n.property
