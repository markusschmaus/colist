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

def tailX (as : Bound α α' β β') : Subtype (tailX.Property as) :=
    let head := as.instCurrent.tail as.current
    if not_nil : ¬ as.instCurrent.isNil head then
      have isNil_remaining_of_current a := (not_nil a).elim
      have not_isNil_of_remaining n not_nil' :=
        as.not_isNil_of_remaining n not_nil'

      Subtype.mk
        {inst := as.inst, inst' := as.inst', f := as.f, index := as.index,
          instCurrent := as.instCurrent, current := head, remaining := as.remaining,
          isNil_remaining_of_current := isNil_remaining_of_current,
          not_isNil_of_remaining := not_isNil_of_remaining}
        <| by
          apply tailX.Property.current
          · simp_all only [IsEmpty.forall_iff, not_false_eq_true]
          constructor
          all_goals simp only [heq_eq_eq]
    else if not_nil_tail : ¬ as.inst'.isNil as.remaining then
      let new_index := as.inst'.head as.remaining not_nil_tail
      let new_instCurrent := as.inst new_index
      let new_current := as.f new_index
      let new_remaining := as.inst'.tail as.remaining

      have isNil_remaining_of_current nil_head := by
        have := as.not_isNil_of_remaining 0 not_nil_tail
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
          apply tailX.Property.remaining
          case current_short =>
            have := as.isNil_remaining_of_current
            simp_all only [not_not, imp_false]
          case remaining_not_nil =>
            exact not_nil_tail
          constructor
          all_goals simp only [heq_eq_eq]

    else
      have isNil_remaining_of_current a := by
        simp_all only [not_true_eq_false, not_false_eq_true, not_not]
      have not_isNil_of_remaining n not_nil' :=
        as.not_isNil_of_remaining n not_nil'

      Subtype.mk
        { inst := as.inst, inst' := as.inst', f := as.f, index := as.index,
          instCurrent := as.instCurrent, current := head, remaining := as.remaining,
          isNil_remaining_of_current := isNil_remaining_of_current,
          not_isNil_of_remaining := not_isNil_of_remaining}
        <| by
          apply tailX.Property.nil
          case current_short =>
            simp_all only [not_not, forall_true_left, ProductiveListLike.isNil_iterate_tail,
              not_true_eq_false, eq_mp_eq_cast, id_eq, IsEmpty.forall_iff, forall_const]
          case remaining_nil =>
            simp_all only [not_not, forall_true_left, ProductiveListLike.isNil_iterate_tail,
              not_true_eq_false, eq_mp_eq_cast, id_eq, IsEmpty.forall_iff, forall_const]
          constructor
          all_goals simp only [heq_eq_eq]


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

end tailX.Property.FromCurrent

noncomputable abbrev finiteBy (as : Bound α α' β β') : Lex (Nat × Nat) :=
  toLex (as.inst'.length as.remaining, as.instCurrent.length as.current)

theorem decreasingBy (as : Bound α α' β β') (not_nil : ¬ PartialListLike.isNil as) :
    (PartialListLike.tail as).finiteBy < as.finiteBy := by
  simp [←length_zero_iff_isNil, PartialListLike.isNil] at not_nil
  unfold finiteBy
  simp only [Prod.Lex.lt_iff]
  induction as.tail_property with
  | current _ prop =>
    simp_all only [prop.inst', prop.remaining, lt_self_iff_false, prop.length_current, ne_eq,
      not_false_eq_true, Nat.pred_lt, and_self, or_true]
  | remaining _ _ prop =>
    simp_all? [prop.remaining, length_tail, prop.inst']
    simp_all?
    sorry
  | nil _ _ prop =>
    simp_all?
    sorry

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
    sorry
  finite as := by
    generalize nr_def : as.inst'.length as.remaining = nr
    induction nr generalizing as with
    | zero =>
      unfold PartialListLike.isFinite
      use as.instCurrent.length as.current
      generalize nc_def : as.instCurrent.length as.current = nc
      induction nc generalizing as with
      | zero =>
        simp_all only [Nat.zero_eq, length_zero_iff_isNil, PartialListLike.isNil, id_eq,
          eq_mp_eq_cast, Function.iterate_zero]
      | succ nc ih =>
        apply ih (PartialListLike.tail as)
        · induction as.tail_property
          case current _ prop =>
            simp_all only [Nat.zero_eq, Nat.find_eq_zero, Function.iterate_zero, id_eq,
              prop.remaining, prop.inst']
          case remaining _ _ prop =>
            simp_all only [Nat.zero_eq, length_zero_iff_isNil]
          case nil _ _ prop =>
            simp_all only [Nat.zero_eq, Nat.find_eq_zero, Function.iterate_zero, id_eq, prop.inst',
              prop.remaining]
        · induction as.tail_property
          case current _ prop =>
            simp_all only [Nat.zero_eq, prop.length_current, Nat.pred_succ]
          case remaining _ _ prop =>
            simp_all only [Nat.zero_eq, length_zero_iff_isNil]
          case nil _ _ prop =>
            simp_all only [Nat.zero_eq, prop.length_current, Nat.pred_succ]
    | succ n ih =>

      sorry
