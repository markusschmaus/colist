import Colist.ListLike.AnyListLike
import Colist.ListLike.ProductiveListLike.Mem
import Colist.ListLike.ProductiveListLike.Pairwise
import Colist.util.Option
import Colist.util.Function

universe u v

namespace ListLike

namespace Filtered

def valid {α : Type u} {β : Type v} [inst : PartialListLike α β] (p : α → Prop)
    (baseTail : β) : Prop :=
  (not_nil : ¬ PartialListLike.isNil baseTail) → p (PartialListLike.head baseTail not_nil)

instance {α : Type u} {β : Type v} [inst : ListLike α β] (p : α → Prop)
    [decP : DecidablePred p]  (baseTail : β) : Decidable (valid p baseTail) :=
  if nil? : PartialListLike.isNil baseTail then
    isTrue <| by
      simp_all only [valid, not_true_eq_false, IsEmpty.forall_iff]
  else if valid? : p (PartialListLike.head baseTail nil?) then
    isTrue <| by
      simp_all only [valid, not_false_eq_true, forall_true_left]
  else
    isFalse <| by
      simp_all only [valid, not_false_eq_true, forall_true_left]

namespace baseTail

structure PropertyN {α : Type u} {β : Type v} (inst : ListLike α β) {p : α → Prop}
    (decP : DecidablePred p) (base : β) (baseTail : β) (n : Nat) : Prop where
  hit : valid p (inst.tail^[n] base)
  misses {i : Nat} : i < n → ¬ valid p (inst.tail^[i] base)
  eq_baseTail : baseTail = inst.tail^[n] base

def Property {α : Type u} {β : Type v} [inst : ListLike α β] (p : α → Prop)
    [decP : DecidablePred p] (base : β) (baseTail : β) :=
  ∃ (n : Nat), PropertyN inst decP base baseTail n

end baseTail

def getBaseTail  {α : Type u} {β : Type v} (inst : ListLike α β) {p : α → Prop}
    (decP : DecidablePred p) (base : β) : Subtype (baseTail.Property p base) :=

  let rec go (candidate : β) (n : Nat)
      (iterate_tail : candidate = PartialListLike.tail^[n] base)
      (misses : ∀ (i : Nat), i < n → ¬ valid p (PartialListLike.tail^[i] base)) :
      Subtype (baseTail.Property p base) :=
    if valid? : valid p candidate then
      Subtype.mk candidate <| by
        use n
        constructor
        · simp_all only
        · simp_all only [not_false_eq_true, implies_true, forall_const]
        · simp_all only
    else
      have iterate_tail' := by
        simp_all only [Function.iterate_succ_apply']
      have misses' :=by
        intro i lt
        by_cases i < n
        · simp_all only [Function.iterate_succ_apply', not_false_eq_true]
        · have : i = n := by omega
          simp_all only [Function.iterate_succ_apply', lt_add_iff_pos_right,
            zero_lt_one, lt_self_iff_false, not_false_eq_true]

      -- Show termination:
      have : ∀ (m : ℕ),
          (∀ i < m, ¬PartialListLike.isNil (PartialListLike.tail^[i]
            (PartialListLike.tail candidate))) →
          ¬PartialListLike.isNil (PartialListLike.tail^[m] candidate) := by
        intro m
        by_cases m_zero : m = 0
        · subst m_zero
          simp only [valid, not_forall] at valid?
          have ⟨not_nil, _⟩ := valid?
          simp_all only [Function.iterate_succ_apply', not_lt_zero',
            IsEmpty.forall_iff, forall_const, Function.iterate_zero, id_eq,
            forall_true_left, not_false_eq_true, exists_prop, and_true]
        · intro h
          have := h m.pred
          simp only [←Function.iterate_succ_apply] at this
          have ⟨k, k_def⟩ := Nat.exists_eq_succ_of_ne_zero m_zero
          subst k_def
          simp_all only [lt_add_iff_pos_right, zero_lt_one, not_false_eq_true,
            Function.iterate_succ_apply', Nat.succ_ne_zero, Nat.pred_succ,
            Nat.lt_succ_self, forall_true_left]
      go (PartialListLike.tail candidate) (n + 1) iterate_tail' misses'
  termination_by Nat.find (inst.finite candidate)

  go base 0 rfl (by omega)

abbrev mkBaseTail {α : Type u} {β : Type v} [inst : ListLike α β]
    {p : α → Prop} [decP : DecidablePred p] (base : β) :
    Thunk (Subtype (Filtered.baseTail.Property p base)) :=
  Thunk.mk (fun () => Filtered.getBaseTail inst decP base)

end Filtered

structure Filtered (α : Type u) (β : Type v) where
  [inst : ListLike α β]
  p : α → Prop
  [decP : DecidablePred p]
  base : β
  baseTail : Thunk (Subtype (Filtered.baseTail.Property p base)) :=
    Filtered.mkBaseTail base

namespace Filtered

instance instMembership {α : Type u} {β : Type v} :
    Membership α (Filtered α β) where
  mem a as := as.p a ∧ as.inst.instMembership.mem a as.base

instance instPartialListLike {α : Type u} {β : Type v} :
    PartialListLike α (Filtered α β) where
  isNil as := as.inst.isNil as.baseTail.get
  head as := as.inst.head as.baseTail.get
  tail as :=
    let newBase := as.inst.tail (Thunk.get as.baseTail).val
    {inst := as.inst, p := as.p, decP := as.decP, base := newBase}

@[simp]
theorem tail_p {α : Type u} {β : Type v} {as : Filtered α β} :
    (PartialListLike.tail as).p = as.p := by
  simp [PartialListLike.tail]

@[simp]
theorem iterate_tail_p {α : Type u} {β : Type v} {as : Filtered α β} {n : Nat} :
    (PartialListLike.tail^[n] as).p = as.p := by
  induction n generalizing as with
  | zero =>
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
  | succ n ih =>
    have := ih (as := PartialListLike.tail as)
    simp_all only [tail_p, Function.iterate_succ, Function.comp_apply]

@[simp]
theorem tail_inst {α : Type u} {β : Type v} {as : Filtered α β} :
    (PartialListLike.tail as).inst = as.inst := by
  simp [PartialListLike.tail]

@[simp]
theorem iterate_tail_inst {α : Type u} {β : Type v} {as : Filtered α β} {n : Nat} :
    (PartialListLike.tail^[n] as).inst = as.inst := by
  induction n generalizing as with
  | zero =>
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
  | succ n ih =>
    have := ih (as := PartialListLike.tail as)
    simp_all only [tail_inst, Function.iterate_succ, Function.comp_apply]

@[simp]
theorem tail_decP {α : Type u} {β : Type v} {as : Filtered α β} :
    (PartialListLike.tail as).decP = as.decP := by
  simp [PartialListLike.tail]

@[simp]
theorem iterate_tail_decP_heq {α : Type u} {β : Type v} {as : Filtered α β} {n : Nat} :
    HEq (PartialListLike.tail^[n] as).decP as.decP := by
  induction n generalizing as with
  | zero =>
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq, heq_eq_eq]
  | succ n ih =>
    have := ih (as := PartialListLike.tail as)
    simp_all only [tail_decP, Function.iterate_succ, Function.comp_apply]

theorem is_valid {α : Type u} {β : Type v} (as : Filtered α β) :
    valid as.p as := by
  have ⟨n, prop⟩ := as.baseTail.get.property
  simp only [valid, PartialListLike.head]

  conv =>
    intro not_nil
    arg 2
    arg 1
    rw [prop.eq_baseTail]

  have := prop.hit
  simp_all only [valid, implies_true]

structure Property {α : Type u} {β : Type v} (as : Filtered α β) (m : Nat) : Prop where
  hit : valid (inst := as.inst.toPartialListLike) as.p (as.inst.tail^[m] as.base)
  misses : ∀ {i : Nat}, i < m → ¬ valid as.p (inst := as.inst.toPartialListLike)
      (as.inst.tail^[i] as.base)
  not_nil_base : ¬ PartialListLike.isNil as ↔ ¬ as.inst.isNil (as.inst.tail^[m] as.base)
  isNil_base : PartialListLike.isNil as ↔ as.inst.isNil (as.inst.tail^[m] as.base)
  head_base not_nil :
    PartialListLike.head as not_nil = as.inst.head (as.inst.tail^[m] as.base)
    (not_nil_base.mp not_nil)
  tail_base : (PartialListLike.tail as).base = as.inst.tail^[m.succ] as.base

theorem property {α : Type u} {β : Type v} (as : Filtered α β) :
    ∃ m : Nat, Property as m := by
  have ⟨m, prop⟩ := as.baseTail.get.property
  use m
  constructor
  case not_nil_base =>
    simp only [PartialListLike.isNil]
    rw [prop.eq_baseTail]
  . exact prop.hit
  · exact prop.misses
  · simp only [PartialListLike.isNil]
    rw [prop.eq_baseTail]
  · intro not_nil
    simp [PartialListLike.head]
    conv =>
      lhs
      arg 1
      rw [prop.eq_baseTail]
  · simp only [PartialListLike.tail]
    rw [prop.eq_baseTail]
    simp only [Function.iterate_succ', Function.comp_apply]

structure PropertyTail {α : Type u} {β : Type v} (as : Filtered α β) (m : Nat) : Prop where
  hit : valid (inst := as.inst.toPartialListLike) as.p (as.inst.tail^[m] as.base)
  not_nil_base : ¬ PartialListLike.isNil (PartialListLike.tail as) →
    ¬ as.inst.isNil (as.inst.tail^[m] as.base)
  isNil_base : PartialListLike.isNil (PartialListLike.tail as) ↔
    as.inst.isNil (as.inst.tail^[m] as.base)
  head_base not_nil : PartialListLike.head (PartialListLike.tail as) not_nil =
    as.inst.head (as.inst.tail^[m] as.base) (not_nil_base not_nil)
  tail_base : (PartialListLike.tail (PartialListLike.tail as)).base =
    as.inst.tail^[m.succ] as.base
  le : 1 ≤ m

theorem property_tail {α : Type u} {β : Type v} (as : Filtered α β) :
    ∃ m : Nat, PropertyTail as m := by
  have ⟨m, prop⟩ := (PartialListLike.tail as).property
  have ⟨m', prop'⟩ := as.property
  have m_eq : m + Nat.succ m' = m + 1 + m':= by omega
  use m + 1 + m'
  constructor
  case not_nil_base =>
    intro not_nil
    have := prop.not_nil_base.mp not_nil
    revert this
    rw [prop'.tail_base]
    simp only [← Function.iterate_add_apply, m_eq, imp_self]
  . have := prop.hit
    simp_all only [prop'.tail_base, tail_inst, tail_p, Function.iterate_succ', Function.comp_apply,
      Function.iterate_add_apply, Function.iterate_zero, id_eq]
  · simp only [Function.iterate_succ', Function.iterate_zero, Function.comp_apply, id_eq,
      prop.isNil_base, tail_inst, prop'.tail_base, Function.iterate_add_apply, eq_iff_iff]
  · intro not_nil
    simp_all only [Function.iterate_succ', Function.iterate_zero, Function.comp_apply, id_eq,
      prop.head_base, tail_inst, prop'.tail_base, Function.iterate_add_apply]
  · simp only [Function.iterate_succ', Function.iterate_zero, Function.comp_apply, id_eq,
      prop.tail_base, tail_inst, prop'.tail_base, Function.iterate_add_apply]
  . omega

structure PropertyIterateTail {α : Type u} {β : Type v} (as : Filtered α β) (n m : Nat) : Prop where
  hit : valid (inst := as.inst.toPartialListLike) as.p (as.inst.tail^[m] as.base)
  not_nil_base : ¬ PartialListLike.isNil (PartialListLike.tail^[n] as) →
    ¬ as.inst.isNil (as.inst.tail^[m] as.base)
  isNil_base : PartialListLike.isNil (PartialListLike.tail^[n] as) ↔
    as.inst.isNil (as.inst.tail^[m] as.base)
  head_base not_nil : PartialListLike.head (PartialListLike.tail^[n] as) not_nil =
    as.inst.head (as.inst.tail^[m] as.base) (not_nil_base not_nil)
  tail_base : (PartialListLike.tail (PartialListLike.tail^[n] as)).base =
    as.inst.tail^[m.succ] as.base
  le : n ≤ m

theorem property_iterate_tail {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    ∃ m : Nat, PropertyIterateTail as n m := by
  induction n generalizing as with
  | zero =>
    have ⟨m, prop⟩ := as.property
    use m
    constructor
    . exact prop.hit
    · exact prop.isNil_base
    · exact prop.head_base
    · exact prop.tail_base
    · linarith
  | succ n ih =>
    replace ⟨m, ih⟩ := ih (as := PartialListLike.tail as)
    have ⟨m', prop'⟩ := as.property
    use m + 1 + m'
    constructor
    case not_nil_base =>
      simp only [Function.iterate_succ, Function.comp_apply, ih.isNil_base, tail_inst,
        prop'.tail_base, Function.iterate_add_apply, Function.iterate_zero,
        Function.apply_iterate_apply, id_eq, imp_self]
    · have := ih.hit
      simp_all only [tail_inst, tail_p, prop'.tail_base, Function.iterate_succ', Function.comp_apply,
        Function.iterate_add_apply, Function.iterate_zero, id_eq]
    · simp only [Function.iterate_succ, Function.comp_apply, ih.isNil_base, tail_inst,
        prop'.tail_base, Function.iterate_add_apply, Function.iterate_zero,
        Function.apply_iterate_apply, id_eq]
    · intro not_nil
      simp only [Function.iterate_succ_apply, ih.head_base not_nil, prop'.tail_base]
      simp only [← Function.iterate_succ_apply, ← Function.iterate_succ_apply', ←
        Function.iterate_add_apply]
      have : m + Nat.succ m' = m + 1 + m':= by omega
      simp only [this]
    · simp only [Function.iterate_succ_apply, ih.tail_base, prop'.tail_base]
      simp only [← Function.iterate_succ_apply, ← Function.iterate_succ_apply', ←
        Function.iterate_add_apply]
      congr
      omega
    · have := ih.le
      omega

-- theorem isNil_tail {α : Type u} {β : Type v} (as : Filtered α β) :
--     ∃ k : Nat,
--     PartialListLike.isNil (PartialListLike.tail as) ↔
--     as.inst.isNil (as.inst.tail^[k] as.base)  := by
--   have ⟨k_tail, prop_tail⟩ := (PartialListLike.tail as).baseTail.get.property
--   have ⟨k', prop⟩ := as.baseTail.get.property
--   simp only [PartialListLike.isNil]
--   rw [prop_tail.eq_baseTail]
--   simp [PartialListLike.tail]
--   rw [prop.eq_baseTail]
--   use k_tail + 1 + k'
--   simp only [Function.iterate_add_apply, Function.iterate_succ, Function.iterate_zero,
--     Function.comp_apply, id_eq]

-- theorem head_expand  {α : Type u} {β : Type v} {as : Filtered α β}
--     {k : Nat} (not_nil : _) :
--     ∃ not_nil',
--     PartialListLike.head (PartialListLike.tail^[k] as) not_nil =
--     as.inst.head ↑(Thunk.get (PartialListLike.tail^[k] as).baseTail) not_nil' := by
--   revert as
--   induction k with
--   | zero =>
--     intro as not_nil
--     use not_nil
--     simp only [PartialListLike.tail, Nat.zero_eq, Function.iterate_zero, id_eq,
--       PartialListLike.head, implies_true]
--   | succ k ih =>
--     intro as
--     have := ih (as := PartialListLike.tail as)
--     simp_all only [tail_inst, not_false_eq_true, implies_true, Function.iterate_succ,
--       Function.comp_apply]

-- theorem head_tail {α : Type u} {β : Type v} {as : Filtered α β} {not_nil : _} :
--     ∃ (k : Nat) (not_nil' : _),
--     PartialListLike.head (PartialListLike.tail as) not_nil =
--     as.inst.head (as.inst.tail^[k] as.base) not_nil' := by
--   have ⟨not_nil', head_eq⟩ := head_expand (as := as) (k := 1) not_nil
--   simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at head_eq
--   rw [head_eq]

--   have ⟨k_tail, prop_tail⟩ := (PartialListLike.tail as).baseTail.get.property
--   have ⟨k', prop⟩ := as.baseTail.get.property
--   use k_tail + 1 + k'

--   use ?not_nil'
--   case not_nil' =>
--     by_contra not_nil'
--     clear head_eq
--     revert not_nil
--     simp only [imp_false, not_not]
--     simp only [PartialListLike.isNil]
--     rw [prop_tail.eq_baseTail]
--     simp [PartialListLike.tail]
--     rw [prop.eq_baseTail]
--     simp_all only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
--       tail_inst, tail_decP, Function.iterate_add_apply]

--   conv =>
--     lhs
--     arg 1
--     rw [prop_tail.eq_baseTail]

--   simp only [PartialListLike.tail]

--   conv =>
--     lhs
--     arg 1
--     arg 3
--     rw [prop.eq_baseTail]

--   simp only [Function.iterate_add_apply, Function.iterate_succ, Function.iterate_zero,
--     Function.comp_apply, id_eq]


-- @[simp]
-- theorem iterate_tail_base {α : Type u} {β : Type v} (as : Filtered α β) (k : Nat)  :
--     ∃ (k' : Nat) (_ : k ≤ k') ,
--     (PartialListLike.tail^[k] as).base =
--     as.inst.tail^[k'] as.base := by
--   revert as
--   induction k with
--   | zero =>
--     intro as
--     use 0
--     simp only [PartialListLike.tail, Nat.zero_eq, Function.iterate_zero, id_eq, le_refl,
--       exists_const]
--   | succ k ih =>
--     intro as
--     have ⟨k', le , ih⟩ := ih (as := PartialListLike.tail as)
--     have ⟨k'', prop⟩ := property as
--     have := prop.tail_base
--     use k' + k'' + 1
--     constructor
--     case h.w =>
--       omega
--     simp_all only [tail_inst, Function.iterate_succ, Function.comp_apply,
--       Function.iterate_add_apply, Function.iterate_zero, id_eq]

-- theorem isNil_iterate_tail  {α : Type u} {β : Type v} (as : Filtered α β) (k : Nat) :
--     ∃ (k' : Nat) (_ : k ≤ k'),
--     PartialListLike.isNil (PartialListLike.tail^[k] as) ↔
--     as.inst.isNil (as.inst.tail^[k'] as.base)  := by
--   revert as
--   induction k with
--   | zero =>
--     intro as
--     have ⟨k', prop⟩ := as.baseTail.get.property
--     use k'
--     simp only [PartialListLike.isNil, Nat.zero_eq, Function.iterate_zero, id_eq, zero_le,
--       exists_const]
--     rw [prop.eq_baseTail]
--   | succ k ih =>
--     intro as
--     replace ⟨k', _, ih⟩ := ih (as := PartialListLike.tail as)
--     have ⟨k'', prop⟩ := property as
--     have := prop.tail_base
--     use k' + k'' + 1
--     constructor
--     case h.w =>
--       omega
--     simp_all only [tail_inst, Function.iterate_succ, Function.comp_apply,
--       Function.iterate_add_apply, Function.iterate_zero, id_eq]

-- theorem head_iterate_tail  {α : Type u} {β : Type v} (as : Filtered α β)
--     (k : Nat) (not_nil : _) :
--     ∃ (k' : Nat) (_ : k ≤ k') (not_nil' : _),
--     PartialListLike.head (PartialListLike.tail^[k] as) not_nil =
--     as.inst.head (as.inst.tail^[k'] as.base) not_nil' := by
--   revert as
--   induction k with
--   | zero =>
--     intro as not_nil
--     have ⟨k', prop⟩ := as.baseTail.get.property
--     use k'
--     simp only [PartialListLike.head, Nat.zero_eq, Function.iterate_zero, id_eq]
--     simp only [Nat.zero_eq, Function.iterate_zero, id_eq] at not_nil
--     constructor
--     case h.w =>
--       omega
--     constructor
--     case h.w =>
--       simp [PartialListLike.isNil] at not_nil
--       rw [prop.eq_baseTail] at not_nil
--       exact not_nil

--     conv =>
--       lhs
--       arg 1
--       rw [prop.eq_baseTail]
--   | succ k ih =>
--     intro as not_nil'
--     replace ⟨k', _, ih⟩ := ih (as := PartialListLike.tail as) (not_nil := not_nil')
--     have ⟨k'', prop⟩ := property as
--     have := prop.tail_base
--     use k' + k'' + 1
--     constructor
--     case h.w =>
--       omega
--     simp_all only [tail_inst, Function.iterate_succ, Function.comp_apply,
--       Function.iterate_add_apply, Function.iterate_zero, id_eq]

namespace baseTail

theorem tail_PropertyN {α : Type u} {β : Type v} {as : Filtered α β} {n : Nat} :
    PropertyN (PartialListLike.tail as).inst (PartialListLike.tail as).decP
      (PartialListLike.tail as).base (PartialListLike.tail as).baseTail.get n =
    PropertyN as.inst as.decP (PartialListLike.tail as).base
      (PartialListLike.tail as).baseTail.get n := by
  simp only [tail_inst, tail_decP]

theorem iterate_tail_PropertyN {α : Type u} {β : Type v} {as : Filtered α β} {n k : Nat} :
    PropertyN (PartialListLike.tail^[k] as).inst (PartialListLike.tail^[k] as).decP
      (PartialListLike.tail^[k] as).base (PartialListLike.tail^[k] as).baseTail.get n =
    PropertyN as.inst as.decP (PartialListLike.tail^[k] as).base
      (PartialListLike.tail^[k] as).baseTail.get n := by
  induction k generalizing as with
  | zero =>
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
  | succ n ih =>
    have := ih (as := PartialListLike.tail as)
    simp_all only [iterate_tail_inst, eq_iff_iff, tail_inst, tail_decP, Function.iterate_succ,
      Function.comp_apply]

end baseTail
-- namespace PropertyN

-- theorem p_head {α : Type u} {β : Type v} {as : Filtered α β} {n : Nat}
--     (prop : PropertyN as.inst as.decP as.base as.baseTail.get n) :
--     (not_nil : ¬ PartialListLike.isNil as) → as.p (PartialListLike.head as not_nil) := by
--   simp [PartialListLike.isNil, PartialListLike.head]
--   rw [prop.eq_baseTail]
--   have := prop.hit
--   simp_all only [valid, implies_true]

-- theorem eq_tail_base {α : Type u} {β : Type v} {as : Filtered α β} {n : Nat}
--     (prop : PropertyN as.inst as.decP as.base as.baseTail.get n) :
--     (PartialListLike.tail as).base = as.inst.tail^[n.succ] as.base := by
--   simp only [PartialListLike.tail, Function.iterate_succ_apply']
--   rw [prop.eq_baseTail]

-- theorem iff_isNil {α : Type u} {β : Type v} {as : Filtered α β} {n k : Nat}
--     (prop : PropertyN as.inst as.decP (PartialListLike.tail^[k] as).base
--       (PartialListLike.tail^[k] as).baseTail.get n) :
--     PartialListLike.isNil (PartialListLike.tail^[k] as) ↔
--     as.inst.isNil (as.inst.tail^[n] (PartialListLike.tail^[k] as).base) := by
--   simp [Filtered.isNil_expand]
--   have := prop.eq_baseTail
--   rw [prop.eq_baseTail]

-- theorem eq_head {α : Type u} {β : Type v} {as : Filtered α β} {n : Nat}
--     (prop : PropertyN as.inst as.decP as.base as.baseTail.get n) (not_nil : _) :
--     PartialListLike.head as not_nil =
--     as.inst.head (as.inst.tail^[n] as.base) (prop.iff_isNil.not.mp not_nil) := by
--   simp [PartialListLike.head]
--   have := prop.eq_baseTail
--   simp_all only

-- end baseTail.PropertyN


theorem Mem {α : Type u} {β : Type v} (a : α) (as : Filtered α β) :
    PartialListLike.Mem a as ↔ as.p a ∧ as.inst.Mem a as.base := by
  constructor
  · simp only [ProductiveListLike.Mem, forall_exists_index]
    intro n not_nil a_def
    have ⟨k, prop⟩ := as.property_iterate_tail n
    constructor
    · have := (PartialListLike.tail^[n] as).is_valid not_nil
      simp_all only [iterate_tail_p]
    · subst a_def
      have not_nil' := prop.not_nil_base not_nil
      use k
      use not_nil'
      exact id (prop.head_base not_nil).symm
  ·
    intro ⟨p_a, k, not_nil, a_eq⟩
    subst a_eq
    have iterateTo : ∃ (n k' : Nat),
        k ≤ k' ∧ PropertyIterateTail as n k' := by
      use k
      have ⟨k', prop⟩ := as.property_iterate_tail k
      use k'
      use prop.le
    have := Classical.dec
    have ⟨n, ⟨k', k_le_k', prop⟩, least_n⟩ := Nat.findX iterateTo
    clear iterateTo
    unfold PartialListLike.Mem
    use n
    by_cases n_zero : n = 0
    · subst n_zero
      simp?
      have := prop
      sorry
    · have ⟨k', prop⟩ := as.property_iterate_tail n
      sorry




    subst a_eq

    let is_match k' := ∃ not_nil', PartialListLike.Mem
      (as.inst.head (as.inst.tail^[k'] as.base) not_nil') as

    by_cases exists_pred : ∃ k_pred < k,
      is_match k_pred ∧ ∀ i : Nat, (k_pred < i) → (i < k) → ¬ is_match i
    · sorry
    · simp? at exists_pred
      sorry


    -- intro ⟨p_a, k, not_nil, a_eq⟩
    -- subst a_eq
    -- unfold PartialListLike.Mem
    -- induction as with
    -- | @mk inst p decP base baseTail =>
    -- simp only at p_a not_nil
    -- induction k generalizing base with
    -- | zero =>
    --   let as : Filtered α β := {p := p, base := base, baseTail := baseTail}
    --   have ⟨k', prop⟩ := as.property
    --   use 0
    --   simp only [Nat.zero_eq, Function.iterate_zero, id_eq] at p_a not_nil ⊢
    --   by_cases k_zero : 0 < k'
    --   case pos =>
    --     have ⟨_, _⟩ := prop.misses 0 k_zero
    --       |> not_forall.mp
    --     contradiction
    --   simp only [not_lt, nonpos_iff_eq_zero] at k_zero
    --   have not_nil_iff := prop.isNil_base
    --   simp only [k_zero, Function.iterate_zero, id_eq] at not_nil_iff
    --   have not_nil' := not_nil_iff.not.mpr not_nil
    --   use not_nil'
    --   simp_all only [prop.head_base, Function.iterate_zero, id_eq]
    -- | succ k ih =>
    --   -- simp only [Function.iterate_succ, Function.comp_apply] at p_a not_nil
    --   replace ⟨k', not_nil', ih⟩ := ih (inst.tail base) (mkBaseTail (inst.tail base)) not_nil p_a
    --   simp only [←Function.iterate_succ_apply] at ih
    --   use k'.succ
    --   use sorry
    --   rw [ih]
    --   simp only [Function.iterate_succ', Function.comp_apply]
    --   generalize eq : ({p := p, base := base, baseTail := baseTail} : Filtered α β) = as
    --   sorry


    --   intro as not_nil p_a
    --   have ⟨k', prop⟩ := as.property
    --   have ⟨k_tail, prop_tail⟩ := as.property_tail
    --   by_cases k'_k : k.succ < k'
    --   · have := prop.misses k k'_k


    --     sorry
    --   · simp only [not_lt] at k'_k
    --     have := ProductiveListLike.isNil_iterate_tail_of_isNil_iterate_tail k'_k
    --       (inst := as.inst.toProductiveListLike) (as := as.base) |> not_imp_not.mpr
    --       <| not_nil


    --     sorry

-- theorem head_iterate_tail_base_of_head_iterate_tail  {α : Type u} {β : Type v}
--     (as : Filtered α β) (n : Nat) (not_nil : _) :
--     ∃ (m : Nat) (not_nil' : _ ),
--     PartialListLike.head (PartialListLike.tail^[n] as) not_nil =
--     as.inst.head (as.inst.tail^[m] as.base) not_nil' := by
--   revert as
--   induction n with
--   | zero =>
--     simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
--     intro as not_nil
--     have ⟨m, prop⟩ := as.baseTail.get.property
--     use m
--     rw [prop.eq_head not_nil]
--     simp_all only [prop.iff_isNil.not.mp not_nil, not_false_eq_true, exists_const]
--   | succ n ih =>
--     simp only [Function.iterate_succ_apply]
--     intro as not_nil
--     have ⟨m, prop⟩ := (PartialListLike.tail as).baseTail.get.property
--     have := ih (as := PartialListLike.tail as) (not_nil := ?not_nil')
--     case not_nil' =>
--       sorry
--     sorry

instance instListLike {α : Type u} {β : Type v} :
    ListLike α (Filtered α β) where
  toPartialListLike := instPartialListLike
  terminal_isNil as := by
    have ⟨n, prop⟩ := as.baseTail.get.property
    have ⟨n', prop'⟩:= (PartialListLike.tail as).baseTail.get.property
    simp only [PartialListLike.isNil] at *
    rw [prop.eq_baseTail]
    rw [prop'.eq_baseTail]
    rw [prop.eq_tail_base]
    simp only [←Function.iterate_add_apply]
    apply ProductiveListLike.isNil_iterate_tail_of_isNil_iterate_tail
      (inst := as.inst.toProductiveListLike)
    omega
  consistent_mem a as := by
    constructor
    · simp [PartialListLike.Mem, Membership.mem]
      intro n not_nil a_def
      have ⟨k, prop⟩ := (PartialListLike.tail^[n] as).baseTail.get.property
      have := prop.p_head not_nil
      simp_all only [iterate_tail_p, true_and]
      apply as.inst.consistent_mem
        (PartialListLike.head (PartialListLike.tail^[n] as) not_nil) as.base |>.mp
      exact head_iterate_tail_base_of_head_iterate_tail as n _
    · simp [Membership.mem, PartialListLike.Mem]
      intro valid mem
      have ⟨k, not_nil, a_def⟩ := (as.inst.consistent_mem a as.base).mpr mem
      subst a_def
      have := head_iterate_tail_base_of_head_iterate_tail as k ?not_nil
      case not_nil =>
        sorry

      sorry
  finite as := by
    have ⟨n , finite⟩ := as.inst.finite as.base
    use n
    revert finite as
    induction n with
    | zero =>
      intro as
      have ⟨n, prop⟩ := as.baseTail.get.property
      simp only [Nat.zero_eq, Function.iterate_zero, id_eq, PartialListLike.isNil,
        Function.iterate_succ, Function.comp_apply, Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int,
        Nat.cast_ofNat, eq_mpr_eq_cast, prop.eq_baseTail]
      apply ProductiveListLike.isNil_iterate_tail
        (inst := as.inst.toProductiveListLike)
    | succ n ih =>
      intro as finite
      apply ih (PartialListLike.tail as)
      have ⟨k, prop⟩ := as.baseTail.get.property
      rw [prop.eq_tail_base]
      simp only [←Function.iterate_add_apply]
      revert finite
      apply ProductiveListLike.isNil_iterate_tail_of_isNil_iterate_tail
        (inst := as.inst.toProductiveListLike)
      omega
