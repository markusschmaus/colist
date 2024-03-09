import Colist.ListLike.AnyListLike
import Colist.ListLike.ProductiveListLike.Mem
import Colist.ListLike.ProductiveListLike.Pairwise
import Colist.util.Option
import Colist.util.Function

universe u v

namespace ListLike

namespace Filtered

def validBaseTail {α : Type u} {β : Type v} [inst : PartialListLike α β] (p : α → Prop)
    (baseTail : β) : Prop :=
  (not_nil : ¬ PartialListLike.isNil baseTail) → p (PartialListLike.head baseTail not_nil)

instance {α : Type u} {β : Type v} [inst : ListLike α β] (p : α → Prop)
    [decP : DecidablePred p]  (baseTail : β) : Decidable (validBaseTail p baseTail) :=
  if nil? : PartialListLike.isNil baseTail then
    isTrue <| by
      simp_all only [validBaseTail, not_true_eq_false, IsEmpty.forall_iff]
  else if valid? : p (PartialListLike.head baseTail nil?) then
    isTrue <| by
      simp_all only [validBaseTail, not_false_eq_true, forall_true_left]
  else
    isFalse <| by
      simp_all only [validBaseTail, not_false_eq_true, forall_true_left]

namespace baseTail

structure PropertyK {α : Type u} {β : Type v} (inst : ListLike α β) {p : α → Prop}
    (decP : DecidablePred p) (base : β) (baseTail : β) (k : Nat) : Prop where
  hit : validBaseTail p (inst.tail^[k] base)
  misses {i : Nat} : i < k → ¬ validBaseTail p (inst.tail^[i] base)
  eq_baseTail : baseTail = inst.tail^[k] base

structure Result {α : Type u} {β : Type v} (inst : ListLike α β) (p : α → Prop)
    (decP : DecidablePred p) (base : β) where
  baseTail : β
  baseTailIter : Nat
  property : PropertyK inst decP base baseTail baseTailIter

end baseTail

def getBaseTail  {α : Type u} {β : Type v} (inst : ListLike α β) {p : α → Prop}
    (decP : DecidablePred p) (base : β) : baseTail.Result inst p decP base :=

  let rec go (candidate : β) (n : Nat)
      (iterate_tail : candidate = PartialListLike.tail^[n] base)
      (misses : ∀ (i : Nat), i < n → ¬ validBaseTail p (PartialListLike.tail^[i] base)) :
      baseTail.Result inst p decP base :=
    if valid? : validBaseTail p candidate then
      baseTail.Result.mk candidate n <| by
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
          simp only [validBaseTail, not_forall] at valid?
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
    Thunk (baseTail.Result inst p decP base) :=
  Thunk.mk (fun () => getBaseTail inst decP base)

end Filtered

structure Filtered (α : Type u) (β : Type v) where
  [inst : ListLike α β]
  p : α → Prop
  [decP : DecidablePred p]
  base : β
  cache : Thunk (Filtered.baseTail.Result inst p decP base) :=
    Filtered.mkBaseTail base

namespace Filtered

def baseTailIter {α : Type u} {β : Type v} (as : Filtered α β) : Nat :=
  as.cache.get.baseTailIter

def baseTail {α : Type u} {β : Type v} (as : Filtered α β) : β :=
  as.cache.get.baseTail


instance instMembership {α : Type u} {β : Type v} :
    Membership α (Filtered α β) where
  mem a as := as.p a ∧ as.inst.instMembership.mem a as.base

instance instPartialListLike {α : Type u} {β : Type v} :
    PartialListLike α (Filtered α β) where
  isNil as := as.inst.isNil as.baseTail
  head as := as.inst.head as.baseTail
  tail as :=
    let newBase := as.inst.tail as.baseTail
    {inst := as.inst, p := as.p, decP := as.decP, base := newBase}

theorem hit {α : Type u} {β : Type v} (as : Filtered α β) :
    validBaseTail (inst := as.inst.toPartialListLike)
    as.p (as.inst.tail^[as.baseTailIter] as.base) := by
  simp only [baseTailIter]
  induction as.cache.get with
  | mk baseTail baseTailIter prop =>
  have := prop.hit
  unfold validBaseTail at *
  simp_all only [implies_true]

theorem misses {α : Type u} {β : Type v} (as : Filtered α β) {i : Nat} :
    i < as.baseTailIter → ¬ validBaseTail (inst := as.inst.toPartialListLike)
    as.p (as.inst.tail^[i] as.base) := by
  simp only [baseTailIter]
  induction as.cache.get with
  | mk baseTail baseTailIter prop =>
  simp only
  intro lt
  have := prop.misses lt
  unfold validBaseTail at *
  simp_all only [not_forall]

@[simp]
theorem eq_baseTail {α : Type u} {β : Type v} (as : Filtered α β) :
    as.baseTail = as.inst.tail^[as.baseTailIter] as.base := by
  simp only [baseTailIter, baseTail]
  induction as.cache.get with
  | mk baseTail baseTailIter prop =>
  have := prop.eq_baseTail
  simp_all only

@[simp]
theorem tail_base {α : Type u} {β : Type v} (as : Filtered α β) :
    (PartialListLike.tail as).base = as.inst.tail^[as.baseTailIter.succ] as.base := by
  simp only [baseTail, baseTailIter, PartialListLike.tail]
  induction as.cache.get with
  | mk baseTail baseTailIter prop =>
  simp_all only [prop.eq_baseTail, Function.iterate_succ', Function.comp_apply]

@[simp]
theorem tail_p {α : Type u} {β : Type v} (as : Filtered α β) :
    (PartialListLike.tail as).p = as.p := rfl

@[simp]
theorem iterate_tail_p {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    (PartialListLike.tail^[n] as).p = as.p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp_all only [Function.iterate_succ', Function.comp_apply, tail_p]

@[simp]
theorem tail_inst {α : Type u} {β : Type v} (as : Filtered α β) :
    (PartialListLike.tail as).inst = as.inst := rfl

@[simp]
theorem iterate_tail_inst {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    (PartialListLike.tail^[n] as).inst = as.inst := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp_all only [Function.iterate_succ', Function.comp_apply, tail_inst]

@[simp]
theorem tail_decP {α : Type u} {β : Type v} (as : Filtered α β) :
    (PartialListLike.tail as).decP = as.decP := rfl

@[simp]
theorem iterate_tail_decP_heq {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    HEq (PartialListLike.tail^[n] as).decP as.decP := by
  induction n generalizing as with
  | zero =>
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq, heq_eq_eq]
  | succ n ih =>
    have := ih (as := PartialListLike.tail as)
    simp_all only [tail_decP, Function.iterate_succ, Function.comp_apply]

@[simp]
theorem tail_baseTail {α : Type u} {β : Type v} (as : Filtered α β) :
    as.inst.tail (as.baseTail) = (PartialListLike.tail as).base := rfl

noncomputable def baseIterTailIterate.model {α : Type u} {β : Type v}
    (as : Filtered α β) : Nat → Nat
  | Nat.zero => 0
  | Nat.succ n =>
    (baseIterTailIterate.model as n) +
      (PartialListLike.tail^[n] as).baseTailIter.succ

@[simp]
theorem baseIterTailIterate.model_succ {α : Type u} {β : Type v}
    (as : Filtered α β) (n : Nat) :
    baseIterTailIterate.model as n.succ = baseIterTailIterate.model as n +
    (PartialListLike.tail^[n] as).baseTailIter.succ := by
  rfl

structure baseIterTailIterate.Property {α : Type u} {β : Type v}
    (as : Filtered α β) (n : Nat) (out : Nat) :
    Prop where
  eq : (PartialListLike.tail^[n] as).base = as.inst.tail^[out] as.base
  model : out = baseIterTailIterate.model as n
  n_le : n ≤ out

def baseIterTailIterate {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    Subtype (baseIterTailIterate.Property as n) :=
  let rec go (acc : Nat) (current : Filtered α β) (m : Nat)
      (eq_current : current = PartialListLike.tail^[m] as)
      (acc_valid : baseIterTailIterate.Property as m acc)
      (le : m ≤ n) :
      Subtype (baseIterTailIterate.Property as n) :=
    if m_zero : m = n then
      Subtype.mk acc <| by
        simp_all only
    else
      have : current.inst = as.inst := by
        simp_all only [iterate_tail_inst]
      have acc_valid' := by
        constructor
        . have := acc_valid.eq
          simp_all only [iterate_tail_inst, Function.iterate_succ', Function.comp_apply, tail_base,
            Function.iterate_add_apply]
        . have := acc_valid.model
          simp_all only [iterate_tail_inst]
          unfold baseIterTailIterate.model
          induction m with
          | zero =>
            simp only [Nat.zero_eq, Function.iterate_zero, id_eq, add_zero, self_eq_add_left]
            rfl
          | succ m _ =>
            simp only [Function.iterate_succ, Function.comp_apply, baseIterTailIterate.model_succ]
            ring
        · have := acc_valid.n_le
          omega
      have eq_current' := by
        simp_all only [Function.iterate_succ', Function.comp_apply]
      have le' := by
        omega
      -- Show termination:
      have : n - m.succ < n - m := by
        omega
      go (current.baseTailIter.succ + acc) (PartialListLike.tail current) m.succ
        eq_current' acc_valid' le'
  termination_by n - m

  have acc_valid := by
    constructor
    · rfl
    · rfl
    · omega

  go 0 as 0 rfl acc_valid (by omega)

@[simp]
theorem iterate_tail_base {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    (PartialListLike.tail^[n] as).base = as.inst.tail^[baseIterTailIterate as n] as.base := by
  exact baseIterTailIterate as n |>.property.eq

structure  baseTailIterTailIterate.Property {α : Type u} {β : Type v}
    (as : Filtered α β) (n : Nat) (out : Nat) :
    Prop where
  eq : (PartialListLike.tail^[n] as).baseTail = as.inst.tail^[out] as.base
  n_le : n ≤ out

@[simp]
def baseTailIterTailIterate {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    Subtype (baseTailIterTailIterate.Property as n) :=
    Subtype.mk (baseTailIter (PartialListLike.tail^[n] as) + baseIterTailIterate as n) <| by
  have prop := baseIterTailIterate as n |>.property
  constructor
  · simp only [eq_baseTail, iterate_tail_inst, iterate_tail_base,
      ← Function.iterate_add_apply]
  · have := prop.n_le
    omega

def baseTailIterTailIterate' {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    (baseTailIterTailIterate as n).val =
    baseIterTailIterate as n + baseTailIter (PartialListLike.tail^[n] as) := by
  simp only [baseTailIterTailIterate]
  ring_nf

@[simp]
theorem baseIterTailIterate_succ {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    (baseIterTailIterate as n.succ).val = (baseTailIterTailIterate as n).val.succ := by
  have model := baseIterTailIterate as n |>.property.model
  have model_succ := baseIterTailIterate as n.succ |>.property.model
  simp only [baseIterTailIterate.model_succ] at model_succ
  simp_all only [baseTailIterTailIterate]
  ring
  rfl

@[simp]
theorem iterate_tail_baseTail {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    (PartialListLike.tail^[n] as).baseTail =
    as.inst.tail^[baseTailIterTailIterate as n] as.base := by
  exact baseTailIterTailIterate as n |>.property.eq

@[simp]
theorem baseTailIterTailIterate_zero {α : Type u} {β : Type v} (as : Filtered α β) :
    baseTailIterTailIterate as 0 = as.baseTailIter := rfl

theorem isNil_iterate_tail {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat) :
    PartialListLike.isNil (PartialListLike.tail^[n] as) ↔
    as.inst.isNil (as.inst.tail^[baseTailIterTailIterate as n] as.base) := by
  simp only [PartialListLike.isNil, iterate_tail_inst, eq_baseTail, iterate_tail_base,
    baseTailIterTailIterate, Function.iterate_add_apply]

theorem head_iterate_tail {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat)
    (not_nil : _) :
    PartialListLike.head (PartialListLike.tail^[n] as) not_nil =
    as.inst.head (as.inst.tail^[baseTailIterTailIterate as n] as.base)
    (isNil_iterate_tail as n |>.not.mp not_nil) := by
  simp only [PartialListLike.head, eq_baseTail, iterate_tail_inst, iterate_tail_base]
  apply PartialListLike.head_eq_of_head?_eq
  · simp only [baseTailIterTailIterate, Function.iterate_add_apply]
  · simp only [iterate_tail_inst]

instance instListLike {α : Type u} {β : Type v} :
    ListLike α (Filtered α β) where
  toPartialListLike := instPartialListLike
  terminal_isNil as := by
    simp only [PartialListLike.isNil]
    simp only [eq_baseTail, tail_inst, tail_base]
    simp only [eq_baseTail, iterate_tail_inst, iterate_tail_base, ←Function.iterate_add_apply]
    intro is_nil
    refine ProductiveListLike.isNil_iterate_tail_of_isNil_iterate_tail ?_ is_nil
    omega
  consistent_mem a as:= by
    constructor
    case mp =>
      unfold PartialListLike.Mem
      intro ⟨n, not_nil, a_def⟩
      simp [Membership.mem]
      constructor
      · subst a_def
        simp only [isNil_iterate_tail] at not_nil
        simp only [PartialListLike.head, eq_baseTail, iterate_tail_inst, iterate_tail_base]
        have := (PartialListLike.tail^[n] as).hit <| by
          simp_all only [PartialListLike.isNil, iterate_tail_inst, eq_baseTail, iterate_tail_base,
            baseTailIterTailIterate, not_false_eq_true]
        simp_all only [iterate_tail_inst, iterate_tail_base, iterate_tail_p]
      · apply as.inst.consistent_mem a as.base |>.mp
        subst a_def
        unfold PartialListLike.Mem
        simp [isNil_iterate_tail] at not_nil
        use(baseTailIterTailIterate as n).val
        use not_nil
        simp only [head_iterate_tail]
    case mpr =>
      intro ⟨p_a, a_def⟩

      -- Find the smallest n such that k ≤ (baseTailIterTailIterate as n).val
      replace ⟨k, not_nil, a_def⟩ := as.inst.consistent_mem a as.base |>.mpr a_def
      have exists_n: ∃ (n : Nat), k ≤ (baseTailIterTailIterate as n).val := by
        use k
        exact (baseTailIterTailIterate as k).property.n_le
      let ⟨n, k_le, least⟩ := Nat.findX exists_n
      clear exists_n
      use n

      -- Show that for this n actually k = (baseTailIterTailIterate as n).val
      have k_eq : k = (baseTailIterTailIterate as n).val := by
        apply Nat.eq_iff_le_and_ge.mpr
        simp_all only [not_le, true_and]

        have le_k : (baseIterTailIterate as n).val ≤ k := by
          by_cases n_zero : n = 0
          · subst n_zero
            exact Int.ofNat_le.mp (Int.NonNeg.mk (k + 0))
          · have n_def := Nat.succ_pred n_zero
            generalize n.pred = m at *
            subst n_def
            replace least := least (m := m) <| by
              omega
            simp_all only [baseTailIterTailIterate, Function.iterate_succ, Function.comp_apply,
              baseIterTailIterate_succ, Nat.succ_ne_zero, not_false_eq_true, not_le, Nat.succ_le]

        have ⟨k', k_def⟩ := Nat.exists_eq_add_of_le le_k
        have k'_eq : ¬ k' < baseTailIter (PartialListLike.tail^[n] as) := by
          by_contra k'_lt
          have := (PartialListLike.tail^[n] as).misses k'_lt
          revert this
          unfold validBaseTail
          simp only [iterate_tail_inst, iterate_tail_p, iterate_tail_base, imp_false, not_not]
          intro not_nil
          revert p_a
          apply Iff.mp
          apply iff_of_eq
          apply congrArg
          apply PartialListLike.head_eq_of_head?_eq
          · rw [k_def]
            simp only [← Function.iterate_add_apply]
            ring_nf
          · simp_all only [baseTailIterTailIterate, not_le, le_add_iff_nonneg_right, zero_le,
            not_exists, iterate_tail_inst]

        simp_all only [baseTailIterTailIterate, le_add_iff_nonneg_right, zero_le, not_lt, ge_iff_le]
        omega
      subst k_eq

      -- The rest is mopping up
      simp only [isNil_iterate_tail]
      use not_nil
      subst a_def
      apply PartialListLike.head_eq_of_head?_eq
      · simp only [baseTailIterTailIterate, eq_baseTail, iterate_tail_inst, iterate_tail_base, ←
        Function.iterate_add_apply]
      · apply congrFun
        simp only [iterate_tail_inst]
  finite as := by
    unfold PartialListLike.isFinite
    have ⟨n, is_nil⟩ := as.inst.finite as.base
    use n
    simp only [PartialListLike.isNil, eq_baseTail, iterate_tail_inst,
      iterate_tail_base, ←Function.iterate_add_apply]

    refine ProductiveListLike.isNil_iterate_tail_of_isNil_iterate_tail ?_ is_nil
    have := (baseIterTailIterate as n).property.n_le
    omega
