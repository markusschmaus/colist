import Colist.ListLike.AnyListLike
import Colist.ListLike.ProductiveListLike.Mem
import Colist.ListLike.ProductiveListLike.Pairwise
import Colist.util.Option
import Colist.util.Function

universe u v

namespace ListLike

structure PartialFiltered (α : Type u) (β : Type v) where
  [inst : ListLike α β]
  p : α → Prop
  [decP : DecidablePred p]
  head? : Option α
  baseTail : β

structure Filtered (α : Type u) (β : Type v) extends (PartialFiltered α β) where
  valid : (h : ¬ head? = none) → p (head?.get (Option.ne_none_iff_isSome.mp h))
  terminal_none : head? = none → inst.isNil baseTail

namespace Filtered

abbrev mk' {α : Type u} {β : Type v} [inst : ListLike α β] (p : α → Prop) [decP : DecidablePred p]
    (head? : Option α) (baseTail : β) (valid : (h : ¬ head? = none) → p (head?.get (Option.ne_none_iff_isSome.mp h)))
    (terminal_none : head? = none → inst.isNil baseTail) : Filtered α β :=
  Filtered.mk (PartialFiltered.mk (inst := inst) (decP := decP) head? baseTail) valid terminal_none

inductive tail.Property.hit {α : Type u} {β : Type v} (x : PartialFiltered α β)
    (out : Filtered α β) (n : Nat) : Prop where
  | found
    (tail_eq : out.baseTail = x.inst.tail^[n + 1] x.baseTail)
    (inst_eq : out.inst = x.inst)
    (not_nil : ¬ x.inst.isNil (x.inst.tail^[n] x.baseTail))
    (head_eq : x.inst.head (x.inst.tail^[n] x.baseTail) not_nil = out.head?)
    (p_head : ∃ head, out.head? = some head ∧ x.p head)
  | empty
    (tail_eq : out.baseTail = x.inst.tail^[n + 1] x.baseTail)
    (inst_eq : out.inst = x.inst)
    (baseTail_nil : x.inst.isNil out.baseTail)
    (head_none : out.head? = none)

@[simp]
def tail.Property.hit.tail_eq {α : Type u} {β : Type v} {x : PartialFiltered α β}
    {out : Filtered α β} {n : Nat} (h : tail.Property.hit x out n) :=
  match h with
  | tail.Property.hit.found tail_eq _ _ _ _ => tail_eq
  | tail.Property.hit.empty tail_eq _ _ _ => tail_eq

@[simp]
def tail.Property.hit.inst_eq {α : Type u} {β : Type v} {x : PartialFiltered α β}
    {out : Filtered α β} {n : Nat} (h : tail.Property.hit x out n) :=
  match h with
  | tail.Property.hit.found _ inst_eq _ _ _ => inst_eq
  | tail.Property.hit.empty _ inst_eq _ _ => inst_eq

structure tail.Property.miss {α : Type u} {β : Type v} (x : PartialFiltered α β)
    (n : Nat) : Prop where
  not_nil : ¬ x.inst.isNil (x.inst.tail^[n] x.baseTail)
  not_p_head : ¬ (x.p <| x.inst.head (x.inst.tail^[n] x.baseTail) not_nil)

abbrev tail.Property {α : Type u} {β : Type v} (x : PartialFiltered α β)
    (out : Filtered α β) : Prop :=
  ∃ n : Nat, tail.Property.hit x out n ∧ ∀ m < n, tail.Property.miss x m

def tailX {α : Type u} {β : Type v} (x : PartialFiltered α β) :
    Subtype (tail.Property x) :=
  let rec loop (current : β) (n : Nat)
      (h : current = x.inst.tail^[n] x.baseTail ∧ ∀ m < n, tail.Property.miss x m) :
      Subtype (tail.Property x) :=
    if is_nil : x.inst.isNil current then
      let result := Filtered.mk'
        (inst := x.inst) (p := x.p) (decP := x.decP) (head? := none)
        (baseTail := x.inst.tail current)
        (valid := fun h => (h rfl).elim)
        (terminal_none := fun _ => x.inst.terminal_isNil current is_nil)
      Subtype.mk result <| by
        use n
        constructor
        · apply tail.Property.hit.empty
          · simp_all only [h.left, true_and, Function.iterate_succ, Function.comp_apply,
              Function.apply_iterate_apply]
          . rfl
          · exact x.inst.terminal_isNil current is_nil
          · exact rfl
        · exact h.right
    else
      let head := x.inst.head current is_nil
      let _ := x.decP head
      if proof : x.p head then
        let result := Filtered.mk'
          (inst := x.inst) (p := x.p) (decP := x.decP) (head? := head)
          (baseTail := x.inst.tail current)
          (valid := fun _ => proof)
          (terminal_none := by simp_all only [IsEmpty.forall_iff])
        Subtype.mk result <| by
          use n
          constructor
          · apply tail.Property.hit.found
            · simp only [Function.iterate_succ, Function.comp_apply, h.left,
                Function.apply_iterate_apply]
            · rfl
            · simp only [h.left]
            · simp only [Option.some.injEq, exists_eq_left', proof]
            · simp only [← h.left, is_nil, not_false_eq_true]
          · exact h.right
      else
        have : ∀ (m : ℕ),
            (∀ n < m, ¬x.inst.isNil ((x.inst.tail)^[n] (x.inst.tail current))) →
            ¬x.inst.isNil (x.inst.tail^[m] current)
          | 0, _ => by
            simp only [Function.iterate_zero, id_eq, is_nil, not_false_eq_true]
          | m + 1, h => by
            simp only [Function.iterate_succ, Function.comp_apply, h m (Nat.lt_succ_self m),
              not_false_eq_true]
        loop (x.inst.tail current) n.succ <| by
          unfold_let head at proof
          constructor
          · simp_all only [Function.iterate_succ_apply']
          · intro m m_lt_n_succ
            by_cases m_lt_n : m < n
            · simp_all only
            · have m_eq_n : m = n := by
                omega
              subst m_eq_n
              constructor
              · simp_all only [h.left, true_and, Nat.lt_succ_self,
                  lt_self_iff_false, not_false_eq_true]
              · rw [←h.left]
                exact is_nil
  termination_by Nat.find (x.inst.finite current)

  loop x.baseTail 0 ⟨rfl, by omega⟩

abbrev tail {α : Type u} {β : Type v} (x : Filtered α β)  := (tailX x.toPartialFiltered).val

theorem nil_of_baseTail_nil {α : Type u} {β : Type v} (x : Filtered α β) :
    x.inst.isNil x.baseTail → x.tail.head? = none :=
  by
    intro baseTail_nil
    have ⟨n, ⟨hit, _⟩⟩ := tailX x.toPartialFiltered |>.property
    have := hit.inst_eq
    have := hit.tail_eq
    simp_all only [Function.iterate_succ, Function.comp_apply]
    induction hit with
    | found _ _ not_nil head_eq _ =>
      by_contra
      clear head_eq
      revert not_nil
      simp only [imp_false, not_not]
      apply ProductiveListLike.iterate_terminal_isNil (inst := x.inst.toProductiveListLike)
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq]
    | empty _ _ _ head_none =>
      exact head_none

@[simp]
theorem iterate_tail_inst {α : Type u} {β : Type v} (x : Filtered α β) (n : Nat) :
    (tail^[n] x).inst = x.inst := by
  revert x
  induction n with
  | zero =>
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq, implies_true]
  | succ n ih =>
    intro x
    replace ih := ih (tail x)
    have ⟨n, ⟨hit, misses⟩⟩ := tailX x.toPartialFiltered |>.property
    simp_all only [tail, Function.iterate_succ, Function.comp_apply]
    exact hit.inst_eq

instance instPartialListLike {α : Type u} {β : Type v} :
    PartialListLike α (Filtered α β) where
  isNil x := x.head? = none
  head x h := x.head?.get (Option.ne_none_iff_isSome.mp h)
  tail := tail

instance instListLike {α : Type u} {β : Type v} :
    ListLike α (Filtered α β) where
  toPartialListLike := instPartialListLike
  terminal_isNil as := by
    simp only [tail, PartialListLike.isNil, PartialListLike.tail]
    have ⟨n, ⟨hit, _⟩⟩ := tailX as.toPartialFiltered |>.property
    induction hit with
    | found _ _ not_nil _ _ =>
      intro head_none
      have := as.terminal_none head_none
      have := as.inst.iterate_terminal_isNil as.baseTail n this
      contradiction
    | empty _ _ _ head_none =>
      intro _
      exact head_none
  finite as := by
    have m_of_n (n : Nat) : ∃ (m : Nat), (n ≤ m) ∧
        (Filtered.tail^[n] as).baseTail = as.inst.tail^[m] as.baseTail := by
      revert as
      induction n with
      | zero =>
        intro as
        use 0
        simp_all only [Nat.zero_eq, le_refl, Function.iterate_zero, id_eq, and_self]
      | succ n ih =>
        intro as
        have ⟨m', n_le_m', ih'⟩ := ih (Filtered.tail as)
        have ⟨n', ⟨hit, _⟩⟩ := tailX as.toPartialFiltered |>.property
        use m' + n' + 1
        constructor
        · omega
        · have := hit.tail_eq
          have := hit.inst_eq
          simp_all only [Function.iterate_add_apply, Function.iterate_succ, Function.iterate_zero,
            Function.comp_apply, id_eq]
    have ⟨n, nil_it_n⟩ := as.inst.finite as.baseTail
    have ⟨m, n_le_m, tail_n_eq_tail_m⟩ := m_of_n n
    have ⟨k, k_def⟩ := Nat.exists_eq_add_of_le n_le_m
    rw [add_comm] at k_def
    subst k_def
    use n + 1
    simp only [PartialListLike.isNil, PartialListLike.tail, Function.iterate_succ_apply, ← Function.apply_iterate_apply]
    have nil_tail : as.inst.isNil (tail^[n] as).baseTail := by
      simp_all only [le_add_iff_nonneg_left, zero_le, Function.iterate_add, Function.comp_apply,
        ProductiveListLike.iterate_terminal_isNil (inst := as.inst.toProductiveListLike)]
    have ⟨n', ⟨hit, _⟩⟩ := tailX (tail^[n] as).toPartialFiltered |>.property
    have := hit.inst_eq
    refine' nil_of_baseTail_nil (tail^[n] as) _
    simp_all only [le_add_iff_nonneg_left, zero_le, iterate_tail_inst]

end Filtered

abbrev filter {α : Type u} {β : Type v} [ListLike α β] (p : α → Prop)
    [DecidablePred p] (as : β) : Filtered α β :=
  Filtered.tailX <| PartialFiltered.mk p none as

theorem exists_iterate_tail_eq {α : Type u} {β : Type v} [ListLike α β]
    (p : α → Prop) [DecidablePred p] (as : β) (n : Nat) :
    ∃ (m : Nat), (PartialListLike.tail^[n] (filter p as)) = filter p (PartialListLike.tail^[m] as) := by
  revert as
  induction n with
  | zero =>
    intro as
    use 0
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
  | succ n ih =>
    simp only [PartialListLike.tail, Function.iterate_succ, Function.comp_apply]
    intro as
    replace ⟨k, ih⟩ := ih as
    have ⟨j, ⟨hit, _⟩⟩ := Filtered.tailX (Filtered.tail^[n] (filter p as)).toPartialFiltered |>.property
    have := hit.tail_eq
    rw [←Filtered.tail] at this
    use k + j
    simp_all?
    sorry

theorem mem_filter {α : Type u} {β : Type v} [ListLike α β] (p : α → Prop)
    [DecidablePred p] (as : β) (a : α) :
    a ∈ filter p as ↔ a ∈ as ∧ p a := by
  constructor
  · simp [ProductiveListLike.Mem, Membership.mem]
    intro n nil_filter a_def
    subst a_def

    sorry
  · sorry
