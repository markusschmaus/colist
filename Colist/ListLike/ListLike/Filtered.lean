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

theorem eq {α : Type u} {β : Type v} (x : Filtered α β) (y : Filtered α β) :
    x.inst = y.inst → x.p = y.p → x.head? = y.head? → x.baseTail = y.baseTail →
    x = y := by
  intro inst_eq p_eq head?_eq baseTail_eq
  cases x with
  | mk x' valid terminal_none =>
  cases y with
  | mk y' valid terminal_none =>
  simp_all only [mk.injEq]
  cases x'
  cases y'
  simp_all only [not_false_eq_true, implies_true]
  rw [inst_eq]

end Filtered

namespace PartialFiltered

inductive tailX.Property.hit {α : Type u} {β : Type v} (x : PartialFiltered α β)
    (out : Filtered α β) (n : Nat) : Prop where
  | found
    (tail_eq : out.baseTail = x.inst.tail^[n + 1] x.baseTail)
    (inst_eq : out.inst = x.inst)
    (p_eq : out.p = x.p)
    (not_nil : ¬ x.inst.isNil (x.inst.tail^[n] x.baseTail))
    (head_eq : x.inst.head (x.inst.tail^[n] x.baseTail) not_nil = out.head?)
    (p_head : x.p (x.inst.head (x.inst.tail^[n] x.baseTail) not_nil))
  | empty
    (tail_eq : out.baseTail = x.inst.tail^[n + 1] x.baseTail)
    (inst_eq : out.inst = x.inst)
    (p_eq : out.p = x.p)
    (is_nil : x.inst.isNil (x.inst.tail^[n] x.baseTail))
    (baseTail_nil : x.inst.isNil out.baseTail)
    (head_none : out.head? = none)

def tailX.Property.hit.tail_eq {α : Type u} {β : Type v} {x : PartialFiltered α β}
    {out : Filtered α β} {n : Nat} (h : tailX.Property.hit x out n) :=
  match h with
  | tailX.Property.hit.found tail_eq _ _ _ _ _ => tail_eq
  | tailX.Property.hit.empty tail_eq _ _ _ _ _ => tail_eq

def tailX.Property.hit.head?_eq {α : Type u} {β : Type v} {x : PartialFiltered α β}
    {out : Filtered α β} {n : Nat} (h : tailX.Property.hit x out n) :
    out.head? = x.inst.head? (x.inst.tail^[n] x.baseTail) :=
  match h with
  | tailX.Property.hit.found _ _ _ not_nil _ _ => by
    simp_all? [Function.iterate_succ, Function.comp_apply, not_false_eq_true,
      x.inst.head?_not_nil]

  | tailX.Property.hit.empty _ _ _ is_nil _ _ => by
    simp_all only [Function.iterate_succ, Function.comp_apply, x.inst.head?_nil]

def tailX.Property.hit.inst_eq {α : Type u} {β : Type v} {x : PartialFiltered α β}
    {out : Filtered α β} {n : Nat} (h : tailX.Property.hit x out n) :=
  match h with
  | tailX.Property.hit.found _ inst_eq _ _ _ _ => inst_eq
  | tailX.Property.hit.empty _ inst_eq _ _ _ _ => inst_eq

def tailX.Property.hit.p_eq {α : Type u} {β : Type v} {x : PartialFiltered α β}
    {out : Filtered α β} {n : Nat} (h : tailX.Property.hit x out n) :=
  match h with
  | tailX.Property.hit.found _ _ p_eq _ _ _ => p_eq
  | tailX.Property.hit.empty _ _ p_eq _ _ _ => p_eq

def tailX.Property.hit.p_head {α : Type u} {β : Type v} {x : PartialFiltered α β}
    {out : Filtered α β} {n : Nat} (h : tailX.Property.hit x out n) :
    (not_nil : ¬ x.inst.isNil (x.inst.tail^[n] x.baseTail)) → x.p (x.inst.head (x.inst.tail^[n] x.baseTail) not_nil) :=
  match h with
  | tailX.Property.hit.found _ _ _ _ _ p_head => by
    intro
    exact p_head
  | tailX.Property.hit.empty _ _ _ _ _ _ => by
    intro not_nil
    simp_all only [Function.iterate_succ, Function.comp_apply]

structure tailX.Property.miss {α : Type u} {β : Type v} (x : PartialFiltered α β)
    (n : Nat) : Prop where
  not_nil : ¬ x.inst.isNil (x.inst.tail^[n] x.baseTail)
  not_p_head : ¬ (x.p <| x.inst.head (x.inst.tail^[n] x.baseTail) not_nil)

abbrev tailX.Property {α : Type u} {β : Type v} (x : PartialFiltered α β)
    (out : Filtered α β) : Prop :=
  ∃ n : Nat, tailX.Property.hit x out n ∧ ∀ m < n, tailX.Property.miss x m

instance tailX.Property.instSubsingleton {α : Type u} {β : Type v}
    (x : PartialFiltered α β) :
    Subsingleton (Subtype (tailX.Property x)) := by
  constructor
  intro a b
  have ⟨na, ⟨hit_a, misses_a⟩⟩ := a.property
  have ⟨nb, ⟨hit_b, misses_b⟩⟩ := b.property
  have := hit_a.inst_eq
  have := hit_b.inst_eq
  have := hit_a.p_eq
  have := hit_b.p_eq
  have n_eq : na = nb := by
    apply Linarith.eq_of_not_lt_of_not_gt
    · by_contra lt
      have miss_a := misses_b _ lt
      induction hit_a with
      | found _ _ _ _ _ p_head =>
        have := miss_a.not_p_head
        simp_all only [Function.iterate_succ, Function.comp_apply]
      | empty _ _ _ _ _ _ =>
        have := miss_a.not_nil
        simp_all only [Function.iterate_succ, Function.comp_apply]
    · by_contra lt
      have miss_b := misses_a _ lt
      induction hit_b with
      | found _ _ _ _ _ p_head =>
        have := miss_b.not_p_head
        simp_all only [Function.iterate_succ, Function.comp_apply]
      | empty _ _ _ _ _ _ =>
        have := miss_b.not_nil
        simp_all only [Function.iterate_succ, Function.comp_apply]
  apply Subtype.eq
  apply Filtered.eq
  · simp_all only
  · simp_all only
  · have := hit_a.head?_eq
    have := hit_b.head?_eq
    simp_all only [implies_true, forall_const]
  · have := hit_a.tail_eq
    have := hit_b.tail_eq
    simp_all only [implies_true, forall_const]

def tailX {α : Type u} {β : Type v} (x : PartialFiltered α β) :
    Subtype (tailX.Property x) :=
  let rec loop (current : β) (n : Nat)
      (h : current = x.inst.tail^[n] x.baseTail ∧ ∀ m < n, tailX.Property.miss x m) :
      Subtype (tailX.Property x) :=
    if is_nil : x.inst.isNil current then
      let result := Filtered.mk'
        (inst := x.inst) (p := x.p) (decP := x.decP) (head? := none)
        (baseTail := x.inst.tail current)
        (valid := fun h => (h rfl).elim)
        (terminal_none := fun _ => x.inst.terminal_isNil current is_nil)
      Subtype.mk result <| by
        use n
        constructor
        · apply tailX.Property.hit.empty
          · simp_all only [h.left, true_and, Function.iterate_succ, Function.comp_apply,
              Function.apply_iterate_apply]
          . rfl
          . rfl
          · rw [h.left] at is_nil
            exact is_nil
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
          · apply tailX.Property.hit.found
            · simp only [Function.iterate_succ, Function.comp_apply, h.left,
                Function.apply_iterate_apply]
            · rfl
            · rfl
            · simp only [h.left]
            · simp only [h.left] at proof
              exact proof
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

theorem exists_tailX_equiv_iterate {α : Type u} {β : Type v} {x : PartialFiltered α β} :
    ∃ (n : Nat), (tailX x).val.head? = x.inst.head? (x.inst.tail^[n] x.baseTail) ∧
    (tailX x).val.baseTail = x.inst.tail^[n + 1] x.baseTail := by
  have ⟨n, ⟨hit, _⟩⟩ := (tailX x).property
  use n
  have := hit.tail_eq
  have := hit.head?_eq
  simp_all only [Function.iterate_succ, Function.comp_apply, and_self]

end PartialFiltered

namespace Filtered

abbrev tail {α : Type u} {β : Type v} (x : Filtered α β)  := (PartialFiltered.tailX x.toPartialFiltered).val

theorem nil_of_baseTail_nil {α : Type u} {β : Type v} (x : Filtered α β) :
    x.inst.isNil x.baseTail → x.tail.head? = none :=
  by
    intro baseTail_nil
    have ⟨n, ⟨hit, _⟩⟩ := x.toPartialFiltered.tailX |>.property
    have := hit.inst_eq
    have := hit.tail_eq
    simp_all only [Function.iterate_succ, Function.comp_apply]
    induction hit with
    | found _ _ _ not_nil head_eq p_head =>
      by_contra
      clear head_eq p_head
      revert not_nil
      simp only [imp_false, not_not]
      apply ProductiveListLike.iterate_terminal_isNil (inst := x.inst.toProductiveListLike)
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq]
    | empty _ _ _ _ _ head_none =>
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
    have ⟨n, ⟨hit, misses⟩⟩ := x.toPartialFiltered.tailX |>.property
    simp_all only [tail, Function.iterate_succ, Function.comp_apply]
    exact hit.inst_eq

instance instMembership {α : Type u} {β : Type v} :
    Membership α (Filtered α β) where
  mem a as := as.p a ∧ (some a = as.head? ∨ as.inst.instMembership.mem a as.baseTail)

instance instPartialListLike {α : Type u} {β : Type v} :
    PartialListLike α (Filtered α β) where
  isNil as := as.head? = none
  head as h := as.head?.get (Option.ne_none_iff_isSome.mp h)
  tail := tail

@[simp]
theorem head?_eq_head? {α : Type u} {β : Type v} (as : Filtered α β) :
    as.head? = PartialListLike.head? as := by
  by_cases h : PartialListLike.isNil as
  · simp_all only [PartialListLike.isNil, PartialListLike.head?_nil]
  · simp_all only [PartialListLike.isNil, not_false_eq_true, PartialListLike.head?_not_nil,
      PartialListLike.head, Option.some_get]

@[simp]
theorem tail_eq_tail {α : Type u} {β : Type v} (as : Filtered α β) :
    as.tail = PartialListLike.tail as := by
  simp_all only [PartialListLike.tail]

@[simp]
theorem tailX_eq_tail {α : Type u} {β : Type v} (as : Filtered α β) :
    as.toPartialFiltered.tailX = PartialListLike.tail as := by
  simp_all only [PartialListLike.tail]

@[simp]
theorem valid_head {α : Type u} {β : Type v} (as : Filtered α β) :
    (not_nil : _) → as.p (PartialListLike.head as not_nil) := by
  intro not_nil
  have := as.valid not_nil
  simp_all only [head?_eq_head?, not_false_eq_true, PartialListLike.head?_not_nil, Option.get_some]

theorem terminal_isNil {α : Type u} {β : Type v} (as : Filtered α β) :
    PartialListLike.isNil as → PartialListLike.isNil (PartialListLike.tail as) := by
  simp only [tail, PartialListLike.isNil, PartialListLike.tail]
  have ⟨n, ⟨hit, _⟩⟩ := as.toPartialFiltered.tailX |>.property
  induction hit with
  | found _ _ _ _ _ _ =>
    intro head_none
    have := as.terminal_none head_none
    have := as.inst.iterate_terminal_isNil as.baseTail n this
    contradiction
  | empty _ _ _ _ _ head_none =>
    intro _
    exact head_none

@[simp]
theorem valid_head_iterate_tail {α : Type u} {β : Type v} (as : Filtered α β) (n : Nat):
    (not_nil : _) → as.p (PartialListLike.head (PartialListLike.tail^[n] as) not_nil) := by
  intro not_nil
  generalize p_eq : as.p = p
  revert as
  induction n with
  | zero =>
    intro as not_nil p_eq
    subst p_eq
    simp_all only [Nat.zero_eq, Function.iterate_zero, id_eq, valid_head]
  | succ n ih =>
    intro as not_nil p_eq
    have ⟨_, ⟨hit, _⟩⟩ := as.toPartialFiltered.tailX |>.property
    have := ih (PartialListLike.tail as) ?not_nil ?p_eq
    case not_nil =>
      simp_all only [Function.iterate_succ, Function.comp_apply, not_false_eq_true]
    case p_eq =>
      have := hit.p_eq
      simp_all only [Function.iterate_succ, Function.comp_apply, tail_eq_tail]
    simp_all only [tail_eq_tail, Function.iterate_succ, Function.comp_apply]

theorem Mem_Filtered  {α : Type u} {β : Type v} (a : α) (as : Filtered α β) :
    PartialListLike.Mem a as ↔ as.p a ∧
    (some a = as.head? ∨ PartialListLike.Mem (inst := as.inst.toPartialListLike) a as.baseTail) := by
  simp only [PartialListLike.Mem]
  constructor
  · intro ⟨n, not_nil, eq⟩
    by_cases n_zero : n = 0
    . subst n_zero
      simp only [Function.iterate_zero, id_eq] at not_nil
      simp_all only [Function.iterate_zero, id_eq, valid_head, head?_eq_head?, not_false_eq_true,
        PartialListLike.head?_not_nil, true_or, and_self]
    . have := Nat.succ_pred_eq_of_ne_zero n_zero
      generalize m_def : n.pred = m
      rw [m_def] at this
      clear m_def
      subst this
      subst eq
      constructor
      · apply valid_head_iterate_tail
      apply Or.inr
      use m
      use ?not_nil'
      case not_nil' =>
        apply as.inst.terminal_isNil (as.inst.tail^[m] as.baseTail) |>
          not_imp_not.mpr
        simp only [Function.iterate_succ, Function.comp_apply] at not_nil
        clear n_zero
        revert as
        induction m with
        | zero =>
          simp_all?
          sorry
        | succ m ih =>
          intro as
          have := ih (PartialListLike.tail as)
          simp? at this
          simp?
          exact this
          revert this
          unfold PartialListLike.isNil PartialListLike.tail ProductiveListLike.toPartialListLike
          intro this
          exact this
          sorry


      sorry
  ·
    sorry


instance instListLike {α : Type u} {β : Type v} :
    ListLike α (Filtered α β) where
  toPartialListLike := instPartialListLike
  terminal_isNil := terminal_isNil
  consistent_mem a as := by
    simp only [PartialListLike.Mem, Membership.mem]
    constructor
    · intro ⟨n, is_nil, _⟩
      by_cases n_zero : n = 0
      . simp_all?
        sorry
      . sorry
    · sorry
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
        have ⟨n', ⟨hit, _⟩⟩ := as.toPartialFiltered.tailX |>.property
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
    have ⟨n', ⟨hit, _⟩⟩ := (tail^[n] as).toPartialFiltered.tailX |>.property
    have := hit.inst_eq
    refine' nil_of_baseTail_nil (tail^[n] as) _
    simp_all only [le_add_iff_nonneg_left, zero_le, iterate_tail_inst]

end Filtered

namespace ListLike

abbrev filterX {α : Type u} {β : Type v} [inst : ListLike α β] (p : α → Prop)
    [decP : DecidablePred p] (as : β) :=
  (PartialFiltered.mk p none as).tailX

abbrev filter {α : Type u} {β : Type v} [inst : ListLike α β] (p : α → Prop)
    [decP : DecidablePred p] (as : β) : Filtered α β :=
  (filterX p as).val

@[simp]
theorem filter_inst {α : Type u} {β : Type v} [inst : ListLike α β] {p : α → Prop}
    [DecidablePred p] {as : β} : (filter (inst := inst) p as).inst = inst := by
  unfold filter
  have ⟨n, ⟨hit, _⟩⟩ := filterX p as |>.property
  have := hit.inst_eq
  simp_all only

@[simp]
theorem filter_p {α : Type u} {β : Type v} [inst : ListLike α β] {p : α → Prop}
    [DecidablePred p] {as : β} : (filter (inst := inst) p as).p = p := by
  unfold filter
  have ⟨n, ⟨hit, _⟩⟩ := filterX p as |>.property
  have := hit.p_eq
  simp_all only

@[simp]
theorem head?_filter {α : Type u} {β : Type v} [inst : ListLike α β] {p : α → Prop}
    [decP : DecidablePred p] {as : β}
    (h : (not_nil : ¬ PartialListLike.isNil as) → p (PartialListLike.head as not_nil)) :
    PartialListLike.head? (filter (inst := inst) p as) = PartialListLike.head? as := by
  have ⟨n, ⟨hit, misses⟩⟩ := filterX p as |>.property
  by_cases zero_n : 0 < n
  · have miss := misses 0 zero_n
    have := h miss.not_nil
    have := miss.not_p_head
    simp_all only [implies_true, Function.iterate_zero, id_eq, not_true_eq_false]
  simp only [not_lt, nonpos_iff_eq_zero] at zero_n
  subst zero_n
  cases hit with
  | found tail_eq _ _ not_nil head_eq p_head =>
    simp_all only [not_lt_zero', IsEmpty.forall_iff, forall_const, zero_add, Function.iterate_succ,
      Function.iterate_zero, Function.comp_apply, id_eq, filter_inst, filter_p,
      Filtered.head?_eq_head?]
    rw [←head_eq]
    apply Eq.symm ∘ PartialListLike.some_head?_eq_of_head_eq (not_nil := not_nil)
    simp_all only [implies_true, Function.iterate_zero, id_eq]
  | empty _ _ _ _ _ head_none =>
    simp_all only [not_lt_zero', IsEmpty.forall_iff, forall_const, zero_add, Function.iterate_succ,
      Function.iterate_zero, Function.comp_apply, id_eq, filter_inst, filter_p,
      Filtered.head?_eq_head?, dite_eq_left_iff, imp_false, not_not, PartialListLike.head?_nil]

theorem mem_filter {α : Type u} {β : Type v} [ListLike α β] (p : α → Prop)
    [DecidablePred p] (as : β) (a : α) :
    a ∈ filter p as ↔ a ∈ as ∧ p a := by
  constructor
  · simp [ProductiveListLike.Mem, Membership.mem]
    intro n nil_filter a_def
    subst a_def

    sorry
  · sorry
