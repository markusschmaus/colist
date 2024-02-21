import Colist.PartialListLike

universe u v w

def PartialColist (α : Type u) := Quotient (PartialListLike.instSetoid α)

namespace PartialColist

def mk {α : Type u} {β : Type v} [inst : PartialListLike α β] (x : β): PartialColist α :=
  Quotient.mk (PartialListLike.instSetoid α) ⟨β, inst, x⟩

instance {α : Type u} {L : Type u → Type v} [PartialListLike α (L α)] : CoeOut (L α) (PartialColist α) where
  coe := mk

theorem exists_rep {α : Type u} (as : PartialColist α) : ∃ (β : Type v)
    (inst : PartialListLike α β) (x : β), mk (inst := inst) x = as := by
  obtain ⟨x, rep⟩ := Quotient.exists_rep as
  use x.imp
  use x.inst
  use x.value
  exact rep

def isNil {α : Type u} : PartialColist α → Prop := Data.lift (PartialListLike.instSetoid α) (·.isNil) <| by
  constructor
  · simp only [implies_true]
  · simp only [Setoid.r, heq_eq_eq, eq_iff_iff]
    intro _ _ _ _ _ _ h
    have := (h 0).isNil_eq
    simp_all only [Function.iterate_zero, id_eq]

instance instDecidableIsNil {α : Type u} : (as : PartialColist α) → Decidable (isNil as) := Data.lift (PartialListLike.instSetoid α) (·.instDecidableIsNil) <| by
  constructor
  · exact fun x => rfl
  · intro _ _ inst inst' x x' equiv
    have isNil_eq := equiv 0 |>.isNil_eq
    have type_eq : Decidable (PartialListLike.isNil α x) = Decidable (PartialListLike.isNil α x') := by
      simp_all only [Function.iterate_zero, id_eq]
    apply Subsingleton.helim type_eq

@[simp]
theorem isNil_mk_imp {α : Type u} (x : Data.Imp (PartialListLike α)) :
    isNil ⟦x⟧ ↔ x.inst.isNil x.value := by
  exact { mp := fun a => a, mpr := fun a => a }

@[simp]
theorem not_isNil_of_mk_imp {α : Type u} (x : Data.Imp (PartialListLike α)) :
    ¬ x.inst.isNil x.value → ¬ isNil ⟦x⟧ := by
  exact fun a => a

def head {α : Type u} : (as : PartialColist α) → ¬ isNil as → α := Data.lift (PartialListLike.instSetoid α) (·.head) <| by
  constructor
  · intro x
    have : HEq (isNil ⟦x⟧) (x.inst.isNil x.value) := by
      unfold isNil
      refine Data.lift_mk (PartialListLike.instSetoid α) (·.isNil) _ _ _
    rw [eq_of_heq this]
  · simp only [Setoid.r]
    intro _ _ _ _ _ _ h
    have := (h 0).head_heq
    simp_all only [Function.iterate_zero, id_eq]

def tail {α : Type u} : PartialColist α → PartialColist α := Data.liftGenId (PartialListLike.instSetoid α) (·.tail) <| by
  simp_all [Setoid.r, PartialListLike.equiv, PartialListLike.equivExt]
  intro _ _ h n
  have := h n.succ
  simp_all only [Function.iterate_succ, Function.comp_apply]

@[simp]
theorem tail_mk_imp {α : Type u} (x : Data.Imp (PartialListLike α)) :
    tail ⟦x⟧ = ⟦⟨x.imp, x.inst, x.inst.tail x.value⟩⟧ := rfl

@[simp]
theorem iterate_tail_mk_imp (n : Nat) {α : Type u} (x : Data.Imp (PartialListLike α)) :
    tail^[n] ⟦x⟧ = ⟦⟨x.imp, x.inst, (x.inst.tail^[n] x.value)⟩⟧ := by
  apply Data.iterate_liftGen_mk
  intro a b h n
  simp only [Setoid.r, PartialListLike.equiv, id_eq] at *
  exact h n.succ

def terminal_isNil {α : Type u} (as : PartialColist α) : isNil as → isNil (tail as) := by
    obtain ⟨x, rep⟩ := Quotient.exists_rep as
    rw [← rep]
    exact x.inst.terminal_isNil x.value

instance instPartialListLike {α : Type u} : PartialListLike α (PartialColist α) where
  isNil := isNil
  head := head
  tail := tail
  terminal_isNil := terminal_isNil

@[simp]
theorem isNil_mk (α : Type u) {β : Type v} [PartialListLike α β] {x : β} :
    PartialListLike.isNil α (mk x : PartialColist α) ↔ PartialListLike.isNil α x := by
  exact { mp := fun a => a, mpr := fun a => a }

@[simp]
theorem head_mk {α : Type u} {β : Type v} [PartialListLike α β] {x : β} {h : ¬ PartialListLike.isNil α x} :
    PartialListLike.head (mk x : PartialColist α) h = PartialListLike.head x h := rfl

@[simp]
theorem tail_mk {α : Type u} {β : Type v} [PartialListLike α β] {x : β} :
    PartialListLike.tail α (mk x : PartialColist α) = mk (PartialListLike.tail α x) := rfl

@[simp]
theorem iterate_tail_mk (n : Nat) {α : Type u} {β : Type v} [inst : PartialListLike α β] {x : β} :
    (PartialListLike.tail α)^[n] (mk x : PartialColist α) = mk ((PartialListLike.tail α)^[n] x) := by
  simp only [PartialListLike.tail, mk, iterate_tail_mk_imp]

@[simp]
theorem isFinite_mk {α : Type u} {β : Type v} [PartialListLike α β] {x : β} :
    PartialListLike.isFinite α (mk x : PartialColist α) ↔ PartialListLike.isFinite α x := by
  simp only [PartialListLike.isFinite, iterate_tail_mk, isNil_mk]
