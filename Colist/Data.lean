import Mathlib.Tactic

universe u v w

@[simp]
def cast' {α β : Sort u} (a : α) (h : α = β) : β := cast h a

namespace Data

structure Imp (Class : Type u → Type v) : Type (max (u + 1) v) where
  imp : Type u
  inst : Class imp
  value : imp

structure lift.Precondition {Class : Type u → Type v} {β : {imp : Type u} → Class imp → imp → Type w}
    (s : Setoid (Imp Class))
    (f : {imp : Type u} → (inst : Class imp) → (x : imp) → β inst x) (out : Quotient s → Type w): Prop where
  β_eq (x : Imp Class) : β x.inst x.value = out (Quotient.mk s x)
  f_heq {imp imp': Type u} (inst : Class imp) (inst' : Class imp')
    (x : imp) (x' : imp') (h : s.r ⟨imp, inst, x⟩ ⟨imp', inst', x'⟩):
    HEq (f inst x)  (f inst' x')

def lift {Class : Type u → Type v} {β : {imp : Type u} → Class imp → imp → Type w}
    (s : Setoid (Imp Class))
    (f : {imp : Type u} → (inst : Class imp) → (x : imp) → β inst x)
    {out : Quotient s → Type w} (h : lift.Precondition s f out) (q : Quotient s) : (out q) :=
  let β' := Quotient.lift (fun x : Imp Class => β x.inst x.value) <| by
    intro x x' x_equiv
    simp_all only [h.β_eq x, Quotient.sound x_equiv, h.β_eq x']
  let result := Quotient.hrecOn q (motive := β') (fun x : Imp Class => f x.inst x.value) <| by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro x x' x_equiv
    exact h.f_heq x.inst x'.inst x.value x'.value x_equiv
  cast' result <| by
    obtain ⟨x, rep⟩ := Quotient.exists_rep q
    rw [← rep] at *
    have := h.β_eq x
    simp_all only [Quotient.lift_mk]

theorem lift_mk {Class : Type u → Type v} {β : {imp : Type u} → Class imp → imp → Type w}
    (s : Setoid (Imp Class))
    (f : {imp : Type u} → (inst : Class imp) → (x : imp) → β inst x)
    (out : Quotient s → Type w) (h : lift.Precondition s f out) (x : Imp Class) :
    HEq (lift s f h ⟦x⟧) (f x.inst x.value):= by
  apply HEq.symm
  apply heq_of_cast_eq (h.β_eq x)
  rfl

@[simp]
abbrev liftGen.Precondition {Class : Type u → Type v} (s : Setoid (Imp Class))
    {Class' : Type u → Type v} (s' : Setoid (Imp Class'))
    {β : (imp : Type u) → Class imp → Type u}
    (inst' : {imp : Type u} → (inst : Class imp) → Class' (β imp inst))
    (f : {imp : Type u} → (inst : Class imp) → imp → β imp inst) : Prop :=
  (a b : Imp Class) → (h : s.r a b) → s'.r ⟨β a.imp a.inst, inst' a.inst, f a.inst a.value⟩ ⟨β b.imp b.inst, inst' b.inst, f b.inst b.value⟩

def liftGen {Class : Type u → Type v} (s : Setoid (Imp Class))
    {Class' : Type u → Type v} (s' : Setoid (Imp Class'))
    {β : (imp : Type u) → Class imp → Type u}
    (inst' : {imp : Type u} → (inst : Class imp) → Class' (β imp inst))
    (f : {imp : Type u} → (inst : Class imp) → imp → β imp inst)
    (h : liftGen.Precondition s s' inst' f)
    (q : Quotient s) : Quotient s' :=
  Quotient.hrecOn q (fun x : Imp Class => Quotient.mk s' <| ⟨β x.imp x.inst, inst' x.inst, f x.inst x.value⟩) <| by
    simp only [HasEquiv.Equiv, heq_eq_eq, Quotient.eq,]
    exact h

@[inline]
abbrev liftGenId {Class : Type u → Type v} (s : Setoid (Imp Class)) := liftGen s s id

theorem liftGen_mk {Class : Type u → Type v} (s : Setoid (Imp Class))
    {Class' : Type u → Type v} (s' : Setoid (Imp Class'))
    {β : (imp : Type u) → Class imp → Type u}
    (inst' : {imp : Type u} → (inst : Class imp) → Class' (β imp inst))
    (f : {imp : Type u} → (inst : Class imp) → imp → β imp inst)
    (h : liftGen.Precondition s s' inst' f)
    (x : Imp Class) :
    (liftGen s s' inst' f h ⟦x⟧) = ⟦⟨β x.imp x.inst, inst' x.inst, f x.inst x.value⟩⟧ := by
  rfl

theorem iterate_liftGen_mk (n : Nat)
    {Class : Type u → Type v}
    (s : Setoid (Imp Class))
    (f : {imp : Type u} → (inst : Class imp) → imp → imp)
    (h : liftGen.Precondition s s id f)
    (x : Imp Class) :
    ((liftGenId s f h)^[n] ⟦x⟧) = ⟦⟨x.imp, x.inst, ((f x.inst)^[n] x.value)⟩⟧ := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    have := ih ⟨x.imp, x.inst, f x.inst x.value⟩
    simp_all only [Function.iterate_succ, Function.comp_apply, liftGen_mk, id_eq]
