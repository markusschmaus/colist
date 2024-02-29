import Mathlib.Tactic

universe u v w w'

@[simp]
def cast' {α β : Sort u} (a : α) (h : α = β) : β := cast h a

structure ClassSetoid.Imp (Class : Type u → Type v) : Type (max (u + 1) v) where
  imp : Type u
  inst : Class imp
  value : imp

abbrev ClassSetoid (Class : Type u → Type v) := Setoid (ClassSetoid.Imp Class)

namespace ClassSetoid

def Quotient {Class : Type u → Type v} (s : ClassSetoid Class) := _root_.Quotient s

set_option checkBinderAnnotations false in
def mkQuotient {Class : Type u → Type v} (s : ClassSetoid Class) {imp : Type u} [inst : Class imp] (x : imp) : Quotient s :=
  Quotient.mk s ⟨imp, inst, x⟩

set_option checkBinderAnnotations false in
theorem eq {Class : Type u → Type v} {s : ClassSetoid Class} {imp : Type u} [inst : Class imp] {imp' : Type u} [inst' : Class imp'] {x : imp}  {y : imp'}:
    mkQuotient (inst := inst) s x = mkQuotient (inst := inst') s y ↔ s.r ⟨_, inst, x⟩  ⟨_, inst', y⟩ := by
  unfold mkQuotient
  constructor
  · intro h
    exact Quotient.eq'.mp h
  · intro h
    exact Quotient.eq'.mpr h

theorem exists_rep {Class : Type u → Type v} (s : ClassSetoid Class) (x : Quotient s) : ∃ (β : Type u)
    (inst : Class β) (x' : β), s.mkQuotient (inst := inst) x' = x := by
  obtain ⟨x', rep⟩ := Quotient.exists_rep x
  use x'.imp
  use x'.inst
  use x'.value
  exact rep

structure lift.Precondition {Class : Type u → Type v} (s : ClassSetoid Class)
    {β : {imp : Type u} → Class imp → imp → Type w}
    (f : {imp : Type u} → (inst : Class imp) → (x : imp) → β inst x) (out : Quotient s → Type w): Prop where
  β_eq (x : Imp Class) : β x.inst x.value = out (Quotient.mk s x)
  f_heq {imp imp': Type u} (inst : Class imp) (inst' : Class imp')
    (x : imp) (x' : imp') (h : s.r ⟨imp, inst, x⟩ ⟨imp', inst', x'⟩):
    HEq (f inst x)  (f inst' x')

def lift {Class : Type u → Type v} (s : ClassSetoid Class)
    {β : {imp : Type u} → Class imp → imp → Type w}
    (f : {imp : Type u} → (inst : Class imp) → (x : imp) → β inst x)
    {out : Quotient s → Type w} (h : lift.Precondition s f out) (q : Quotient s) : out q :=
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
    simp_all only [Quotient.lift_mk (s := s)]

@[simp]
theorem lift_mk_heq {Class : Type u → Type v} {s : ClassSetoid Class}
    {β : {imp : Type u} → Class imp → imp → Type w}
    {f : {imp : Type u} → (inst : Class imp) → (x : imp) → β inst x}
    {out : Quotient s → Type w} {h : lift.Precondition s f out}
    {imp : Type u} {inst : Class imp} (x : imp) :
    HEq (s.lift f h (s.mkQuotient (inst := inst) x)) (f inst x) := by
  refine cast_heq (lift.proof_3 s (fun {imp} => f) h (s.mkQuotient (inst := inst) x)) ?x

@[simp]
theorem lift_prop_mk {Class : Type u → Type v} (s : ClassSetoid Class)
    {β : Type w}
    {pᵢ : {imp : Type u} → Class imp → imp → Prop}
    {f : {imp : Type u} → (inst : Class imp) → (x : imp) → pᵢ inst x → β}
    {pₒ : Quotient s → Prop}
    {h : lift.Precondition s f (fun x => pₒ x → β)}
    {imp : Type u} {inst : Class imp} {x : imp}
    {hᵢ : pᵢ _ _} {hₒ : pₒ _} :
    s.lift f h (s.mkQuotient (inst := inst) x) hₒ = f inst x hᵢ := by
  apply congr_heq
  · simp only [lift_mk_heq]
  · exact heq_prop hₒ hᵢ

@[simp]
theorem lift_mk {Class : Type u → Type v} (s : ClassSetoid Class)
    {β : Type w}
    (f : {imp : Type u} → (inst : Class imp) → (x : imp) → β)
    (h : lift.Precondition s f (fun _ => β))
    {imp : Type u} {inst : Class imp} (x : imp) :
    s.lift f h (s.mkQuotient (inst := inst) x) = f inst x :=
  rfl

@[simp]
abbrev liftGen.Precondition {Class : Type u → Type v} (s : ClassSetoid Class)
    {Class' : Type u → Type v} (s' : Setoid (Imp Class'))
    {β : (imp : Type u) → Class imp → Type u}
    (inst' : {imp : Type u} → (inst : Class imp) → Class' (β imp inst))
    (f : {imp : Type u} → (inst : Class imp) → imp → β imp inst) : Prop :=
  (a b : Imp Class) → (h : s.r a b) → s'.r ⟨β a.imp a.inst, inst' a.inst, f a.inst a.value⟩ ⟨β b.imp b.inst, inst' b.inst, f b.inst b.value⟩

def liftGen {Class : Type u → Type v} (s : ClassSetoid Class)
    {Class' : Type u → Type v} (s' : ClassSetoid Class')
    {β : (imp : Type u) → Class imp → Type u}
    (inst' : {imp : Type u} → (inst : Class imp) → Class' (β imp inst))
    (f : {imp : Type u} → (inst : Class imp) → imp → β imp inst)
    (h : liftGen.Precondition s s' inst' f)
    (q : Quotient s) : Quotient s' :=
  Quotient.hrecOn q (fun x : Imp Class => Quotient.mk s' <| ⟨β x.imp x.inst, inst' x.inst, f x.inst x.value⟩) <| by
    intro _ _ _
    simp_all only [heq_eq_eq]
    apply Quotient.eq (r := s') |>.mpr
    simp_all only [HasEquiv.Equiv]

@[simp]
theorem liftGen_mk {Class : Type u → Type v} (s : ClassSetoid Class)
    {Class' : Type u → Type v} (s' : ClassSetoid Class')
    {β : (imp : Type u) → Class imp → Type u}
    (inst' : {imp : Type u} → (inst : Class imp) → Class' (β imp inst))
    (f : {imp : Type u} → (inst : Class imp) → imp → β imp inst)
    (h : liftGen.Precondition s s' inst' f)
    {imp : Type u} {inst : Class imp} (x : imp) :
    (liftGen s s' inst' f h (s.mkQuotient (inst := inst) x)) = s'.mkQuotient (inst := inst' inst) (f inst x) := by
  rfl

@[inline]
abbrev liftEndo {Class : Type u → Type v} (s : ClassSetoid Class) := liftGen s s id

@[simp]
theorem liftEndo_mk
    {Class : Type u → Type v}
    (s : ClassSetoid Class)
    (f : {imp : Type u} → (inst : Class imp) → imp → imp)
    (h : liftGen.Precondition s s id f)
    {imp : Type u} {inst : Class imp} (x : imp) :
    (liftEndo s f h (s.mkQuotient (inst := inst) x)) = s.mkQuotient (inst := inst) (f inst x) :=
  rfl

@[simp]
theorem iterate_liftEndo_mk (n : Nat)
    {Class : Type u → Type v}
    (s : ClassSetoid Class)
    (f : {imp : Type u} → (inst : Class imp) → imp → imp)
    (h : liftGen.Precondition s s id f)
    {imp : Type u} {inst : Class imp} (x : imp) :
    ((liftEndo s f h)^[n] (s.mkQuotient (inst := inst) x)) = s.mkQuotient (inst := inst) ((f inst)^[n] x) := by
  revert imp inst x
  induction n with
  | zero => simp only [Nat.zero_eq, Function.iterate_zero, id_eq, implies_true, forall_const]
  | succ n ih =>
    intro imp inst x
    have := ih (inst := inst) (f inst x)
    simp_all only [Function.iterate_succ, Function.comp_apply, liftGen_mk, id_eq]
