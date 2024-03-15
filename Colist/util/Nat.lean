import Mathlib.Init.Data.Nat.Lemmas

theorem Nat.find_def {p : ℕ → Prop} [DecidablePred p] (H : ∃ (n : ℕ), p n) {n : ℕ} :
    Nat.find H = n ↔ p n ∧ ∀ (m : ℕ), m < n → ¬p m := by
  constructor
  · intro n_def
    subst n_def
    simp only [Nat.find_spec, true_and]
    intro m m_lt_n
    have h := Nat.find_min H m_lt_n
    simp_all only [not_false_eq_true]
  · intro ⟨spec, min⟩
    have := Nat.find_min H (m := n) |> imp_not_comm.mp <| spec
    have := min (Nat.find H) |> imp_not_comm.mp <| Nat.find_spec H
    omega
