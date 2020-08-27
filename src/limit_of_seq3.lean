import data.real.basic
open classical
attribute [instance] prop_decidable

/-
  Rigorous definition of a limit
  For a sequence x_n, we say that \lim_{n \to \infty} x_n = l if
    ∀ ε > 0, ∃ N, n ≥ N → |x_n - l| < ε
-/

def lim_to_inf (x : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (x n - l) < ε

theorem exercise_1p4 (x : ℕ → ℝ) (l : ℝ) (h₁ : lim_to_inf x l) :
  lim_to_inf (λ n, abs (x n)) (abs l) := 
begin
    intros ε ε_pos,
    rcases h₁ ε ε_pos with ⟨N, hN⟩,
    use N,
    intros n hn,
    calc 
    abs (abs (x n) - abs l) ≤ abs ((x n) - l) : abs_abs_sub_le_abs_sub (x n) l
    ... < ε : hN n hn
end