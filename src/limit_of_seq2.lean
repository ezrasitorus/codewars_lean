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

theorem exercise_1p3 (x y : ℕ → ℝ) (l : ℝ)
  (h₁ : ∀ n, abs (x n - l) ≤ y n) (h₂ : lim_to_inf y 0) :
  lim_to_inf x l := 
begin
    intros ε ε_pos,
    rcases h₂ ε ε_pos with ⟨N, hN⟩,
    use N,
    intros n hn,
    specialize h₁ n,
    specialize hN n hn,
    calc 
    abs (x n - l) ≤ y n   : h₁
    ... ≤ abs (y n)       : le_abs_self (y n)
    ... ≤ abs (y n - 0)   : by rw sub_zero (y n)
    ... < ε               : hN,
end