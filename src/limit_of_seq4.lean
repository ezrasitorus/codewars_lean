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

/-
  Bounded sequences
  A sequence is bounded if |x_n| \leq B for some constant B
  and all n
-/

-- Lean's mathlib already defines bounded so we rename our
-- predicate as bounded' to avoid name clashes
def bounded' (x : ℕ → ℝ) :=
  ∃ B, ∀ n, abs (x n) ≤ B

theorem exercise_1p13 (x y : ℕ → ℝ) (h₁ : lim_to_inf x 0)
  (h₂ : bounded' y) : lim_to_inf (λ n, x n * y n) 0 := 
begin
    intros ε ε_pos,
    rcases h₂ with ⟨B, hB⟩,
    let ε' := ε / ((abs B) + 1),
    have key : 0 < (abs B) + 1,
        exact add_pos_of_nonneg_of_pos (abs_nonneg B) zero_lt_one,
    have ε'_pos : ε' > 0,
        exact div_pos ε_pos key,
    rcases h₁ ε' ε'_pos with ⟨N, hN⟩,
    use N,
    intros n hn,
end