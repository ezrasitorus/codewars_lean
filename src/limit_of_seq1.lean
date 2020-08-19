import data.real.basic
open classical
open tactic
attribute [instance] prop_decidable

/-
  Rigorous definition of a limit
  For a sequence x_n, we say that \lim_{n \to \infty} x_n = l if
    ∀ ε > 0, ∃ N, n ≥ N → |x_n - l| < ε
-/

def lim_to_inf (x : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (x n - l) < ε

theorem help (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) :  abs (y - x) ≤ abs (z - x) :=
begin
    have key : (y - x) ≤ (z - x),
        exact sub_le_sub_right h2 x,
    have h1 : 0 ≤ (y - x),
        linarith,
    apply abs_le_abs key _,
    linarith
end

theorem help' (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) :  abs (z - y) ≤ abs (z - x) :=
begin
    have key : (-x ≥ -y) ∧ (-y ≥ -z) := ⟨by linarith, by linarith⟩,
    have key' : abs (-y - (-z)) ≤ abs (-x - (-z)),
        exact help _ _ _ key.2 key.1,
    simp only [neg_sub_neg] at key',
    assumption,
end

theorem exercise_1p2 (x y : ℕ → ℝ) (l : ℝ)
  (h₁ : ∀ n, x n ≤ l ∧ l ≤ y n)
  (h₂ : lim_to_inf (λ n, x n - y n) 0) :
  lim_to_inf x l ∧ lim_to_inf y l := 
begin
    split,
    {
        intros ε ε_pos,
        rcases h₂ ε ε_pos with ⟨N, hN⟩,
        use N,
        intros n hn,
        have key : abs (l - x n) ≤ abs (y n - x n),
            exact help _ _ _ (h₁ n).1 (h₁ n).2,
        specialize hN n hn,
        simp only [sub_zero] at hN,
        calc 
        abs (x n - l) = abs (l - x n) : abs_sub (x n) l
        ... ≤ abs (y n - x n)         : key
        ... = abs (x n - y n)         : abs_sub (y n) (x n)
        ... < ε                       : hN,
    },
    {
    intros ε ε_pos,
        rcases h₂ ε ε_pos with ⟨N, hN⟩,
        use N,
        intros n hn,
        have key : abs (y n - l) ≤ abs (y n - x n),
            exact help' _ _ _ (h₁ n).1 (h₁ n).2,
        specialize hN n hn,
        simp only [sub_zero] at hN,
        calc 
        abs (y n - l) ≤ abs (y n - x n) : key
        ... = abs (x n - y n)           : abs_sub (y n) (x n)
        ... < ε                         : hN,
    }
end