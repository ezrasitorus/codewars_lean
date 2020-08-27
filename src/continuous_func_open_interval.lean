import data.real.basic data.set.intervals.basic

open set

/-
  Continuous function
  A function f(x) is said to be continuous at x = a if, for any ε > 0,
  there is δ > 0 s.t. |f(x) - f(a)| < ε whenever |x - a| < δ
-/

def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

theorem continuous_function_about_an_open_interval {f a}
  (hcont : continuous_at f a) (hgt : f a > 0) :
  ∃ b c : ℝ, a ∈ Ioo b c ∧ ∀ x ∈ Ioo b c, f x > 0 :=
begin
    specialize hcont ((f a) / 2) (half_pos hgt),
    rcases hcont with ⟨δ, δ_pos, hδ⟩,
    use [a - δ, a + δ],
    split,
        {
            split; linarith,
        },
        {
            intros x x_in,
            cases x_in with gt lt,
            have key : abs (x - a) < δ,
                rw abs_sub_lt_iff,
                split; linarith,
            specialize hδ x key,
            have key2 : f x > f a - f a / 2,
                by exact sub_lt_of_abs_sub_lt_left hδ,
            linarith,
        }
end