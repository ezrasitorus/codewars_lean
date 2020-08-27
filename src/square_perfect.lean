import tactic

theorem expand : ∀ n : ℕ, (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 :=
-- Tedious way
begin
    intro n,
    rw nat.pow_two,
    rw mul_add,
    rw add_mul,
    rw ← nat.pow_two,
    rw one_mul,
    rw mul_one,
    rw ← add_assoc,
    rw two_mul,
    rw ← add_assoc,
end

-- Neater way to do it
example : ∀ n : ℕ, (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := λ _, by ring
