import topology.metric_space.basic

def converges_to {X : Type*} [metric_space X] (s : ℕ → X) (x : X) :=
∀ (ε : ℝ) (hε : 0 < ε), ∃ N : ℕ, ∀ (n : ℕ) (hn : N ≤ n), dist x (s n) < ε

notation s ` ⟶ ` x := converges_to s x

theorem limit_unique {X : Type*} [metric_space X] {s : ℕ → X}
  (x₀ x₁ : X) (h₀ : s ⟶ x₀) (h₁ : s ⟶ x₁) :
x₀ = x₁ := 
begin
    apply classical.by_contradiction,
    intro h,
    let ε' := (dist x₀ x₁),
    have ε'_pos : 0 < ε',
        exact dist_pos.mpr h,
    let ε := ε'/2,
    have ε_pos : 0 < ε,
        exact half_pos ε'_pos,
    rcases h₀ ε ε_pos with ⟨N₀, hN₀⟩,
    rcases h₁ ε ε_pos with ⟨N₁, hN₁⟩,
    let N := max N₀ N₁,
    specialize hN₀ N (le_max_left N₀ N₁),
    specialize hN₁ N (le_max_right N₀ N₁),
    have key : ε' < ε',
        calc 
        ε' = dist x₀ x₁ : rfl
        ... ≤ (dist x₀ (s N)) + (dist x₁ (s N)) : dist_triangle_right x₀ x₁ (s N)
        ... < ε + ε : add_lt_add hN₀ hN₁
        ... = ε' : add_halves ε',
        exact (irrefl ε') key,
end