import topology.metric_space.basic
import topology.uniform_space.basic

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

lemma easy {X : Type*} [metric_space X] (a b : X) (R : ℝ) : R - (dist a b) = R - (dist b a) :=
begin
    rw dist_comm,
end

theorem limit_within_closed_bound {X : Type*} [metric_space X] {s : ℕ → X}
    (x : X) (R : ℝ) (h₀ : s ⟶ x) (h₁ : ∀ n m : ℕ, dist (s n) (s m) < R) :
∀ n : ℕ, dist (s n) x ≤ R :=
begin
    intro n,
    apply classical.by_contradiction,
    intro hf,
    rw not_le at hf,
    have help : 0 < (dist (s n) x - R) / 2,
        suffices : 0 < (dist (s n) x - R),
            exact half_pos this,
        exact sub_pos.mpr hf,
    rcases h₀ ((dist (s n) x - R) / 2) help with ⟨N, hN⟩,
    specialize hN N (rfl.ge),
    have key : dist (s n) (s N) > R,
        have help' : (dist (s n) x) ≤ (dist (s n) (s N)) + (dist (s N) x),
            apply dist_triangle,
        calc
        (dist (s n) (s N)) ≥ (dist (s n) x) - (dist (s N) x) : sub_le_iff_le_add.mpr help'
        ... = (dist (s n) x) - (dist x (s N)) : easy (s N) x (dist (s n) x)
        ... > (dist (s n) x) - (dist (s n) x - R) / 2 : sub_lt_sub_left hN (dist (s n) x)
        ... = (dist (s n) x + R) / 2 : by ring
        ... > (R + R) / 2 : by linarith
        ... = R : half_add_self R,
        exact (lt_asymm (h₁ n N)) key,    
end

