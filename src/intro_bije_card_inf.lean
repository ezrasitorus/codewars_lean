import init.function
import tactic

structure iso (A : Type) (B : Type) :=
  (a_to_b : A → B)
  (b_to_a : B → A)
  (a_b_a : ∀ a, b_to_a (a_to_b a) = a)
  (b_a_b : ∀ b, a_to_b (b_to_a b) = b)

open function

-- Task 0
-- Find a bijection between bool and bit. (provided for you as an example)

inductive bit : Type
  | b0 : bit
  | b1 : bit

open bit

def bool_to_bit : bool → bit
| tt := b1
| ff := b0

def bit_to_bool : bit → bool
| b0 := ff
| b1 := tt

def bool_iso_bit : iso bool bit :=
{
  a_to_b := bool_to_bit,
  b_to_a := bit_to_bool,
  a_b_a := λ a, bool.cases_on a rfl rfl,
  b_a_b := λ b, bit.cases_on b rfl rfl,
}

-- Task 1
-- General properties of iso

-- Task 1-1 : Prove that any set has the same cardinality as itself
def iso_rfl {A : Type} : iso A A := 
{
  a_to_b := id,
  b_to_a := id,
  a_b_a := λ _, rfl,
  b_a_b := λ _, rfl,
}

-- Task 1-2 : Prove that iso is symmetric
def iso_symm {A B : Type} (i : iso A B) : iso B A := 
{
  a_to_b := i.b_to_a,
  b_to_a := i.a_to_b,
  a_b_a := i.b_a_b,
  b_a_b := i.a_b_a,
}

-- Task 1-3 : Prove that iso is transitive
def iso_trans {A B C : Type} (ab : iso A B) (bc : iso B C) : iso A C := 
{
  a_to_b := bc.a_to_b ∘ ab.a_to_b,
  b_to_a := ab.b_to_a ∘ bc.b_to_a,
  a_b_a := 
    λ _, by rw [comp_app, bc.a_b_a, ab.a_b_a],
  b_a_b := 
    λ _, by rw [comp_app, ab.b_a_b, bc.b_a_b],
}

-- Task 1-4 : Prove the following statement:
-- Given two functions A->B and B->A, if A->B->A is satisfied and B->A is injective, A <=> B
def bijection_alt {A B : Type} (ab : A → B) (ba : B → A) 
  (h : ∀ a, ba (ab a) = a) (hba: injective ba) : iso A B := 
{
  a_to_b := ab,
  b_to_a := ba,
  a_b_a := h,
  b_a_b := 
  begin
      intro b,
      apply hba,
      apply h,
  end
}

-- Task 2
-- iso relations between nat and various supersets of nat

-- nat_plus_1 : a set having one more element than nat. (provided in preloaded)

inductive nat_plus_1 : Type
| null : nat_plus_1
| is_nat (n : ℕ) : nat_plus_1

open nat_plus_1

def nat_to_nat_plus_1 : ℕ → nat_plus_1
  | 0 := null
  | (nat.succ n) := is_nat n

def nat_plus_1_to_nat : nat_plus_1 → ℕ
  | null := 0
  | (is_nat n) := nat.succ n

def nat_iso_nat_plus_1 : iso ℕ nat_plus_1 := 
{
  a_to_b := nat_to_nat_plus_1,
  b_to_a := nat_plus_1_to_nat,
  a_b_a :=
  begin
    intro n, cases n,
    {
      refl,
    },
    {
      rw [nat_to_nat_plus_1, nat_plus_1_to_nat],
    },
  end,
  b_a_b :=
  begin
    intro n, cases n,
    {
      refl,
    },
    {
      rw [nat_plus_1_to_nat, nat_to_nat_plus_1],
    },
  end
}

-- nat_plus_nat : a set having size(nat) more elements than nat. (provided in preloaded)

inductive nat_plus_nat : Type
| left (n : ℕ) : nat_plus_nat
| right (n : ℕ) : nat_plus_nat

inductive even : ℕ → Prop
| even_zero : even 0
| even_ss : ∀ {n}, even n → even (n + 2)

open nat_plus_nat


-- In Haskell this would use quotRem
-- ntnpn :: ℕ -> nat_plus_nat
-- ntnpn n
-- | r == 0    = left q
-- | otherwise = right q
-- where
--  (q, r) = quotRem n 2

def ntnpn : ℕ → nat_plus_nat := sorry 

def npntn : nat_plus_nat → ℕ
  | (left n) := 2 * n
  | (right n) := 2 * n + 1

def nat_iso_nat_plus_nat : iso ℕ nat_plus_nat := 
{
  a_to_b := ntnpn,
  b_to_a := npntn,
  a_b_a := sorry,
  b_a_b := sorry,
}
