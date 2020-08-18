def bad_theorem : Prop := 
  ∀ (α : Type) (r : α → α → Prop), symmetric r → transitive r → reflexive r

def fail (a b : unit): Prop := false
theorem fail_symm : symmetric fail := λ x y h, h
theorem fail_trans : transitive fail := λ x y z h1 _, false.rec (fail x z) h1
-- theorem not_refl_fail : ¬ reflexive fail := λ a, a ()

theorem correct_version : ¬ bad_theorem := λ a, a unit fail fail_symm fail_trans ()