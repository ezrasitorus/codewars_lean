theorem not_not_not 
  (P : Prop) :
  ¬ ¬ ¬ P → ¬ P := 
λ h p, h $ not_not_intro p