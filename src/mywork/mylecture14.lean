axioms
  (Person : Type)
  (Likes : Person → Person → Prop)

example :
  ¬ (∀ p : Person, Likes p p) ↔
  ∃ p : Person, ¬ Likes p p :=
begin
  apply iff.intro _ _,

  assume h,
  have fornf := classical.em (∃ (p : Person), ¬Likes p p),
  cases fornf with f nf,
  exact f,

  have contra : ∀ (p : Person), Likes p p := _,
  contradiction,

  assume p,
  have g := classical.em (Likes p p),
  cases g,
  exact g,

  have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
  contradiction,

  assume h,
  cases h with p l,
  assume g,
  have a := g p,
  contradiction,
end