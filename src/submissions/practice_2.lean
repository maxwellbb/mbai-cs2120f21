/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    assume pandp,
    apply and.elim_left pandp,
    
    assume p,
    apply and.intro _ _,
      exact p,
      exact p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume porq,
    apply or.elim porq,
      assume p,
      apply or.intro_right _ _,
        exact p,
    assume q,
      apply or.intro_left _ _,
        exact q,
    
    assume qorp,
      apply or.elim qorp,
        assume q,
        apply or.intro_right _ _,
          exact q,
    assume p,
      apply or.intro_left _ _,
        exact p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume pandq,
    apply and.intro _ _,
      exact and.elim_right pandq,
      exact and.elim_left pandq,
    
    assume qandp,
    apply and.intro _ _,
      exact and.elim_right qandp,
      exact and.elim_left qandp,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    assume hl,
    cases hl,
      cases hl_right,
      apply or.intro_left,
      exact and.intro hl_left hl_right,

      apply or.intro_right,
      exact and.intro hl_left hl_right,

    assume hr,
    cases hr,
      apply and.intro _ _,
        cases hr,
        exact hr_left,

        cases hr,
        apply or.intro_left _ _,
        exact hr_right,
    
      apply and.intro _ _,
        cases hr,
        exact hr_left,

        cases hr,
        apply or.intro_right _ _,
        exact hr_right,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    assume hl,
    cases hl,
      apply and.intro _ _,
        apply or.intro_left _,
        exact hl,
        
        apply or.intro_left _,
        exact hl,
    
    cases hl,
      apply and.intro _ _,
        apply or.intro_right _,
        exact hl_left,
      
        apply or.intro_right _,
        exact hl_right,
    
    assume hr,
    cases hr,
      cases hr_left,
        apply or.intro_left _ _,
        exact hr_left,

      cases hr_right,
        apply or.intro_left _ _,
        exact hr_right,

      apply or.intro_right _ _,
      exact and.intro hr_left hr_right,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume hl,
      cases hl,
      exact hl_left,
    
    assume hr,
      apply and.intro _ _,
        exact hr,

        apply or.intro_left,
        exact hr,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
    assume P Q,
    apply iff.intro _ _,
    assume hl,
      cases hl,
      exact hl,

      cases hl,
      exact hl_left,
    
    assume hr,
      apply or.intro_left,
      exact hr,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
    assume port,
    apply true.intro,

    assume t,
    apply or.intro_right,
    exact t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    assume porf,
    apply or.elim porf,
      assume p,
      exact p,

      assume f,
      cases f,
    
    assume p,
      apply or.intro_left,
      exact p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    assume pandt,
    cases pandt,
    exact pandt_left,

    assume p,
    apply and.intro _ _,
      exact p,
      apply true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
    assume pandf,
    apply and.elim_right pandf,

    assume f,
    apply and.intro _ _,
    cases f,
    exact f,
end


