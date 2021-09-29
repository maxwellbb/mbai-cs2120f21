-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  assume hl,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp with p np,
  cases qornq with q nq,

  have pandq := and.intro p q,
  contradiction,

  apply or.intro_right,
  exact nq,

  apply or.intro_left,
  exact np,

  assume hr,
  apply not.intro _,

  cases hr with np nq,
  assume pandq,
  cases pandq with p q,
  have f := np p,
  exact f,

  assume pandq,
  cases pandq with p q,
  have f := nq q,
  exact f,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h,

  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp with p np,
  cases qornq with q nq,

  apply and.intro _ _,
  assume p,
  apply not.intro h,
  apply or.intro_left,
  exact p,
  
  assume q,
  apply not.intro h,
  apply or.intro_right,
  exact q,

  apply and.intro _ _,
  assume p,
  apply not.intro h,
  apply or.intro_left,
  exact p,

  exact nq,

  cases qornq with q nq,
  apply and.intro _ _,
  exact np,

  assume q,
  apply not.intro h,
  apply or.intro_right,
  exact q,

  apply and.intro _ _,
  exact np,

  exact nq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,

  assume hl,
  have pornp := classical.em P,
  cases pornp with p np,

  apply or.intro_left _,
  exact p,

  apply or.intro_right,
  cases hl,

  contradiction,

  cases hl,
  exact hl_right,

  assume porq,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp with p np,
  cases qornq with q nq,
  apply or.intro_left,
  exact p,

  apply or.intro_left,
  exact p,

  cases qornq with q nq,
  apply or.intro_right,
  apply and.intro _ _,
  exact np,

  exact q,

  cases porq with p q,
  apply or.intro_left,
  exact p,

  apply or.intro_right,
  apply and.intro _ _,
  exact np,

  exact q,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,

  assume hl,
  cases hl with porq porr,

  cases porq with p q,

  apply or.intro_left,
  exact p,

  cases porr with p r,

  apply or.intro_left,
  exact p,

  apply or.intro_right,
  apply and.intro _ _,
  exact q,

  exact r,

  assume hr,
  apply and.intro _ _,

  cases hr,

  apply or.intro_left,
  exact hr,

  cases hr,

  apply or.intro_right,
  exact hr_left,

  cases hr,

  apply or.intro_left,
  exact hr,

  cases hr,

  apply or.intro_right,
  exact hr_right,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  assume hl,

  cases hl with porq rors,
  cases porq with p q,
  cases rors with r s,

  apply or.intro_left,
  apply and.intro _ _,
  exact p,
  exact r,

  apply or.intro_right,
  apply or.intro_left,
  apply and.intro _ _,
  exact p,
  exact s,

  cases rors with r s,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  apply and.intro _ _,
  exact q,
  exact r,

  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_right,
  apply and.intro _ _,
  exact q,
  exact s,

  assume hr,
  apply and.intro _ _,
  
  cases hr,
  cases hr with p r,

  apply or.intro_left,
  exact p,

  cases hr,
  cases hr with p s,
  apply or.intro_left,
  exact p,

  cases hr,
  cases hr with q r,

  apply or.intro_right,
  exact q,

  cases hr with q s,
  apply or.intro_right,
  exact q,

  cases hr,
  cases hr with p r,
  apply or.intro_left,
  exact r,

  cases hr,
  cases hr with p s,
  apply or.intro_right,
  exact s,

  cases hr,
  cases hr with q r,
  apply or.intro_left,
  exact r,

  cases hr with q s,
  apply or.intro_right,
  exact s,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : (∀ (n : ℕ), n = 0) → false :=
begin
  assume h,
  /--/
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  
  assume hl,

  have pornp := classical.em P,
  cases pornp with p np,
  have q := hl p,
  apply or.intro_right,
  exact q,

  apply or.intro_left,
  exact np,

  assume hr,
  assume p,
  have pornp := classical.em P,
  cases pornp with p np,
  cases hr,
  contradiction,

  exact hr,

  contradiction,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume ptoq,

  assume nq,
  have qornq := classical.em Q,
  cases qornq with q nq,
  contradiction,

  have pornp := classical.em P,
  cases pornp with p np,
  have q := ptoq p,
  contradiction,

  exact np,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume nptonq,

  have pornp := classical.em P,
  have qornq := classical.em Q,

  cases pornp with p np,
  cases qornq with q nq,

  assume q,
  exact p,

  assume q,
  exact p,

  assume q,
  have nq := nptonq np,
  contradiction,
end

