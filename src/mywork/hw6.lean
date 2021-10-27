import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

example : ∀ {α : Type} (L : set α), (L ∩ L = L) :=
begin
  assume α,
  assume L,

  apply set.ext _,

  assume x,
  split,

  assume h,
  cases h with l r,
  exact l,

  assume h,
  apply and.intro _ _,

  exact h,
  exact h,
end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

example : ∀ {α : Type} (L X : set α), L ∪ X = X ∪ L :=
begin
  assume α,
  assume X L,
  
  apply set.ext _,
  assume x,
  split,

  assume h,
  cases h,

  apply or.intro_right _,
  exact h,

  apply or.intro_left _,
  exact h,

  assume h,
  cases h,

  apply or.intro_right _,
  exact h,

  apply or.intro_left _,
  exact h,
end

/-
let L and X be sets of type α. the statement that 
L ∪ X = X ∪ L essentially means that for every 
element x, x is a member of L ∪ X if and only if
x is also a member of X ∪ L. by splitting proposition
into x ∈ X ∪ L → x ∈ L ∪ X and x ∈ L ∪ X → x ∈ X ∪ L
we now have two directions of implications to prove.
in our forward direction, we can prove our proposition
by splitting up our set X ∪ L into two cases: either
x is in X or x is in L. then, we can apply the or
elimination rules to show that both X and L are in
L ∪ X. the same general steps follow for the backwards
direction. QED.
-/

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

example : ∀ {α : Type} (A B C X : set α), X ⊆ X ∧ 
  (A ⊆ B → B ⊆ C → A ⊆ C) :=
begin
  assume α,
  assume A B C X,

  apply and.intro _ _,

  assume h,
  assume i,
  exact i,

  assume i,
  assume j,

  assume h,
  assume k,
  
  have hb := i k,
  have hc := j hb,

  exact hc,
end

/-
to show that ⊆ is reflexive and transitive, we are to
show that ∀ {α : Type} (A B C X : set α), X ⊆ X ∧ 
(A ⊆ B → B ⊆ C → A ⊆ C). by applying the intro rule
for and, we now have to just prove separately that 
X ⊆ X and A ⊆ B → B ⊆ C → A ⊆ C. for reflexivity,
we first assume X is an arbitrary set of type α.
to say X ⊆ X is to say that for every element h
∈ X is also a member of X (i.e., h ∈ X → h ∈ X),
which is obviously true. for A ⊆ B → B ⊆ C → A ⊆ C,
we assume that A, B, and C are all arbitrary sets of 
type α. we assume that A ⊆ B and B ⊆ C and to say that
A ⊆ C (what we need to prove) is to say that for every
element that ∈ A, is also a member of set C. we can 
easily obtain a proof that if h ∈ A then h ∈ B from our
proof of A ⊆ B. with the same logic, we know that if 
h ∈ B then h ∈ C. this gives us our proof that if 
h ∈ A then h ∈ C which is our proof that A ⊆ C. QED.
-/

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

example : ∀ {α : Type} (A B C : set α), ((A ∪ (B ∪ C)) = 
  ((A ∪ B) ∪ C)) ∧ ((A ∩ (B ∩ C)) = ((A ∩ B) ∩ C)) :=
begin
  assume α,
  assume A B C,
  
  apply and.intro _ _,

  apply set.ext _,
  assume x,
  split,

  assume h,
  cases h,

  apply or.intro_left _,
  apply or.intro_left _,
  exact h,

  cases h,
  apply or.intro_left _,
  apply or.intro_right _,
  exact h,

  apply or.intro_right _,
  exact h,

  assume h,
  cases h,
  cases h,
  
  apply or.intro_left _,
  exact h,

  apply or.intro_right _,
  apply or.intro_left _,
  exact h,

  apply or.intro_right _,
  apply or.intro_right _,
  exact h,

  apply set.ext _,
  assume x,
  split,

  assume h,
  cases h with a bc,
  cases bc with b c,
  apply and.intro _ _,
  exact and.intro a b,
  exact c,

  assume h,
  cases h with ab c,
  cases ab with a b,
  apply and.intro _ _,
  exact a,
  apply and.intro b c,
end

/-
to show that ∪ and ∩ are both associative we need to prove
the proposition that ∀ {α : Type} (A B C : set α), 
((A ∪ (B ∪ C)) = ((A ∪ B) ∪ C)) ∧ ((A ∩ (B ∩ C)) =
((A ∩ B) ∩ C)). this is to say that if an element is in
(A ∪ (B ∪ C)) then it is also a member of ((A ∪ B) ∪ C),
and similarly, if an element is in (A ∩ (B ∩ C)) then it is
also a member of ((A ∩ B) ∩ C). assuming A, B, and C are all
arbitrary sets of type α... to show this for ∪, we first
apply the set extensionality axiom and split our statement
into two separate directions. for the forward direction, we
show that forall x s.t. x ∈ A ∪ (B ∪ C) → x ∈ A ∪ B ∪ C.
assuming x is a member if A ∪ (B ∪ C), we can first split
this into two cases, one where x ∈ A and x ∈ B ∪ C. for x ∈ A,
we use the or introduction rules to show that if x ∈ (A ∪ B) ∪ C
then it is a member of either A ∪ B or just C, which means that
it is a member of either A, B, or C. since we know that x ∈ A, 
we have shown this. and then similarly for x ∈ B ∪ C, we can split
this into x ∈ B and x ∈ C, and in the same way split up 
x ∈ (A ∪ B) ∪ C again to easily prove the forward direction
completely. for the backwards direction, we show that x ∈ (A ∪ B) ∪ C
→ x ∈ A ∪ (B ∪ C). we essentially follow the same general steps,
splitting (A ∪ B) ∪ C into different cases and showing using or intro
rules that each case can prove that x is a member of (A ∪ B) ∪ C.

for ∩, we obviously first apply the axiom of set extensionality, 
before splitting our statement into two directions again. for our
forward direction, we need to show x ∈ A ∩ (B ∩ C) → x ∈ (A ∩ B) ∩ C.
from the definition of and we know that if x ∈ A ∩ (B ∩ C) then x is a
member of both A and B ∪ C, and if x is a member of B ∪ C then it is
a member of both B and C, which means x is a member of A, B, and C.
using and introduction rules we just need to show that x is a member of
(A ∩ B) and is a member of C separately to show x ∈ A ∩ (B ∩ C). and we
further break this down into x ∈ A and x ∈ B for x ∈ A ∩ B. now we just show
that x ∈ A and x ∈ B and x ∈ C, which we already know from earlier so this is
easily proven. for our backwards direction, we follow the same steps, 
breaking x ∈ (A ∩ B) ∩ C down into x ∈ A, x ∈ B, x ∈ C, and break our
statement to be proven down to the same thing, and is easily shown. QED.
-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

example : ∀ {α : Type} (A B C : set α), A ∩ (B ∩ C) = (A ∩ B)
  ∩ (A ∩ C) :=
begin
  assume α,
  assume A B C,

  apply set.ext _,
  assume x,
  split,

  assume h,
  cases h with a bc,
  cases bc with b c,
  apply and.intro _ _,
  exact and.intro a b,
  exact and.intro a c,

  assume h,
  cases h with ab ac,
  cases ab with a b,
  cases ac with a c,
  apply and.intro _ _,
  exact a,
  exact and.intro b c,
end

/-
first we assume that A, B, and C are all arbitrary sets of
type α. then after splitting our statement into two directions
after applying the axiom of set extensionality, we have two
directions to prove. for our forward direction, we first uses
cases to break A ∩ (B ∩ C) down into three proofs that show that
x ∈ A and x ∈ B and x ∈ C. to show that x ∈ (A ∩ B) ∩ (A ∩ C), we
just show that x is in A ∩ B and also in A ∩ C, which we can prove
by using the intro rules of and to prove both since we know that 
x ∈ A and x ∈ B and x ∈ C.

for backwards, we use cases to break down x ∈ (A ∩ B) ∩ (A ∩ C)
the same way to show that x ∈ A and x ∈ B and x ∈ C, which can
easily help us prove x ∈ A ∩ (B ∩ C) by using and intro rules
to split that into x ∈ A and x ∈ B ∩ C. the first part is already 
known and x ∈ B ∩ C is proven by using showing that x ∈ B and also
x ∈ C. QED.
-/

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

example : ∀ {α : Type} (A B C : set α), A ∪ (B ∩ C) =
  (A ∪ B) ∩ (A ∪ C) :=
begin
  assume α,
  assume A B C,

  apply set.ext _,
  assume x,
  split,

  assume h,
  cases h,

  apply and.intro _ _,
  apply or.intro_left _,
  exact h,

  apply or.intro_left _,
  exact h,

  cases h with b c,
  apply and.intro _ _,
  apply or.intro_right _,
  exact b,

  apply or.intro_right _,
  exact c,

  assume h,
  cases h with ab ac,
  cases ab,
  cases ac,

  apply or.intro_left _,
  exact ab,

  apply or.intro_left _,
  exact ab,

  cases ac,

  apply or.intro_left _,
  exact ac,

  apply or.intro_right _,
  exact and.intro ab ac,
end

/-
first we assume that A, B, and C are all arbitrary sets of
type α. then after splitting our statement into two directions
after applying the axiom of set extensionality, we have two
directions to prove. for our forward direction, we break down
the fact that x ∈ A ∪ B ∩ C into x ∈ A and x ∈ B ∩ C. then break
our statement, x ∈ (A ∪ B) ∩ (A ∪ C), using and intro to just prove
x ∈ A ∪ B and x ∈ A ∪ C. since for both A ∪ B and A ∪ C we just need
to prove that x is a member of A, which we know, then we have proven
both. for the cases where x ∈ B ∩ C, we know that btoh x ∈ B and x ∈ C
which proves A ∪ B and A ∪ C both. lastly, in our backwards direction,
by breaking down our knowledge that x ∈ (A ∪ B) ∩ (A ∪ C), we can split
this into cases so that x ∈ (A ∪ B) and x ∈ (A ∪ C) and then using
cases analysis once again we just prove that x ∈ A ∪ B ∩ C for the
different cases. this ends up being really easy using or intro rules
and finally, to prove x ∈ B ∩ C, we can use and intro rules while
knowing that x ∈ B and x ∈ C. 
-/
