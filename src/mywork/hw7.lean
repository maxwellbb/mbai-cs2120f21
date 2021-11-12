import ..instructor.lectures.lecture_23

namespace relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  
-- Strangely Lean's library does define asymmetric, so here it is.
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x



-- Prove both formally and in English.
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  assume ex,
  assume asymm,
  assume refl,
  cases ex with b pf,
  have rbb : r b b := refl b,
  have contra := asymm rbb,
  contradiction,
end

/-
To prove that if a relation is asymmetric implies not reflexive...
first we assume that there exists a b of type β, and then assume
that the relation is asymmetric. To prove not reflexive, we just
need to prove that the assumption that the relation is reflexive
is false. We can prove that through a contradiction...
We generate a proof that the relation on b is reflexive through
our proof that relation r is reflexive and our b. Then, we take
our proof that r is asymmetric to generate a proof that ¬r b b
using rbb as a witness. Then, because we have both r b b and
¬r b b, we have a contradiction. QED.
-/


/-
Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. Is it actually true?
If not, what condition needs to be added to make it true? See
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html
-/
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  assume b,
  unfold transitive reflexive asymmetric,
  assume trans refl,
  assume asymm,
  cases b with b and pf,
  have rbb := refl b,
  have nrbb := asymm rbb,
  contradiction,
end

/-
we first assume b of type β exists. we assume relation r is both
transitive and reflexive. then, we assume it is asymmetric, and
by proving this false we can show that it cannot be asymmetric.
taking our b, we can generate a proof that r b b since we know 
relation r is reflexive. we have assumed that the relation is
asymmetric, so we can take our proof of r b b and create a proof
that ¬r b b, which creates a contradiction. QED.
-/

/-
State and prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and then give
an informal proof, of this proposition. You may use the following
formal definition of the powerset of a given set, s. 
-/

def powerset (s : set β) := { s' | s' ⊆ s}

example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1ins s2ins s12 s21,
  apply set.ext _,
  assume x,
  apply iff.intro _,

  assume h,
  have xins1 := s21 h,
  exact xins1,

  assume h,
  have xins2 := s12 h,
  exact xins2,
end

/-
first we assume that s is an arbitrary set with elements of type β.
then we assume that s1 and s2 are subsets of s, and that s1 is a
subset of s2 and vice versa. to prove that s1 = s2...
we first apply set extensionality, and assume an arbitrary element
x. first we prove that if x is an element of s1, then it is an element
of s2. this is easy to proof since we know that s1 is a subset of s2. we
do the same for x in s1 if it is in s2 since s2 is also a subset of s2.
QED.
-/

/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/

def divides (m n : ℕ) := ∃ k, n = k * m

/- 
#3: Formally state and prove each of the following propositions.
Remember that the ring tactic is useful for producing proofs of
algebraic equalities involving + and *. You can use the phrase,
"by basic algebra" when translating the use of this tactic into
English.
-/

-- 3a: For any n, 1 divides n.

example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end

/-
first we assume an arbitrary natural number n. saying divides 1 n
means that there exists some k s.t. n = k * 1. if we use the
exists intro rule to replace k with n, we show that n = n * 1. by
basic algebra, our proposition is shown to be true.
-/

-- 3b. For any n, n divides n

example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end

/-
first we assume an arbitrary natural number n. saying divides n n
means that there exists some k s.t. n = k * n. if we use the
exists intro rule to replace k with 1, we show that n = 1 * n. by
basic algebra, our proposition is shown to be true.
-/

-- #3c. divides is reflexive (use our reflexive predicate)

example : reflexive divides :=
begin
  unfold reflexive divides,
  assume x,
  apply exists.intro 1,
  ring,
end 

/-
the proposition that divides is reflexive means that for every 
natural number x, there exists a natural number k such that
x = k * x. we first assume x is any arbitrary natural number.
and like our proof for 3b, we apply exists.intro to substitute
k for 1, and we show that x = 1 * x. by basic algebra, our
proposition is shown to be true.
-/

-- #3d. divides is transitive

example : ∀ h n k, divides h n → divides n k → divides h k :=
begin
  assume h n k,
  unfold divides,

  assume hdvn ndvk,
  cases hdvn with k1 pf1,
  cases ndvk with k2 pf2,

  apply exists.intro (k1 * k2),
  rw pf2,
  rw pf1,
  ring,
end 

/-
assuming that h, n, and k are arbitrary natural numbers...
we take the fact that divides h n to name a natural number k1
such that n = k1 * h. and similarly for divides n k, we have
a k2 such that k = k2 * n. we have to prove divides h k, which
means that there exists a k_1 such that k = k_1 * h. by using
exists.intro, we can substitute our k_1 to be k1 * k2. rewriting
our proposition, we can take k = k1 * k2 * h and turn it into
k2 * n = k1 * k2 * h since k = k2 * n. and n = k1 * h, so we get
k2 * (k1 * h) = k1 * k2 * h. and by basic algebra, we can prove
this to be true. QED.
-/

/- 
#3d. is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/-
divides is not symmetric. if a number x divides a number y,
y does not necessarily divide x, UNLESS x = y. this shows
that divides is not symmetric and not antisymmetric either.

counterex: 10 / 1 != 1 / 10
-/

/- 
#3e. Prove that divides is antisymmetric. Use the
anti_symmetric predicate to state the proposition
formally.
-/
example : relations.anti_symmetric divides := 
begin
  unfold relations.anti_symmetric divides,
  assume x y kx ky,
  cases kx with kxv kxpf,
  cases ky with kyv kypf,
  rw kxpf at kypf,
  /-
  From kypf we can deduce by basic algebra
  that kyv = kxv = 1, and the rewriting kxv
  as 1 in kxpf, we get that y = x. The proof
  of the conclusion then follows by symmetry
  of equality. We don't yet quite have the
  tools to reason formally to the conlusion
  that kxv and kyv are both one, so we'll 
  just admit it as an axiom for now, using
  sorry to remind us to come back and visit
  this point again when we're equipped to 
  polish off the formal proof.
  -/
  sorry,
end

/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume asymm x,
  assume k,
  have nrxx := asymm k,
  contradiction,
end

/-
we first assume our relation r on β is asymmetric.
we then assume x to be of type β.
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume h k,
  assume x y,
  assume rxy nryx,
  have rxx := k rxy nryx,
  have nrxx := h x,
  contradiction,
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume trans symm refl,
  
end


end relation
