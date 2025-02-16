import data.set
import tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
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
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
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
ENGLISH:
we first assume b of type β exists. we assume relation r is both
transitive and reflexive. then, we assume it is asymmetric, and
by proving this false we can show that it cannot be asymmetric.
taking our b, we can generate a proof that r b b since we know 
relation r is reflexive. we have assumed that the relation is
asymmetric, so we can take our proof of r b b and create a proof
that ¬r b b, which creates a contradiction. QED.
-/

/-
the premise we needed to add to make the proposition true was
that we needed some b of type β to exist.

we first assume b of type β exists. we assume relation r is both
transitive and reflexive. then, we assume it is asymmetric, and
by proving this false we can show that it cannot be asymmetric.
taking our b, we can generate a proof that r b b since we know 
relation r is reflexive. we have assumed that the relation is
asymmetric, so we can take our proof of r b b and create a proof
that ¬r b b, which creates a contradiction. QED.
-/

/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
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
ENGLISH:
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
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end

/-
ENGLISH:
first we assume an arbitrary natural number n. saying divides 1 n
means that there exists some k s.t. n = k * 1. if we use the
exists intro rule to replace k with n, we show that n = n * 1. by
basic algebra, our proposition is shown to be true.
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end

/-
ENGLISH:
first we assume an arbitrary natural number n. saying divides n n
means that there exists some k s.t. n = k * n. if we use the
exists intro rule to replace k with 1, we show that n = 1 * n. by
basic algebra, our proposition is shown to be true.
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive divides,
  assume x,
  apply exists.intro 1,
  ring,
end 

/-
ENGLISH:
the proposition that divides is reflexive means that for every 
natural number x, there exists a natural number k such that
x = k * x. we first assume x is any arbitrary natural number.
and like our proof for 3b, we apply exists.intro to substitute
k for 1, and we show that x = 1 * x. by basic algebra, our
proposition is shown to be true.
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z,
  assume xdvy ydvz,

  cases xdvy with k1 xypf,
  cases ydvz with k2 yzpf,

  apply exists.intro (k1 * k2),
  rw yzpf,
  rw xypf,
  ring,
end 

/-
ENGLISH:
assuming that x, y, and z are arbitrary natural numbers...
we take the fact that divides x y to name a natural number k1
such that y = k1 * x. and similarly for divides y z, we have
a k2 such that z = k2 * y. we have to prove divides x z, which
means that there exists a k_1 such that z = k_1 * x. by using
exists.intro, we can substitute our k_1 to be k1 * k2. rewriting
our proposition, we can take z = k1 * k2 * x and turn it into
k2 * y = k1 * k2 * x since z = k2 * y. and y = k1 * x, so we get
k2 * (k1 * x) = k1 * k2 * x. and by basic algebra, we can prove
this to be true. QED.
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/-
ANSWER:
divides is not symmetric. if a number x divides a number y,
y does not necessarily divide x, only unless x = y. this
shows that divides is not symmetric.

counterex: 10 / 1 != 1 / 10
-/

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin
  unfold anti_symmetric,
  assume x y,
  assume xdvy ydvx,
  
  cases xdvy with kxy xypf,
  cases ydvx with kyx yxpf,

  rw yxpf at xypf,
  sorry,
end

/-
ENGLISH:
we assume x and y are arbitrary natural numbers. we assume
x divides y and y divides x. from our proofs of both we can
extract natural numbers kxy and kyx such that y = kxy * x
and x = kyx * y. by rewriting y = kxy * x with xypf, we get
y = kxy * (kyx * y). don't know how to formally prove the rest
here but... we know kxy * kyx must equal 1, and through
basic algebra we can deduce that kxy * kyx = kxy = kyx = 1.
then by rewriting y = kxy * x to y = 1 * x, through basic
algebra we have shown that y = x. because equality has
the property of symmetry it follows that x = y. 
-/

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
  assume rxx,
  have nrxx := asymm rxx,
  contradiction,
end

/-
ENGLISH:
we first assume our relation r on β is asymmetric.
we then assume x to be an arbitrary object of type β. 
then we assume r x x is false to prove ¬r x x. by 
using our proof that r is asymmetric and r x x, we 
can show that ¬r x x. this creates a contradiction, 
proving r x x false. QED.
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume irrefl trans,
  assume x y,
  assume rxy ryx,
  have rxx := trans rxy ryx,
  have nrxx := irrefl x,
  contradiction,
end

/-
ENGLISH:
we first assume our relation r is irreflexive and transitive.
we then assume x and y are both arbitrary objects of type β.
to prove that the relation is asymmetric, we prove that
symmetry on r is false. so, we assume r x y and r y x.
using the proof that r is transitive, and that r x y and
r y x, we get a proof that x is related to itself on r.
but since we have a proof that r is irreflexive, we generate
a proof that ¬r x x, which creates a contradiction, thus
proving symmetry to be false. QED.
-/

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  -- impossible to solve
end

/-
ENGLISH:
cannot be solved because we need to assume some b of type β
exists in order to prove this proposition.
-/

end relation
