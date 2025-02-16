import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:

If there's a function that maps every α value 
that exists to a β value that exists, and for
all α values a, predicate p on a implies 
predicate q on the β value that a is mapped to
through fucntion f. Which implies there exists
a value a of type α where predicate p holds on 
a and also implies there exists a value b of
type β where predicate q holds on b.
-/


-- Give your formal proof here
begin
  assume h,
  assume i,
  
  cases h with hf hp,
  cases i with alpha pa,

  have f := hp alpha,
  have j := f pa,

  apply exists.intro (hf alpha),
  exact j,
end
  
/-
informal proof:
we start by assuming our premise. then we 
take our assumption of our function and
obtain a name for our function and a proof
of what our function does. then we take α
and name it, and obtain a proof of predicate
p on α. from our proof that p a → q (hf a)
we can use our alpha as a witness, and from 
there it follows that we have a proof of 
q (hf alpha). finally we can use (hf alpha)
as a witness to the proposition we are trying
to prove, and since we have a proof of 
q (hf alpha), we are done.
-/
