/-
Operations on relations
-/

/-
We now change our attention to binary relations
more generally: not just from β → β but between
different types, α and β. Not the change in the
type of r as defined here.
-/
variables {α β γ : Type} (r : α → β → Prop)
local infix `≺`:50 := r

/-
In these examples we will treat that the types, 
α and b, as mathematical sets of objects of these
types. 

We will call the set of all α values the "domain
of definition" of the relation r, and we will call
the set of all β values the co-domain of r. Now
the (a, b) pairs of r represent the pairs of values
for which r a b is true. 

Not every value in α needs to be present in the 
set of "a" values that appear as first elements
in the pairs of r. The subset of a values that 
do appear in the first position of some pair in
r is what we will call the domain of the relation. 

The set of b values that appear in the second
positions in all such pairs of r is the set we
will call the *range* of the r. 

Without definitely need to know and understand
the definitions. Be able to write the formal
definitions, which we present next, from your
memory and even more from your understanding 
of what they mean. If you really understand,
then you should be able to derive the formal
definition without having memorized it. Here
are the first four essential terms:

- domain of definition
- domain
- co-domain
- range

It's obviousl that  will always have that 
- domain ⊆ domain of definition
- range ⊆ codomain

With these concepts in hand, we can really start
to  precisely and clearly define powerful ideas
in set theory, and to express and prove theorems
in this setting.
-/

/-
We begin with sets involved in any relation, 
r : α → β. For simplicity here, we will assume
that the domain of definition set in examples
that follow is specified by the type α, and
that the co-domain set is specificed by the
β type.
-/
def domain_of_definition (r : α → β → Prop) : set α := { a : α | true } 
def domain (r : α → β → Prop) := { a : α | ∃ b, r a b }
def co_domain (r : α → β → Prop) := { b : β | true }
def range (r : α → β → Prop) := { b : β | ∃ (a : α), r a b  }

-- EXAMPLE
def R : ℕ → string → Prop := λ n m, n = m.length
#check domain_of_definition R
#reduce domain_of_definition R
#check co_domain R
#reduce co_domain R -- what set?
#check domain R
#reduce domain R    -- a set, right?
#check range R
#reduce range R     -- a set, right?


/-
It will often be useful to consider the
subrelation obtained by restricting the
domain of a relation to elements of a given
set. 

If a relation relates three cats, c1, c2, 
and c3, to their ages, say a1, a2 and a3,
respectively, then restricting the domain
of r to the set, s = {c1, c3}, would give
the relation associating c1 and c3 with
corresponding ages, but there would be no
(c2, a2) pair in the restricted relation
because c2 ∉ s. An analogous definition 
gives us the range restriction of r to a
set, s. 
-/

/-
Note that these operations take relations and
sets as arguments and "return" new relations!
Of course, these are logical specifications, 
not programs, so they don't really compute 
anything at all, but they do formally specify
extremely useful programs that would compute
these operations, at least for finite sets of
things.
-/
def dom_res (r : α → β → Prop) (s : set α) : α → β → Prop := 
  λ a b, r a b ∧ a ∈ s  -- (a,b) pairs in r for which a ∈ s   

def ran_res (r : α → β → Prop) (s : set β) : α → β → Prop := 
_                       -- homework


/-
In a relation in general, an α value can have zero,
one, or more corresponding β values. As a nice example,
consider the binary relation on real numbers defined
by x^2 + y^2 = 1^2. From basic algebra, recall that,
by the pythagorean theorem, this relation comprises
all of the x-y pairs in the unit circle. It's the
set of real number (x,y) pairs for which x^2+y^2=1.

Now where x is zero, as an example, there is not one
but there are two corresponding y values: -1 and 1.
That's fine because a relation is *any* subset of
the set of all α-β pairs. In particular, the "circle"
relation contains both (0,1) and (0,-1). Each pair
satisfies the specification, that x^2+y^2=1. Be sure
you see that this simple algebraic claim is correct.

If we think of "applying" a relation to a value, then,
we have to get back not a single value, in general, but
a set of values that could, in general, be empty, be
a singleton set, or have more than one value. In our
case here where r is the unit circle relation, what
should we expect as the value of (r 0)?

Yes, it's the set { 1, -1 }. We will this result set
the "image" of 0 under r. I guess you can think of r
as being like a bright light shining on 0 from the
left and being blocked from projecting through to the
corresponding β values except for where that 0 is.
What gets illuminated in this case is the set of β 
values, { 1, -1 }.

We can then easily extend this concept to the image
of a set of α values.

Note that the folloowing operations take a relation
and a value and return a set of values.
-/

-- image of an "argument" value under r
def image_val (a : α) : set β :=
{ b : β | a ≺ b } 

-- image of a set, s, of arguments, under r
def image_set (s : set α) : set β :=
{ b : β | ∃ a : α, a ∈ s ∧ a ≺ b }


/- HOMEWORK
Define the concepts of the *pre-image* of a
value of type β or of a set of such values.
-/

/-
Here's another operation that takes a relation
and returns a relation: namely the same as the
original but with all the pair arrows reversed.
-/
-- inverse of r
def inverse : β → α → Prop :=
λ (b : β) (a : α), r a b


/-
Finally we have this beautiful operation that
takes two relations as arguments and glues them
together into a new end-to-end relation: the
*composition* of s with r. The result of applying
this relation to an (a : α) is the (c : γ) that
is obtained by applying the relation s to the 
result of applying the relation r to a. We can
thus call the resulting relation "s after r."
-/
def composition (s : β → γ → Prop) :=
  λ a c, (∃ b, s b c ∧ r a b)

/-
EXAMPLE
-/

def square := (λ a b : ℕ, b = a * a)
def incr := (λ b c : ℕ, c = b + 1)
def square_after_incr := composition square incr

/-
square_after_incr is like a function where a
value enters from the right, first moves left
through incr, and the result of tha then moves
through square, to emerge on the left side as
the final result. So, again the function can
be called square after increment (where incr
is short for increment).
-/

#check square             -- binary relation on ℕ 
#check incr               -- binary relation on ℕ
#check square_after_incr  -- binary relation on ℕ
#reduce square_after_incr -- λ (a c : ℕ), ∃ (b : ℕ), 
                          --  c = b.succ ∧ b = a.mul a
                          -- another relation on ℕ 

/-
State and prove the conjecture that (3,10) 
is "in" the square_after_incr relation.
-/
example : square_after_incr 3 10 :=
begin
unfold square_after_incr square incr composition,
apply exists.intro 9,
split,
repeat { exact rfl },
end

/-
Proof.
Unfolding all of the definitions we see we are
to prove ∃ (b : ℕ), 10 = b + 1 ∧ b = 3 * 3. Let
b = 9, split the conjunction, and prove each side
by simplifying and the reflexivity of equality. 
QED.
-/
