import data.set

/- #1

Formally prove that if there's an object, a, of some 
type, α, having some property (satisfying a predicate), 
P, then not every object of type α fails to have property, 
P. Add a brief comment before each line of your proof 
script to provide what amounts to the outline of a good
English language proof.
-/

example (α : Type) (P : α → Prop) : (∃ a, P a) → (¬(∀ x, ¬ P x)) :=
begin
  -- assume the premise
  assume h,
  -- there is some value a of type α that has the property P a,
  cases h with a Pa,
  -- assume the premise again
  assume nh,
  -- Apply a to the proposition nh
  have nPa := nh a,
  -- form a contradiction
  contradiction,
end


/- Extra credit. 

The converse of this proposition is clasically true. If
not every object lacks propery, P, then there must be some
object that has it. If you try to prove the converse in
our constructive logic, what happens? Show you work, and
then briefly but clearly explain exactly what goes wrong.
-/
example (α : Type) (P : α → Prop) :  (¬(∀ x, ¬ P x)) → (∃ a, P a):=
begin

end
-- there won't be a value of type α to move forward with the proof,
-- therefore classical.em would be needed to prove this proposition.

/- #2

Consider the following binary relation, r, with domain
and co-domain both being ℕ. For each following question,
answer yes/no then briefly justify your answer.

( domain = ℕ, r = {(0,0),(1,1),(2,2)}, co-domain=ℕ )

A. Is this relation reflexive? 
Reflexive : ∀ a, r a a, FOR ALL values in DOMAIN
No, reflexive holds true for every value in the domain. The relation only
holds true for the numbers 0, 1, 2, but not all other Natural numbers,
therefore this relation is not reflexive.
B. Is this relation symmetric? 
Symmetric : r a b → r b a
Yes, 0 maps to 0, 1 maps to 1, 2 maps to 2. 
C. Is this relation transitive? 
Transitive : r a b → r b c → r a c
Yes, because the same number maps to itself multiple times.
D. Is this relation an equivalence relation? 
No, because it does not have all the properties above.
-/



/- #3

A binary relation, r, is said to be *anti-symetric* 
if, for all values in its domain, a and b, if r a b 
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.

Anti-symmetric : r a b → r b a → a = b
                (Symmetric r) → (a = b)

a <= b → b <= b → a = b

r a b,
a domain, b co-domain
-/


/- #4
A binary relation, r, is said to be *asymmetric* if
whenever, for any a and b, if r a b then ¬ r b a. Be
careful to note that asymmetry and antisymmetry are
different properties.  Answer each of the following 
sub-questions. We give you a formal definition of anti
-/

def is_asymmetric 
  {α : Type} 
  (r : α → α → Prop) : Prop 
  := ∀ (a b : α), r a b → ¬ r b a 

/- A.

Name a familar arithmetic relation that's asymmetric
and briefly explain why you think it's asymmetric.

Answer here: Greater Than, If a is greater than b, then it is not the case
that b is greater than a,
-/

/- C: 

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a. <finish
the proof>.

Answer here (rest of proof): 
We have r a a, and the goal is to show ¬ r a a. 
This is a contradiction.
-/

/- D.

Now prove a closely related proposition formally. 
Add a comment to each line of your formal proof 
so as to construct a good skeleton for a fluent 
English language proof.
-/

example
  (α : Type) 
  (r : α → α → Prop)
  (h : is_asymmetric r) :
¬ ∃ (a : α), r a a :=
begin
  -- proof by negation
  -- assume the premise
  assume p1,
  -- do cases on the for each statement
  cases p1 with a raa,
  -- unfold is_asymmetric at h to see what is_asymmetric is
  unfold is_asymmetric at h,
  -- apply a and a to the proposition h,
  have p2 := h a a,
  -- p2 raa forms a proof of not raa
  have nraa := p2 raa,
  -- contradiction to finish the proof.
  contradiction,
end


/- #5
Prove that equality on an inhabited (non-empty) type 
is not assymetric. In the following formalization we
assume there is a value (a : α), which establishes 
that α is inhabited.
-/

example (α : Type) (a : α): ¬ is_asymmetric (@eq α) :=
begin
  unfold is_asymmetric,
  assume assymEQ,
  have p1 := assymEQ a a,
  have neq := p1 rfl,
  contradiction,
end

/- Extra credit: What exactly goes wrong in a formal 
proof if you drop the "inhibitedness" condition? Give
as much of a formal proof as you can then explain why
it can't be completed (if it can't!).


-/
example (α : Type) : ¬ is_asymmetric (@eq α) :=
begin
  unfold is_asymmetric,
  assume assymEQ,
  -- we are stuck here because we don't have a value of type α.
end


/- #6
Two natural numbers, p and q, are said to be 
"equivalent mod m" if p % m = q % m, which makes
"equivalence mod m" a binary relation on natural
numbers. Here's a formal definition of this binary
relation on the natural numbers (given an m).
-/

def equiv_mod_m (m : ℕ) : ℕ → ℕ → Prop := 
  λ p q : ℕ, p % m = q % m

/-
Prove using Lean's definition of "equivalence" that 
equiv_mod_m is an equivalence relation for any natural
number, m. Here you'll also use Lean's definitions of
reflexive, symmetric, and transitive. They are as we
have covered in class. 
-/

example : ∀ m : ℕ, equivalence (equiv_mod_m m) :=
begin
  assume m,
  unfold equivalence equiv_mod_m,
  split,
  {
    unfold reflexive,
    assume x,
    apply rfl,
  },
  {
    split,
    {
      unfold symmetric,
      assume x y,
      assume h,
      rw h,
    },
    {
      unfold transitive,
      assume x y z,
      assume h1 h2,
      rw h1,
      rw h2,
    }
  }

end



/- #7
Consider the relation, tin_rel, that associates people 
with U.S. taxpayer id numbers, which we'll represent as 
natural numbers here. 

Assume this relation is single-valued. Which of the 
following properties does this relation have? Give
a very brief justification of each answer. Assume
the domain is all living persons, and the co-domain
is all natural numbers.

-- it's a function: 
Yes, because it is single-valued.
-- it's total: 
total : everything in the domain has to have an output
No, becasue not every living person has a taxpayer ID number.

-- it's injective :
Yes, becasue two people cannot map to the same ID number

-- it's surjective (where the co-domain is all ℕ):
surjective : every natural number has a person associated with it
No, because not every possible taxpayer ID number has a person associated with it

-- it's strictly partial:  
Yes, because not every US living person has a tax ID number

-- it's bijective: 
Bijective = surjective ∧ injective.
The statement is not surjective, so it is not bijective
-/



/- #8
Suppose r is the empty relation on the natural 
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

-- reflexive:
The statement does not cover the entire domain, therefore it is not
reflexive.
-- symmetric: 
We cannot provide a contradictary proof that it is not symmetric,
therefore it is symmetric.
-- transitive:
Same idea as symmetric. We cannot prove that it is not transitive, 
therefore it is transitive.
-/



/- #9
Here's a formal definition of this empty relation.
That there are no constructors given here means there 
are no proofs, which is to say that no pair can be 
proved to be in this relation, so it must be empty.
-/

inductive empty_rel : ℕ → ℕ → Prop

/-
Formally state and prove you answer for each of the
three properties. That is, for each property assert
either that empty_rel does have it or does not have it, 
then prove your assertion. Include English-language 
comments on each line to give the essential elements 
of a good English language proof.
-/


example : ¬reflexive empty_rel :=
begin
unfold reflexive,
assume h,
let x := h 0,
cases x,
end

example : symmetric empty_rel :=
begin
unfold symmetric,
assume a b h,
cases h,
end

example : transitive empty_rel :=
begin
assume a b c h k,
cases h,
end

/- #10
A relation, r, is said to have the property of being 
a *partial order* if it's reflexive, anti-symmetric,
and transitive. Give a brief English language proof 
that the subset relation on the subsets of any set, 
S (of objects of some type), is a partial order. 

Pf:  
Suppose S is a set, with a ⊆ S and b ⊆ S subsets. Then

1. Reflexive, a is a subset of itself.
2. Anti-symmetric, if a is a subset of b, and b is a subset of a,
    then a is the same as b.
3. Transitive, if a is a subset of b, and b is a subset of c, 
    then a must be a subset of c. 

QED.
-/



/- #11 
Finally we return again to DeMorgan's laws, but
now for sets. You'll recall that these "laws" as we
have seent them so far tell us how to distribute ¬  
over ∨ and over ∧. You will also recall that set
intersection (∩) is defined by the conjunction (∧) 
of the membership predicates, set union (∪) by the
disjunction (∨), and set complement (Sᶜ for a set,
S), by negation (¬). It makes sense to hypothesize 
that we can recast DeMorgan's laws in terms of the
distribution of complement over set union and set
intersection. Indeed we can. Your job is to state
and prove (formally) the first DeMorgan laws for 
sets, which states that the complement of a union
of any two sets equals the intersection of their 
complements.

Hint: To prove that two sets are equal, S = T, use
the ext tactic. It applies a bew axiom (called set 
extensionality) that states that to prove S = T it 
suffices to prove S ↔ T, viewing the sets as being
defined by their logical membership predicates. You
know how to handle bi-implications. The rest you 
can do by seeing "not," "and," and "or" in place 
of complement, conjunction, and disjuction, resp.  
-/

example 
  (α : Type) 
  (a b: set α) :
  (a ∪ b)ᶜ = aᶜ ∩ bᶜ := 
begin
  ext,
  apply iff.intro _ _,
  {
    assume notAUB,
    split,
    {
      assume xa,
      have AUB := or.inl xa,
      have f := notAUB AUB,
      contradiction,
    },
    {
      assume xb,
      have AUB := or.inr xb,
      have f := notAUB AUB,
      contradiction,
    }
  },
  {
    assume ACBC,
    assume AUB,
    cases AUB with A B,
    {
      have XA_prime := and.elim_left ACBC,
      contradiction,
    },
    {
      have XB_prime := and.elim_right ACBC,
      contradiction,
    }
  }
end


