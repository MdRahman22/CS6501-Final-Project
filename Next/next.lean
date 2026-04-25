/- @@@

So what's coming next? We have to finish out proof
theory first, then we'll get on to set theory. There
are two main parts to what is left of proof theory.
First, we need predicates (represented constructively
as functions from whatever to Prop).

Predicates are just *propositions with placeholders*.
You fill the placeholders of a predicate by applying
to actual parameters. But why do we want parameterized
propositions (predicates) at all?

As a motivating example, consider a proposition called
*henryIsReallyNice*. It's a good one, but this style of
representations means a separate proposition for every
single person we wanted to say is really nice.

The answer is *abstraction*. We cover all variants at
once with a single definition. If henry is a Person, and
isReallyNice : Person -> Prop, is a predicate (function)
then the term, (isReallyNice henry : Prop), by modus
ponens, is a proposition,, that we can read in English
as *Henry is really nice*.

We've already seen predicates a few times, namely in
relation to ∀ propositions (universal generalizations).
The form of a universal generalization is written as:
\all (a : A), B a. Left of the comma is the binder. It
binds the name, a, to an arbitrary (thus any) object
of type A. After the comma comes a proposition about
the object, *a*. B is a predicate (e.g., IsReallyNice), and
the bound variable, *a*, (Henry), is its subject. We
put it all together and interpret (\all (a : A), B a)
to assert that every a has property B.

For example, ∀ (p :Person), IsReallyNice p, is defined
to be true exactly when every Person (all Persons, any
Person) satisfies the predicate, IsReallyNice.  

So, that's half old news. Now you need the second of the
two quantifiers if predicate logic, whether first-order
or higher-order. It's Exists. An existential proposition,
written \exists (a : A), B a, is read as asserting that
there exists some object, call it a, of type A, such that
the proposition,, B a, is valid.

For example, ∃ (p : Person), IsReallyNice p, is defined
to be true just when there is some (at least one) person,
p, who is really nice: who satisfies the predicate. What
this means constructively logic is that *IsReallyNice p* 
has a proof, *(pf_IRN : IsReallyNice p)*.

Such a proof object is a value of type (IsReallyNice p),
this type itself being in (of type) Prop, making it also
a logical proposition. It's in Prop, because isReallyNice
is a function from Person to Prop. When applied to a person
the result is of type Prop: voila, a proposition. A proof
of (IsReallyNice henry) it will depend on exaclty how the
terms, Person and IsReallyNice are defined, but in general
a proof will encode "evidence" that *Henry in particular*
is nice.   

Now that we know how to prove *B a* (IsReallyNice henry),

how does one prove  *∃ (a : A), B a*? A constructivist
won't accept a proof of existence of any kind of object
without having a concrete instance to serve as a witness
to the existence of such an object. Of course not every
value (a : A) will satisfy B in general, so in addition
 a witness, one needs a proof of *(B a)*

 A constructive proof of existence is thus a kind of pair.
 The first element is some (a : A). The second is a proof
 of *(B a)*: a proof that *a* has the property that *B*
expresses (e.g., *IsReallyNice*).

{A : Type} (B : A -> Prop) (w : A)  (h : B a)
----------------------------------------------- Exists_intro
         ( < a, h >  :  \exists (a : A),  B a)

Yes, but what about Exists.elim? Ah. An interesting question! 


The second (and )last part of what remains of proof theory is induction.

This will take a little time.

Suppose you want to prove something about the natural numbers. Maybe this:

\all (n : Nat), (n<>0 -> \exists (m : Nat), n = m + 1

In English, every natural number except zero is the successor (. + 1) of some one-smaller natural number. 

Here's the rub. A case analysis won't do, as there's an infinity of cases that'd have to be checked. At this point we have no way to proceed. We have no axiom that would let us conclude that the predicate holds for every number other than zero (ruled out of consideration by the initial unequal-to (<>) condition). How can one construct proofs for types with finite or even infinite numbers of values (what are the introduction axioms)? And how can one use such proofs (what are the elimination principles)?

Well,, it turns out that every single inductively defined type (structure, inductive) has its own introduction rules, which are its highly visible constructors, but it also has its own elimination principles. These are the fundamental rules that tell you how you can take apart and access the internal structure of a given type of object. This is where things start to get pretty deeply interesting! Don't start skipping out on classes now :-)
-/
