# Arithmetic

In this chapter we adapt the what we've learned in the
chapter on propositional logic syntax and semantics to
specify the syntax and semantics of a simple language of
*natural number arithmetic*. The language we specify here
will have two distinct kinds of expressions.

An expression of the first kind of expression evaluates
to a natural number. Consider *2 + X*, for example. The
operator symbol, *+*, tells us that this expressions has
a natural number as its semantic meaning: namely, the sum
of *2* and whatever (now numberic) value *X* has under a
given interpretation. We will refer to *+* and similar
symbols as arithmetic *operators*, and to expressions
that use them as arithemtic *operator expressions*.

An expression of the second kind will evaluate not to a
numeric value but to a Boolean,. Consider *2 < X* as an
example. The standard symbol, *<* tells us that we can
expect this expression to evaluate to a Boolean value:
*true* if *2* is less than whatever value *X* evaluate
to, and to *false* otherwise. We will refer to symbols
such as *<* as *predicates*, and expressions such as
*2 < X* as *predicate expressions*.

We will use the phrase *arithmetic expression* to refer
to either an operator or a predicate expression in our
little language of natural number arithmetic.

One of the main insights that you can expect to take
away from this chapter is that you already knew how to
formally define a language such as this one by simple
adaptation of the lessons of the preceding chapter on
the syntax and semantics of propositional logic.
