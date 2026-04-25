# Reasoning and Computation

## Important Distinct Forms of Reasoning

- Abductive
- Inductive
- Deductive

### Abductive Reasoning

Abductive reasoning is a form of logical inference where you start with an observation or set of observations, often by *noticing* discrepancies that others might miss, and then in your mind you search for a most plausible explanation for them. Abductive reasoning is often summarized as “inference to the best explanation.” Abduction hypothesizes an explanation that could make the observed facts true.

Example: If you walk outside and the ground is wet, you might abductively reason that it has rained. Other explanations are possible (sprinklers, someone washing a car), but rain may seem most plausible.

Abduction is central in everyday reasoning: medical diagnosis, scientific discovery, debugging. Take debugging. You are trying to determine why your program is malfunctioning. You slow it down using a debugger to study its internal states. You notice that the bug always seems to act up when a particular function is called. You hypothesize (by abduction) that the bug is actually in that function. You then go on to test your hypothesis. If a first hypothesis turns out to be wrong, you try again. If it was right, now you know what's wrong and so can proceed to fix it.

### Inductive Reasoning

Inductive reasoning is about generalizing from particular cases to generalied models. Inductive reasoning underlies much of science, statistics, and machine learning. Inductive reasoning begins with (often systematic) observation then tries to fit a generalized model to given data in order to then have a basis for predicting future data for as yet unseen cases.

One first chooses a class of *models* (such as linear, i.e., just straight lines), and finds a model instance of that kind (a specific *slope* and **y-intercept* that specifies the line that *best fits* the data in the sense that a measure of how much the it's off by is minimized. The idea is that such a model can have good predictive power. Large language model AI systems work by predicing the best next word over and over again, starting from the prompt. Inductive reasoning can be human and intuitive, too: e.g., it doesn't take too many times touching a hot pan to learn a model in your mind that predicts is a darned bad idea to ever do it again.

As for selecting a class of models, remember Johannes Kepler. Based on incredibly careful, comprehensive, detailed  observational data on the planets by Tycho Brahe, Kepler *inductively reasoned* to the conclusion that right class of models to describe the orbits of planents was eliptical not circular. Finding beautful models or classes of models that match data beautifully and then exhibit good predictive power thereafter is at the very heart of science, and human reasoning more generally. One might even say that intelligence is closely related to the rate at which one learns from data/experience. Hot stove: one-shot learning!

### Deductive Reasoning

Deductive reasoning is a process of deriving of necessary conclusions from given logical assumptions using specified rules of inference. For example, suppose we know that a liqud labelled *A* is poison, and we know that a different liquid labelled *B* is also poison. Suppose furthermore that we know that Billy drank *A* or Billy drank *B*. Before you read any further, what happened to poor Billy?

Quickly reviewing what we already know from class, to construct a proof of a proposition, *P ∧ Q*, one must have a proof (call it *p*) of the proposition, *P*, and one must have a proof (call it *q*) of the proposition *Q*. In this case, one can then have a proof of *P ∧ Q,* by *applying* the proof-building inference rule, *And.intro*, to the proofs, *p* and *q*, like this: *And.intro p q*.  This term is, in this logic, the one possible proof of *P ∧ Q*.

But in the case of poor Billy, we have *Or* proposition (he drank *A* or he drank *B*), not an *And*. The inference rules for And are of no use with Ors! So here comes a new inference rule for *Or*: if you know that A or B, written *(A ∨ B),* is true, and you also know that the same result occurs in either case, then you know that that result occurs.

Sadly, then because he drank this poison or he drank that poison, and because *in either case* drinking it is a very bad choice, poor Billy is no longer with us in this imaginary *world*.

We now even present our new inference rule both formally and generally:

```lean
  ∀ (P Q R : Prop),     -- if you have *any* (∀) three propositions, P, Q, and R
    (porq : P ∨ Q) ∧    -- and if you have a proof that (P or Q) is true  
    (pimr : P → R) ∧    -- and if you have a proof that *if P is true so is R*
    (qimr : Q → R ) →   -- and if you have a proof that *if Q is true so is R*
    R                   -- by the *or elimination* rule, you have a proof of *R*  
```

Check your own understanding: How do P, Q, and R correspond to "Billy drank A,"
"Billy drank B", and "Billy died?" in the preceding generalized expression?

## Constructive Logic

For the rest of this class, we shall be concerned with *deductive* reasoning. It as the crucial form of reasoning required to understand propositions and proofs in mathematics. We will use the constructive logic of the *Lean 4 programming language and proof assistant* as both the most useful logic for new computer scientists to learn today and as an incredible tool for learning formal reasoning in general.

In this class you will gain essential pre-requisites for understanding *inductive learning systems* at a technical level in your future classes. These are the machine learning systems underpinning the current artificial intelligence (AI) craze. In the first part of this course you will learn *predicate logic*, with *propositional logic* as a simple special case to start. This is the basic language of everyday mathematical expression. With that, you will be set up (haha) to learn the theory of sets and relations. That topic in turn is the foundation for discrete probability theory. And *that* topic is the topic you will need to understand *and reason about* machine learning systems.
