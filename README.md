
# This Proof

This is a Coq proof development that strives to show that Nested
Relational Calculus expressions with flat input and output types can
be converted to SQL.

It is a work in progress: At the moment most of the heavy-lifting is
done, but there are a few things left to implement:

* Conditionals in the source language.
* The final translation of normalized NRC expressions into SQL.
* A necessary rewrite rule is missing, and implementing it looks to
  require a lot of work.

And there is much to be desired in the cleanliness of of the
development:

* Naming is fairly inconsistent,
* Some proofs are long, convoluted and not transparent,
* Some things are redundantly defined.

The development is&mdash;after a fashion&mdash;a model of how to do a proof of
this kind in Coq. It is not entirely a *great* example, but it is an
example of what might be done by a relatively unsophisticated student
of machine proof.

## Caveats

The formalization uses de Bruijn indices, widely known as a poor
representation, but it was the only binder-encoding that I fully understood
when I first started this project. I'd like to see if anything is made
significantly simpler by switching to a locally-nameless representation.
