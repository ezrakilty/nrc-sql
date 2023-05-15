
# This Proof

This is a Coq proof of the Lindley-Stark result that shows strong normalization
of Moggi's computational metalanguage with rewrite rules such a beta-reduction for lambda-applications and for a bind (let) form with a "pure" subject term.

## Caveats

The formalization uses de Bruijn indices, widely known as a poor
representation, but it was the only binder-encoding that I fully understood
when I first started this project. I'd like to see if anything is made
significantly simpler by switching to a locally-nameless representation.
