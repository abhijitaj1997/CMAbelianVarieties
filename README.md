# Formalising CM Abelian Varieties

## About the project

This project aims to define CM Abelian varieties with a goal to prove:
>If A is a CM abelian variety over an algebraically closed field of characteristic 0, then it (along with the CM structure) has a model over a number field.

Currently Mathlib does not have many results about Abelian varieties, beyond a proof that it is abelian (this can be found in [Mathlib's Abelian varieties](https://github.com/abhijitaj1997/mathlib4/blob/master/Mathlib/AlgebraicGeometry/Group/Abelian.lean)). In the process of defining CM Abelian varieties, this project also aims to complete the following goals (the list below will be updated with time):
1. Show torsion freeness of the Hom groups.
2. Define the Tate module of an ableian variety.
3. Show that the Hom groups are finitely generated.

## AI usage

The project will try and avoid producing entire definitions/proofs simply by asking an AI agent (if and when that is done, it will be clearly mentioned as a comment above the definition/proof). Claude code is being used as a glorified search engine to find results in Mathlib. It is also being used for book keeping, cleaning up code (for instance when certain definitions, lemma, etc. are renamed, or moved to a different file) and creating the desired notations.

# Collaboration

Please feel free to get in touch via Zulip if you would like to collaborate
