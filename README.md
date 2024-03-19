# HopfAlgebras
An attempt to implement some aspects of Hopf algebras in Lean4, including examples. It uses linear algebra routines from Mathlib, but not the inbuild Hopf algebra libraries. One reason for this is that this is a learning project, and another reason is that I wanted to define algebras symmetrically to coalgebras as linear maps A ⊗ A → A. 

## Basic.lean

Implements the definition of a Hopf algebra. It starts with some linear algebra helper functions (which are probably superfluous), and provides the classes:
- <code>AlgebraTens R A</code>: Associative unital algebra on A over a commutative (semi-)ring R.
- <code>CoalgebraTens R A</code>: Dito for coalgebras.
- <code>HopfAlgebraTens R A</code>: Combines the previous two and adds the antipode.

## ExampleSweedler.lean

<code>sha {K}</code>: Sweedler's four-dimensional Hopf algebra over a commutative ring <code>K</code>. So far contains the proof that it indeed defines a Hopf algebra, i.e. it provides <code>noncomputable instance : HopfAlgebraTens K (@sha K)</code>.

TODOs: implement examples alongside general theory: (co)integrals, R-matrices,... Distant future: Show that representations of Sweedler's Hopf algebra in Vect are the same as those of the symmetric algebra of a two-dimensional purely odd super-vector space in SVect.

## ExampleHopfFromGroup.lean

For a finite group <code>G</code>, the function algebra and the group algebra are Hopf algebras. WORK IN PROGRESS.

<code>Fun {G} {K}</code>: The Hopf algebra of functions G → K. The group structure enters the definition of the coproduct, but not that of the product.

<code>Alg {K} {G}</code>: The group algebra for G over K. The group structure enters the definition of the product but not that of the coproduct.

TODOs: show that these two are Hopf algebras, hopefully will be able to show that these are dual to each other.

### TODOs
Many...