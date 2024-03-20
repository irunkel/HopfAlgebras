# HopfAlgebras
An attempt to implement some aspects of Hopf algebras in Lean4, including examples. It uses linear algebra routines from Mathlib, but not the inbuild Hopf algebra libraries. One reason for this is that this is a learning project, and another reason is that I wanted to define algebras symmetrically to coalgebras as linear maps A ⊗ A → A. 

## Basic.lean

Implements the definition of a Hopf algebra. It starts with some linear algebra helper functions (which are probably superfluous), and provides the classes:
- <code>AlgebraTens R A</code>: Associative unital algebra on `A` over a commutative (semi-)ring `R`.
- <code>CoalgebraTens R A</code>: Dito for coalgebras.
- <code>HopfAlgebraTens R A</code>: Combines the previous two and adds the antipode.

## ExampleSweedler.lean

`sha {K}`: Sweedler's four-dimensional Hopf algebra over a commutative ring `K`. So far contains the proof that it indeed defines a Hopf algebra, i.e. it provides <code>noncomputable instance : HopfAlgebraTens K (@sha K)</code>.

TODOs: implement examples alongside general theory: (co)integrals, R-matrices,... Distant future: Show that representations of Sweedler's Hopf algebra in Vect are the same as those of the symmetric algebra of a two-dimensional purely odd super-vector space in SVect.

## ExampleFunctionAlgebra.lean

`Fun {G} {K}`: The Hopf algebra of functions `G → K`. 
Here `G` is a finite group, `K` is a commutative Ring, and the group structure enters the definition of the coproduct, but not that of the product. The file provides <code>noncomputable instance : HopfAlgebraTens K (@Fun G K)</code>.

There is also an explict example for the group `C2` of two elements, written multiplicatively. (I tried to make this work via `Multiplicative (Fin 2)`, but failed, so now there is a multiplicative `C2` defines from scratch.)

## ExampleGroupAlgebra.lean

`Alg {K} {G}`: The group algebra for a finite group `G` over a commutative ring `K` is a Hopf algebra. The group structure enters the definition of the product but not that of the coproduct. Provides <code>noncomputable instance : HopfAlgebraTens K (@Alg K G)</code>.

TODOs: try to show that `Fun {G} {K}` and `Alg {K} {G}` are dual to each other, ...

## Future plans

Try to implement more bits and pieces of Hopf algebras. E.g. the following would be nice: 
- convolution and uniqueness of antipode
- the dual is a Hopf algebra
- Hopf modules and existence and uniqueness of (co)integrals
- various versions of Uq(sl2)
- R-matrices and braided monoidal structure on representation category
- ...