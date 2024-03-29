# HopfAlgebras
An attempt to implement some aspects of Hopf algebras in Lean4, including examples. It uses linear algebra routines from Mathlib, but not the inbuild Hopf algebra libraries. One reason for this is that this is a learning project, and another reason is that I wanted to define algebras symmetrically to coalgebras as linear maps A ⊗ A → A.

## Basic.lean

Implements the definition of a Hopf algebra. It starts with some linear algebra helper functions (which are probably superfluous), and provides the classes:
- `AlgebraTens R A`: Associative unital algebra on `A` over a commutative (semi-)ring `R`.
- `CoalgebraTens R A`: Dito for coalgebras.
- `BialgebraTens R A`: Combines the previous two and adds the conditions that coproduct and counit are algebra homomorphisms.
- `HopfAlgebraTens R A`: Adds the antipode map to a bialgebra, together with its two conditions.

## ExampleSweedler.lean

`sha {K}`: Sweedler's four-dimensional Hopf algebra over a commutative ring `K`. So far contains the proof that it indeed defines a Hopf algebra, i.e. it provides <code>noncomputable instance : HopfAlgebraTens K (@sha K)</code>.

TODOs: make the proofs less inelegant, implement examples alongside general theory: (co)integrals, R-matrices,... Distant future: Show that representations of Sweedler's Hopf algebra in Vect are the same as those of the symmetric algebra of a two-dimensional purely odd super-vector space in SVect.

## ExampleFunctionAlgebra.lean

`Fun {G} {K}`: The Hopf algebra of functions `G → K`. 
Here `G` is a finite group, `K` is a commutative Ring, and the group structure enters the definition of the coproduct, but not that of the product. The file provides <code>noncomputable instance : HopfAlgebraTens K (@Fun G K)</code>.

There is also an explict example for the group `C2` of two elements, written multiplicatively. (I tried to make this work via `Multiplicative (Fin 2)`, but failed, so now there is a multiplicative `C2` defines from scratch.)

TODOs: This example seems much more cumbersome than the group algebra one below, try to improve the proofs.

## ExampleGroupAlgebra.lean

`Alg {K} {G}`: The group algebra for a finite group `G` over a commutative ring `K` is a Hopf algebra. The group structure enters the definition of the product but not that of the coproduct. Provides <code>noncomputable instance : HopfAlgebraTens K (@Alg K G)</code>.

TODOs: try to show that `Fun {G} {K}` and `Alg {K} {G}` are dual to each other, ...

## Convolution.lean

Let `H` be a Hopf algebra over a commutative (semi)ring `R`.

`convAlg`: The convolution algebra obtained form `H`. The file provides <code>noncomputable instance : AlgebraTens R (@convAlg R _ H _ _)</code>. (I would like to write `convAlg` instead of `(@convAlg R _ H _ _)` but I do not know how.)

`AntipodeUnique`: The theorem that the antipode of `H` is unique. The proof is that the antipode is the inverse to the identity in the convolution algebra, and hence unique.

## AntipodeAntihom.lean

The antipode is an algebra and coalgebra antihomomorphism. 

**Work in progress - on hold until a better method is found**

*Status:* I wanted to do this by translating a string diagram computation with the perspective of having this work the same way in braided categories. However, this has hit a bit of a roadblock. 
For the unit and counit there are the theorems `Antipode_unit` and `Antipode_counit` whose proofs are terribly long calc chains which just shuffle coherence isos around. This is somewhat terrifying as the usual book proof is half a line ("This easily follows from ...").

For `Antipode_mul` I have tried to map out the calculation by string diagrams on paper, and I can see that this will work in principle, but it will be *long*. 
For `Antipode_comul` on can then just flip diagrams, but that will not make it shorter.

TODOs: Find a more efficient way to do this. Maybe the `coherence` tactic in the category theory framework can be used  in some way?

## HopfPairing.lean

A pairing between two bialgebras `A` and `B`, which is compatible with (co)unit and (co)product. For a pairing `ω : A ⊗ B → R`, these compatibility conditions are bundled in `structure Pairing`.

`PairingAntipode`: The statement that a pairing of bialgebras automatically preserves the antipode of a Hopf algebra

TODOs: Very tedious proof by coherence shuffling, more efficient method to translate string diagram equalities would make it shorter. (See `HopfPairing - Pairing preserves antipode (string diagrams).pdf` for the string diagram calculation.) Further results one could try to add:
- Show duality of the function algebra and the group algebra as an example.
- For a non-degenerate pairing `ω : A ⊗ B → R` and `A` already a Hopf algebra, the adjoint morphisms turn `B` into a Hopf algebra.
- Use this to define the dual of a Hopf algebra.

## Further things to try

Try to implement more bits and pieces of Hopf algebras. E.g. the following would be nice: 
- Hopf modules and existence and uniqueness of (co)integrals
- various versions of Uq(sl2)
- R-matrices and braided monoidal structure on representation category
- rewrite everything as Hopf algebras in braided monoidal categories 
- ...