import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace Hopf

-- mathlib docu says I should do this to use ⊗
open scoped TensorProduct

/- --- Linear algebra helper definitions --- -/
section LinAlg

/- Alternate names for unitors and associators
   This should probably be avoided in favour of the
   library to a large extend  -/

noncomputable def unitor_left
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  R ⊗[R] M →ₗ[R] M := TensorProduct.lid R M

noncomputable def unitor_left_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M →ₗ[R] R ⊗[R] M := LinearEquiv.symm (TensorProduct.lid R M)

theorem unitor_left_inv_is_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  unitor_left_inv M ∘ₗ unitor_left M = (LinearMap.id : R ⊗[R] M →ₗ[R] R ⊗[R] M)
  := by
    simp [unitor_left_inv,unitor_left]

theorem unitor_left_inv_is_inv'
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  unitor_left M ∘ₗ unitor_left_inv M = (LinearMap.id : M →ₗ[R] M)
  := by
    simp [unitor_left_inv,unitor_left]

theorem unitor_left_nat
  {R:Type} {M N:Type}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (f : M →ₗ[R] N) :
  ( unitor_left N : R ⊗[R] N →ₗ[R] N )
  ∘ₗ ( TensorProduct.map LinearMap.id f : R ⊗[R] M →ₗ[R] R ⊗[R] N )
  =
  ( f : M →ₗ[R] N )
  ∘ₗ ( unitor_left M : R ⊗[R] M →ₗ[R] M )
  := by
    apply TensorProduct.ext'
    simp [unitor_left]

noncomputable def unitor_right
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M ⊗[R] R →ₗ[R] M := TensorProduct.rid R M

noncomputable def unitor_right_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M →ₗ[R] M ⊗[R] R := LinearEquiv.symm (TensorProduct.rid R M)

theorem unitor_right_inv_is_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  unitor_right_inv M ∘ₗ unitor_right M = (LinearMap.id : M ⊗[R] R →ₗ[R] M ⊗[R] R)
  := by
    simp [unitor_right_inv,unitor_right]

theorem unitor_right_inv_is_inv'
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  unitor_right M ∘ₗ unitor_right_inv M = (LinearMap.id : M →ₗ[R] M)
  := by
    simp [unitor_right_inv,unitor_right]

theorem unitor_right_nat
  {R:Type} {M N:Type}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (f : M →ₗ[R] N) :
  ( unitor_right N : N ⊗[R] R →ₗ[R] N )
  ∘ₗ ( TensorProduct.map f LinearMap.id : M ⊗[R] R →ₗ[R] N ⊗[R] R )
  =
  ( f : M →ₗ[R] N )
  ∘ₗ ( unitor_right M : M ⊗[R] R →ₗ[R] M )
  := by
    apply TensorProduct.ext'
    simp [unitor_right]

noncomputable def assoc {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C)
  := TensorProduct.assoc R A B C

noncomputable def assoc_inv {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C
  := LinearEquiv.symm (TensorProduct.assoc R A B C)

theorem assoc_inv_is_inv  {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  :
  (assoc_inv A B C : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C)
  ∘ₗ
  (assoc A B C : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C))
  =
  (LinearMap.id : (A ⊗[R] B) ⊗[R] C →ₗ[R] (A ⊗[R] B) ⊗[R] C)
  := by
    simp [assoc,assoc_inv]

theorem assoc_inv_is_inv'  {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  :
  (assoc A B C : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C))
  ∘ₗ
  (assoc_inv A B C : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C)
  =
  (LinearMap.id : A ⊗[R] (B ⊗[R] C) →ₗ[R] A ⊗[R] (B ⊗[R] C))
  := by
    simp [assoc,assoc_inv]
end LinAlg

/- --- Algebra definition --- -/
section AlgebraDef
/- This defines an associative unital algebra in terms of
   linear maps and tensor products (mathlib defines algebras
   as rings with a map of a commutative ring to the center
   instead).
   TODO: Is this maybe already in mathlib, too? -/

class AlgebraTens (R:Type) (A:Type)
  [CommSemiring R] [AddCommMonoid A] [Module R A] where

  mul : A ⊗[R] A →ₗ[R] A
  unit : R →ₗ[R] A

  one_mul :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.rTensor A unit : R ⊗[R] A  →ₗ[R]  A ⊗[R] A)
    ∘ₗ (unitor_left_inv A :  A →ₗ[R] (R ⊗[R] A))
    =
    (LinearMap.id : A →ₗ[R] A)

  mul_one :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.lTensor A unit : A ⊗[R] R  →ₗ[R]  A ⊗[R] A)
    ∘ₗ (unitor_right_inv A :  A →ₗ[R] (A ⊗[R] R))
    =
    (LinearMap.id : A →ₗ[R] A)

  mul_assoc :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.rTensor A mul
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A))
    =
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.lTensor A mul
        : A ⊗[R] (A ⊗[R] A) →ₗ[R] (A ⊗[R] A))
    ∘ₗ (TensorProduct.assoc R A A A
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))

end AlgebraDef

/- --- Coalgebra definition --- -/
section CoalgebraDef
/- This is basically the same as in mathlib -/

class CoalgebraTens (R:Type) (A:Type)
  [CommSemiring R] [AddCommMonoid A] [Module R A] where

  comul : A →ₗ[R] A ⊗[R] A
  counit : A →ₗ[R] R

  coone_comul :
    (unitor_left A : R ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.rTensor A counit : A ⊗[R] A  →ₗ[R]  R ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (LinearMap.id : A →ₗ[R] A)

  comul_coone :
    (unitor_right A :  A ⊗[R] R →ₗ[R] A)
    ∘ₗ (LinearMap.lTensor A counit : A ⊗[R] A  →ₗ[R]  A ⊗[R] R)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (LinearMap.id : A →ₗ[R] A)

  comul_coassoc :
    (TensorProduct.assoc R A A A
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (LinearMap.rTensor A comul
        : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (LinearMap.lTensor A comul
        : A ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)

end CoalgebraDef

section BialgebraDef
/-
  Just "def mulAA" Produced a compiler error
  "compiler IR check failed at 'Hopf.mulAA._rarg',
   error: unknown declaration 'TensorProduct.addCommMonoid'"
  This is a known issue
  https://github.com/leanprover/lean4/issues/1785
  It just means that the definition has to be made noncomputable
-/
-- product on A ⊗ A
noncomputable def mulAA {R:Type} {A:Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AlgebraTens R A] :
  (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A
  := (

  -- all the individual maps entering the product on A ⊗ A
  let ass1equiv := TensorProduct.assoc R (A ⊗[R] A) A A
  let ass1 := (ass1equiv :
    ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A)
    )
  let ass1inv := (LinearEquiv.symm ass1equiv :
    (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A
    )
  let ass2equiv := TensorProduct.assoc R A A A
  let ass2_id := (LinearMap.rTensor A ass2equiv :
    ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A
    );
  let ass2inv_id := (LinearMap.rTensor A (LinearEquiv.symm ass2equiv) :
    (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A
    );
  let swap := (TensorProduct.comm R A A :
    A ⊗[R] A →ₗ[R] A ⊗[R] A
    );
  let id_swap_id := (LinearMap.rTensor A (LinearMap.lTensor A swap) :
    (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A
    );
  let mulmul := (TensorProduct.map AlgebraTens.mul AlgebraTens.mul:
    (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A
    )

  -- the product on A ⊗ A
  (mulmul : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A)
  ∘ₗ
  (ass1 : ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A))
  ∘ₗ
  (ass2inv_id : (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A)
  ∘ₗ
  (id_swap_id : (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A)
  ∘ₗ
  (ass2_id : ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A)
  ∘ₗ
  (ass1inv : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A)

  )

-- mulAA on pure tensors : (a ⊗ b) * (c ⊗ d) = (a*c) ⊗ (b*d)
theorem mulAA_tmul {R:Type} {A:Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AlgebraTens R A] (a b c d : A) :
  mulAA ( (a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d) )
  =
  ( AlgebraTens.mul (a ⊗ₜ[R] c) ) ⊗ₜ[R] (AlgebraTens.mul (b ⊗ₜ[R] d) )
  := by simp [mulAA]

/- --- Bi- and Hopf algebra definition --- -/

class BialgebraTens (R:Type) (A:Type)
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
extends AlgebraTens R A, CoalgebraTens R A where

  -- comul is algebra hom
  comul_mul :
  ( mulAA : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( TensorProduct.map comul comul : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A) )
  =
  ( comul : A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( mul : A ⊗[R] A →ₗ[R] A)

  comul_unit :
  ( comul : A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( unit : R →ₗ[R] A )
  =
  ( (TensorProduct.map unit unit) : R ⊗[R] R →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( unitor_left_inv R : R →ₗ[R] R⊗[R] R )

  -- counit is algebra hom
  counit_mul :
  ( counit : A →ₗ[R] R )
  ∘ₗ
  ( mul : A ⊗[R] A →ₗ[R] A)
  =
  ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ
  ( (TensorProduct.map counit counit) : A ⊗[R] A →ₗ[R] R ⊗[R] R )

  counit_unit :
  ( counit : A →ₗ[R] R )
  ∘ₗ
  ( unit : R →ₗ[R] A )
  =
  ( LinearMap.id : R →ₗ[R] R )

end BialgebraDef

section HopfalgebraDef

open AlgebraTens CoalgebraTens BialgebraTens

structure AntipodeProp {R:Type} {A:Type}
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
  [BialgebraTens R A]
  (anti : A →ₗ[R] A) where

  left : -- Δ ∘ (id ⊗ S) ∘ μ
  ( mul : A ⊗[R] A →ₗ[R] A )
  ∘ₗ
  ( LinearMap.lTensor A anti : A ⊗[R] A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( comul : A →ₗ[R] A ⊗[R] A )
  =
  ( unit : R →ₗ[R] A )
  ∘ₗ
  ( counit : A →ₗ[R] R )

  right : -- Δ ∘ (S ⊗ id) ∘ μ
  ( mul : A ⊗[R] A →ₗ[R] A )
  ∘ₗ
  ( LinearMap.rTensor A anti : A ⊗[R] A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( comul : A →ₗ[R] A ⊗[R] A )
  =
  ( unit : R →ₗ[R] A )
  ∘ₗ
  ( counit : A →ₗ[R] R )

class HopfAlgebraTens (R:Type) (A:Type)
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
extends BialgebraTens R A where
  anti : A →ₗ[R] A
  hasAntipodeProp : AntipodeProp anti

end HopfalgebraDef

end Hopf
