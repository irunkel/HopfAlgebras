import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace Hopf

-- mathlib docu says I should do this to use ⊗
open scoped TensorProduct

/- shortcuts for unitors -/

noncomputable def unitor_left
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  R ⊗[R] M →ₗ[R] M := TensorProduct.lid R M

noncomputable def unitor_left_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M →ₗ[R] R ⊗[R] M := LinearEquiv.symm (TensorProduct.lid R M)

noncomputable def unitor_right
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M ⊗[R] R →ₗ[R] M := TensorProduct.rid R M

noncomputable def unitor_right_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M →ₗ[R] M ⊗[R] R := LinearEquiv.symm (TensorProduct.rid R M)

class AlgebraTens (R:Type) (A:Type)
  [CommSemiring R] [AddCommMonoid A] [Module R A] where

  mul : A ⊗[R] A →ₗ[R] A
  unit : R →ₗ[R] A

  one_mul :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.rTensorHom A unit : R ⊗[R] A  →ₗ[R]  A ⊗[R] A)
    ∘ₗ (unitor_left_inv A :  A →ₗ[R] (R ⊗[R] A))
    =
    (LinearMap.id : A →ₗ[R] A)

  mul_one :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.lTensorHom A unit : A ⊗[R] R  →ₗ[R]  A ⊗[R] A)
    ∘ₗ (unitor_right_inv A :  A →ₗ[R] (A ⊗[R] R))
    =
    (LinearMap.id : A →ₗ[R] A)

  mul_assoc :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.rTensorHom A mul
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A))
    =
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.lTensorHom A mul
        : A ⊗[R] (A ⊗[R] A) →ₗ[R] (A ⊗[R] A))
    ∘ₗ (TensorProduct.assoc R A A A
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))


class CoalgebraTens (R:Type) (A:Type)
  [CommSemiring R] [AddCommMonoid A] [Module R A] where

  comul : A →ₗ[R] A ⊗[R] A
  counit : A →ₗ[R] R

  coone_comul :
    (unitor_left A : R ⊗[R] A →ₗ[R] A)
    ∘ₗ (LinearMap.rTensorHom A counit : A ⊗[R] A  →ₗ[R]  R ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (LinearMap.id : A →ₗ[R] A)

  comul_coone :
    (unitor_right A :  A ⊗[R] R →ₗ[R] A)
    ∘ₗ (LinearMap.lTensorHom A counit : A ⊗[R] A  →ₗ[R]  A ⊗[R] R)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (LinearMap.id : A →ₗ[R] A)

  comul_coassoc :
    (TensorProduct.assoc R A A A
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (LinearMap.rTensorHom A comul
        : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (LinearMap.lTensorHom A comul
        : A ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)


-- Why is that not in the library? Maybe I missed it?
noncomputable def tensor_hom {R:Type} {M1 M2 N1 N2:Type}
  [CommSemiring R]
  [AddCommMonoid M1]
  [AddCommMonoid M2]
  [AddCommMonoid N1]
  [AddCommMonoid N2]
  [Module R M1]
  [Module R M2]
  [Module R N1]
  [Module R N2]
  (f : M1 →ₗ[R] N1)
  (g : M2 →ₗ[R] N2)
  :
  M1 ⊗[R] M2 →ₗ[R] N1 ⊗[R] N2
  := (
    (LinearMap.lTensorHom N1 g : N1 ⊗[R] M2 →ₗ[R] N1 ⊗[R] N2)
    ∘ₗ
    (LinearMap.rTensorHom M2 f : M1 ⊗[R] M2 →ₗ[R] N1 ⊗[R] M2)
  )

/-
  Just "def mulAA" Produced a compiler error
  "compiler IR check failed at 'Hopf.mulAA._rarg',
   error: unknown declaration 'TensorProduct.addCommMonoid'"
  This is a known issue
  https://github.com/leanprover/lean4/issues/1785
  It just means that the definition has to be made non-computable
-/
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
  let ass2_id := (LinearMap.rTensorHom A ass2equiv :
    ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A
    );
  let ass2inv_id := (LinearMap.rTensorHom A (LinearEquiv.symm ass2equiv) :
    (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A
    );
  let swap := (TensorProduct.comm R A A :
    A ⊗[R] A →ₗ[R] A ⊗[R] A
    );
  let id_swap_id := (LinearMap.rTensorHom A (LinearMap.lTensorHom A swap) :
    (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A
    );
  let mulmul := (tensor_hom AlgebraTens.mul AlgebraTens.mul:
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

theorem mulAA_tmul {R:Type} {A:Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AlgebraTens R A] (a b c d : A) :
  mulAA ( (a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d) )
  =
  ( AlgebraTens.mul (a ⊗ₜ[R] c) ) ⊗ₜ[R] (AlgebraTens.mul (b ⊗ₜ[R] d) )
  := by
    simp [mulAA,tensor_hom]


class HopfAlgebraTens (R:Type) (A:Type)
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
extends AlgebraTens R A, CoalgebraTens R A where

  anti : A →ₗ[R] A

  -- comul is algebra hom
  comul_mul :
  ( mulAA : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( tensor_hom comul comul : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A) )
  =
  ( comul : A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( mul : A ⊗[R] A →ₗ[R] A)

  comul_unit :
  ( comul : A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( unit : R →ₗ[R] A )
  =
  ( (tensor_hom unit unit) : R ⊗[R] R →ₗ[R] A ⊗[R] A )
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
  ( (tensor_hom counit counit) : A ⊗[R] A →ₗ[R] R ⊗[R] R )

  counit_unit :
  ( counit : A →ₗ[R] R )
  ∘ₗ
  ( unit : R →ₗ[R] A )
  =
  ( LinearMap.id : R →ₗ[R] R )

  -- antipode axioms
  anti_left :
  ( mul : A ⊗[R] A →ₗ[R] A )
  ∘ₗ
  ( LinearMap.lTensorHom A anti : A ⊗[R] A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( comul : A →ₗ[R] A ⊗[R] A )
  =
  ( unit : R →ₗ[R] A )
  ∘ₗ
  ( counit : A →ₗ[R] R )

  anti_right :
  ( mul : A ⊗[R] A →ₗ[R] A )
  ∘ₗ
  ( LinearMap.rTensorHom A anti : A ⊗[R] A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( comul : A →ₗ[R] A ⊗[R] A )
  =
  ( unit : R →ₗ[R] A )
  ∘ₗ
  ( counit : A →ₗ[R] R )

end Hopf
