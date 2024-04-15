import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic -- tensor product of two algebras
import Mathlib.Algebra.Algebra.Hom
import HopfAlgebra.Basic

open BigOperators
open Finset
open LinearMap TensorProduct Hopf

namespace ExampleTensorAlgebra

variable {K:Type} [CommRing K] -- the antipode needs additive inverses
variable {V:Type} [AddCommMonoid V] [Module K V]

-- the check below works and shows that conversion from Algebra to AlgebraTens is recognised
-- #check inferInstanceAs (AlgebraTens K (TensorAlgebra K V))

-- the map v ↦ v ⊗ 1 + 1 ⊗ v
noncomputable def TA_comul_aux : V →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)
  :=
  let left : V →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)
    := (TensorProduct.map id AlgebraTens.unit : (TensorAlgebra K V) ⊗[K] K →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))
      ∘ₗ (unitor_right_inv (TensorAlgebra K V) : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] K)
      ∘ₗ (TensorAlgebra.ι K : V →ₗ[K] (TensorAlgebra K V))
  let right : V →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)
    := (TensorProduct.map AlgebraTens.unit id : K ⊗[K] (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))
      ∘ₗ (unitor_left_inv (TensorAlgebra K V) : (TensorAlgebra K V) →ₗ[K] K ⊗[K] (TensorAlgebra K V))
      ∘ₗ (TensorAlgebra.ι K : V →ₗ[K] (TensorAlgebra K V))
  left+right

noncomputable def TA_comul_alghom : (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)
  := TensorAlgebra.lift K (TA_comul_aux : V →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))

noncomputable def TA_comul : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)
  := AlgHom.toLinearMap TA_comul_alghom

def TA_counit_aux : V →ₗ[K] K := 0

noncomputable def TA_counit_alghom : (TensorAlgebra K V) →ₐ[K] K
  := TensorAlgebra.lift K (TA_counit_aux : V →ₗ[K] K)

noncomputable def TA_counit : (TensorAlgebra K V) →ₗ[K] K
  := AlgHom.toLinearMap TA_counit_alghom


noncomputable def unitor_left_alghom (R B : Type)
  [CommSemiring R] [Semiring B] [Algebra R B]
  :
  R ⊗[R] B →ₐ[R] B
  := (Algebra.TensorProduct.lid R B : R ⊗[R] B →ₐ[R] B)

theorem unitor_left_alghom_lin
  {R B : Type}
  [CommSemiring R] [Semiring B] [Algebra R B]
  :
  AlgHom.toLinearMap (unitor_left_alghom R B) = unitor_left B
  :=
  by
  simp [unitor_left_alghom,unitor_left]
  apply TensorProduct.ext'
  intro r b
  simp

/- QUESTION: Is this theorem already somewhere? I could not see
   it in Mathlib.RingTheory.TensorProduct.Basic -/
theorem AlgebraTensorLinearTensor
  {R A A' B B' : Type}
  [CommSemiring R]
  [Semiring A] [Algebra R A]
  [Semiring A'] [Algebra R A']
  [Semiring B] [Algebra R B]
  [Semiring B'] [Algebra R B']
  (f : A →ₐ[R] A')
  (g : B →ₐ[R] B')
  :
  AlgHom.toLinearMap (Algebra.TensorProduct.map f g)
  =
  TensorProduct.map (AlgHom.toLinearMap f) (AlgHom.toLinearMap g)
  :=
  by
  apply TensorProduct.ext'
  intro a b
  simp

theorem TA_coone_comul :
    (unitor_left (TensorAlgebra K V) : K ⊗[K] (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V))
    ∘ₗ (map TA_counit id : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)  →ₗ[K]  K ⊗[K] (TensorAlgebra K V))
    ∘ₗ (TA_comul : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))
    =
    (id : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V))
  := by

  let lhs_alghom :=
    AlgHom.comp
    (unitor_left_alghom K (TensorAlgebra K V) : K ⊗[K] (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V))
    (AlgHom.comp
      (Algebra.TensorProduct.map TA_counit_alghom (AlgHom.id K _) : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₐ[K]  K ⊗[K] (TensorAlgebra K V))
      (TA_comul_alghom : (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))
    )

  let rhs_alghom :=
    (AlgHom.id K (TensorAlgebra K V) : (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V))

  have : (AlgHom.toLinearMap lhs_alghom) ∘ₗ (TensorAlgebra.ι K)
          = (AlgHom.toLinearMap rhs_alghom) ∘ₗ (TensorAlgebra.ι K)
    := by
    apply LinearMap.ext
    intro v
    simp [lhs_alghom,rhs_alghom,
      TA_comul_alghom,TA_comul_aux]
    simp [AlgebraTens.unit,AlgebraTens.fromAlgebra.unit,AlgebraTens.fromAlgebra.βR]
    simp [TA_counit_alghom,TA_counit_aux]
    simp [unitor_left_alghom]

  have same_hom : lhs_alghom = rhs_alghom := TensorAlgebra.hom_ext this

  have lhs_lin :
        AlgHom.toLinearMap lhs_alghom
        = (unitor_left (TensorAlgebra K V)) ∘ₗ (map TA_counit id) ∘ₗ TA_comul
    := by
    simp [lhs_alghom]
    rw [unitor_left_alghom_lin]
    simp [TA_comul]
    rw [AlgebraTensorLinearTensor]
    simp [TA_counit]

  have rhs_lin :
        AlgHom.toLinearMap rhs_alghom
        = LinearMap.id
    := by
    simp [rhs_alghom]

  calc
    unitor_left (TensorAlgebra K V) ∘ₗ TensorProduct.map TA_counit LinearMap.id ∘ₗ TA_comul
      = AlgHom.toLinearMap lhs_alghom := by rw [← lhs_lin]
    _ = AlgHom.toLinearMap rhs_alghom := by rw [same_hom]
    _ = LinearMap.id := by rw [rhs_lin]


noncomputable instance : CoalgebraTens K (TensorAlgebra K V) where
  comul := TA_comul
  counit := TA_counit
  coone_comul := TA_coone_comul
  comul_coone := sorry
  comul_coassoc := sorry

noncomputable instance : BialgebraTens K (TensorAlgebra K V) where
  comul_mul := sorry
  comul_unit := sorry
  counit_mul := sorry
  counit_unit := sorry

noncomputable def TA_anti_aux : V →ₗ[K] TensorAlgebra K V
  := - TensorAlgebra.ι K

noncomputable def TA_anti_alghom : (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V)
  := TensorAlgebra.lift K (TA_anti_aux : V →ₗ[K] (TensorAlgebra K V))

noncomputable def TA_anti : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V)
  := AlgHom.toLinearMap TA_anti_alghom

noncomputable instance : HopfAlgebraTens K (TensorAlgebra K V) where
  anti := TA_anti
  hasAntipodeProp :=
  {
    left := by
      sorry
    right := by
      sorry
  }

end ExampleTensorAlgebra
