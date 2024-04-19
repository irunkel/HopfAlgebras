import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic -- tensor product of two algebras
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Equiv
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

noncomputable def unitor_right_alghom (R B : Type)
  [CommSemiring R] [Semiring B] [Algebra R B]
  :
  B ⊗[R] R →ₐ[R] B
  := (Algebra.TensorProduct.rid R R B : B ⊗[R] R →ₐ[R] B)

theorem unitor_right_alghom_lin
  {R B : Type}
  [CommSemiring R] [Semiring B] [Algebra R B]
  :
  AlgHom.toLinearMap (unitor_right_alghom R B) = unitor_right B
  :=
  by
  simp [unitor_right_alghom,unitor_left]
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

  -- QUESTION: Why is there no ∘ₐ? Or am I missing something?
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


theorem TA_comul_coone :
    (unitor_right (TensorAlgebra K V) :  (TensorAlgebra K V) ⊗[K] K →ₗ[K] (TensorAlgebra K V))
    ∘ₗ (map id TA_counit : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)  →ₗ[K]  (TensorAlgebra K V) ⊗[K] K)
    ∘ₗ (TA_comul : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))
    =
    (id : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V))
  := by
  let lhs_alghom :=
    AlgHom.comp
    (unitor_right_alghom K (TensorAlgebra K V) : (TensorAlgebra K V) ⊗[K] K →ₐ[K] (TensorAlgebra K V))
    (AlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id K _) TA_counit_alghom : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V) ⊗[K] K)
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
    simp [unitor_right_alghom]

  have same_hom : lhs_alghom = rhs_alghom := TensorAlgebra.hom_ext this

  have lhs_lin :
        AlgHom.toLinearMap lhs_alghom
        = (unitor_right (TensorAlgebra K V)) ∘ₗ (map id TA_counit) ∘ₗ TA_comul
    := by
    simp [lhs_alghom]
    rw [unitor_right_alghom_lin]
    simp [TA_comul]
    rw [AlgebraTensorLinearTensor]
    simp [TA_counit]

  have rhs_lin :
        AlgHom.toLinearMap rhs_alghom
        = LinearMap.id
    := by
    simp [rhs_alghom]

  calc
    unitor_right (TensorAlgebra K V) ∘ₗ TensorProduct.map LinearMap.id TA_counit ∘ₗ TA_comul
      = AlgHom.toLinearMap lhs_alghom := by rw [← lhs_lin]
    _ = AlgHom.toLinearMap rhs_alghom := by rw [same_hom]
    _ = LinearMap.id := by rw [rhs_lin]


theorem TA_comul_coassoc :
    (assoc (TensorAlgebra K V) (TensorAlgebra K V) (TensorAlgebra K V)
        : ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)) ⊗[K] (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)))
    ∘ₗ (map TA_comul id
        : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₗ[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)) ⊗[K] (TensorAlgebra K V))
    ∘ₗ (TA_comul : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))
    =
    (map id TA_comul
        : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)))
    ∘ₗ (TA_comul : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))
  := by

  let lhs_alghom :=
    AlgHom.comp
    (Algebra.TensorProduct.assoc K (TensorAlgebra K V) (TensorAlgebra K V) (TensorAlgebra K V)
        : ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)) ⊗[K] (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V) ⊗[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)))
    (AlgHom.comp
      (Algebra.TensorProduct.map TA_comul_alghom (AlgHom.id K (TensorAlgebra K V))
        : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₐ[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)) ⊗[K] (TensorAlgebra K V))
      (TA_comul_alghom : (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))
    )

  let rhs_alghom :=
    AlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id K (TensorAlgebra K V)) TA_comul_alghom
        : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V) ⊗[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)))
    (TA_comul_alghom : (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V))

  have : (AlgHom.toLinearMap lhs_alghom) ∘ₗ (TensorAlgebra.ι K)
          = (AlgHom.toLinearMap rhs_alghom) ∘ₗ (TensorAlgebra.ι K)
    := by
    apply LinearMap.ext
    intro v
    simp [lhs_alghom,rhs_alghom,
      TA_comul_alghom,TA_comul_aux]
    simp [AlgebraTens.unit,AlgebraTens.fromAlgebra.unit,AlgebraTens.fromAlgebra.βR]
    rw [TensorProduct.add_tmul]
    rw [TensorProduct.tmul_add]
    rw [Algebra.TensorProduct.one_def]
    simp
    rw [add_assoc]

  have same_hom : lhs_alghom = rhs_alghom := TensorAlgebra.hom_ext this

  have same_assoc :
    AlgEquiv.toLinearMap (Algebra.TensorProduct.assoc K (TensorAlgebra K V) (TensorAlgebra K V) (TensorAlgebra K V))
    = assoc (TensorAlgebra K V) (TensorAlgebra K V) (TensorAlgebra K V)
    := by
    apply TensorProduct.ext_threefold
    simp

  have lhs_lin :
        AlgHom.toLinearMap lhs_alghom
        = (assoc (TensorAlgebra K V) (TensorAlgebra K V) (TensorAlgebra K V))
          ∘ₗ (map TA_comul id) ∘ₗ TA_comul
    := by
    simp [lhs_alghom]
    simp [TA_comul]
    rw [AlgebraTensorLinearTensor]
    rw [same_assoc]
    exact rfl

  have rhs_lin :
        AlgHom.toLinearMap rhs_alghom
        = (map id TA_comul) ∘ₗ TA_comul
    := by
    simp [rhs_alghom]
    simp [TA_comul]
    rw [AlgebraTensorLinearTensor]
    simp

  calc
    (assoc (TensorAlgebra K V) (TensorAlgebra K V) (TensorAlgebra K V))
    ∘ₗ (map TA_comul id) ∘ₗ TA_comul
      = AlgHom.toLinearMap lhs_alghom := by rw [lhs_lin]
    _ = AlgHom.toLinearMap rhs_alghom := by rw [same_hom]
    _ = (map id TA_comul) ∘ₗ TA_comul := by rw [rhs_lin]


noncomputable instance : CoalgebraTens K (TensorAlgebra K V) where
  comul := TA_comul
  counit := TA_counit
  coone_comul := TA_coone_comul
  comul_coone := TA_comul_coone
  comul_coassoc := TA_comul_coassoc

theorem TA_comul_mul :
  ( mulAA : ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)) ⊗[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) )
  ∘ₗ
  ( map CoalgebraTens.comul CoalgebraTens.comul : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₗ[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)) ⊗[K] ((TensorAlgebra K V) ⊗[K] (TensorAlgebra K V)) )
  =
  ( CoalgebraTens.comul : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) )
  ∘ₗ
  ( AlgebraTens.mul : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V))
  := by
  rw [fromAlgebra.mulAA_alg]
  apply TensorProduct.ext'
  intro a b
  simp [AlgebraTens.mul,
    AlgebraTens.fromAlgebra.mul,
    AlgebraTens.fromAlgebra.bilin,
    AlgebraTens.fromAlgebra.bilin_aux]
  simp [CoalgebraTens.comul]
  simp [TA_comul]

theorem TA_comul_unit :
  ( CoalgebraTens.comul : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) )
  ∘ₗ
  ( AlgebraTens.unit : K →ₗ[K] (TensorAlgebra K V) )
  =
  ( (map AlgebraTens.unit AlgebraTens.unit) : K ⊗[K] K →ₗ[K] (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) )
  ∘ₗ
  ( unitor_left_inv K : K →ₗ[K] K⊗[K] K )
  := by
  ext
  dsimp [CoalgebraTens.comul,AlgebraTens.unit]
  simp [AlgebraTens.fromAlgebra.unit,AlgebraTens.fromAlgebra.βR]
  simp [TA_comul]
  rw [Algebra.TensorProduct.one_def]

theorem TA_counit_mul :
  ( CoalgebraTens.counit : (TensorAlgebra K V) →ₗ[K] K )
  ∘ₗ
  ( AlgebraTens.mul : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V))
  =
  ( unitor_left K : K ⊗[K] K →ₗ[K] K )
  ∘ₗ
  ( (map CoalgebraTens.counit CoalgebraTens.counit) : (TensorAlgebra K V) ⊗[K] (TensorAlgebra K V) →ₗ[K] K ⊗[K] K )
  := by
  apply TensorProduct.ext'
  intro x y
  simp [CoalgebraTens.counit, TA_counit]
  dsimp [AlgebraTens.mul,AlgebraTens.fromAlgebra.mul,
    AlgebraTens.fromAlgebra.bilin,AlgebraTens.fromAlgebra.bilin_aux]
  simp

theorem TA_counit_unit :
  ( CoalgebraTens.counit : (TensorAlgebra K V) →ₗ[K] K )
  ∘ₗ
  ( AlgebraTens.unit : K →ₗ[K] (TensorAlgebra K V) )
  =
  ( id : K →ₗ[K] K )
  := by
  ext
  simp [AlgebraTens.unit,AlgebraTens.fromAlgebra.unit,
    AlgebraTens.fromAlgebra.βR]
  simp [CoalgebraTens.counit,TA_counit,
    TA_counit_alghom,TA_counit_aux]

noncomputable instance : BialgebraTens K (TensorAlgebra K V) where
  comul_mul := TA_comul_mul
  comul_unit := TA_comul_unit
  counit_mul := TA_counit_mul
  counit_unit := TA_counit_unit

/- TODO: B and B^mop are the same as a K-module, but I am not
   sure how to make Lean see that at the moment. Ideally there
   would be a way without AlgMopId (which I also still need to
   think about how to define).
   For the proof it might be good to first implement Prop 8 on
   p.16 of
   Klimyk,Schmudgen, Quantum groups and their representations
    (Springer 1997)
-/
noncomputable def AlgMopId
  (R B : Type)
  [CommSemiring R] [Semiring B] [Algebra R B]
  :
  B ≃ₗ[R] Bᵐᵒᵖ
  := sorry

noncomputable def TA_anti_aux : V →ₗ[K] (TensorAlgebra K V)ᵐᵒᵖ
  := (AlgMopId K (TensorAlgebra K V) : TensorAlgebra K V →ₗ[K] (TensorAlgebra K V)ᵐᵒᵖ )∘ₗ (- TensorAlgebra.ι K)

noncomputable def TA_anti_alghom : (TensorAlgebra K V) →ₐ[K] (TensorAlgebra K V)ᵐᵒᵖ
  := TensorAlgebra.lift K (TA_anti_aux : V →ₗ[K] (TensorAlgebra K V)ᵐᵒᵖ)

noncomputable def TA_anti : (TensorAlgebra K V) →ₗ[K] (TensorAlgebra K V)
  := ( (AlgMopId K (TensorAlgebra K V)).symm : (TensorAlgebra K V)ᵐᵒᵖ →ₗ[K] TensorAlgebra K V )
     ∘ₗ (AlgHom.toLinearMap TA_anti_alghom)

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
