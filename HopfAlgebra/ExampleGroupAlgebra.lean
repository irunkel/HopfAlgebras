import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HopfAlgebra.Basic

open BigOperators
open Finset
open scoped TensorProduct
open Hopf

-- This is in Mathlib as "MonoidAlgebra"
namespace GroupAlgebra

variable {K : Type} [CommRing K]
variable {G : Type} [Group G] [Finite G] [DecidableEq G]
noncomputable instance : Fintype G := Fintype.ofFinite G

abbrev Alg := G → K

noncomputable def β : Basis G K (@Alg K G)
  := Pi.basisFun K G

noncomputable def ββ : Basis (Prod G G) K ((@Alg K G) ⊗[K] (@Alg K G))
  := Basis.tensorProduct β β

noncomputable def βK : Basis (Fin 1) K K
  := Basis.singleton (Fin 1) K

noncomputable def βββ : Basis ((G × G) × G) K
  (((@Alg K G) ⊗[K] (@Alg K G)) ⊗[K] (@Alg K G))
  := Basis.tensorProduct ββ β

/- --- Algebra structure on function algebra --- -/

noncomputable def Alg_mul_on_basis : G × G → (@Alg K G) :=
  fun (a,b) ↦ β (a*b)

noncomputable def Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) :=
  Basis.constr ββ K Alg_mul_on_basis

noncomputable def Alg_unit : K →ₗ[K] (@Alg K G) :=
  Basis.constr βK K (fun (_: Fin 1) ↦ β (1:G))

theorem Alg_mul_ββ_lemma  {g h : G} : Alg_mul ((β g) ⊗ₜ[K] (β h)) = Alg_mul_on_basis (g,h)
  := by
    rw [Alg_mul]
    rw [← Basis.tensorProduct_apply, ← ββ]
    simp

theorem Alg_unit_1_lemma : Alg_unit (1:K) = (β (1:G) : @Alg K G)
  := by simp [Alg_unit,βK]

theorem Alg_unit_βK_lemma (i:Fin 1) : Alg_unit (βK i) = (β (1:G) : @Alg K G)
  := by simp [Alg_unit,βK]

theorem Alg_one_mul :
  ( Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G))
  ∘ₗ (LinearMap.rTensor Alg Alg_unit : K ⊗[K] (@Alg K G)  →ₗ[K]  (@Alg K G) ⊗[K] (@Alg K G))
  ∘ₗ (unitor_left_inv Alg : (@Alg K G) →ₗ[K] (K ⊗[K] (@Alg K G)))
  =
  (LinearMap.id : (@Alg K G) →ₗ[K] (@Alg K G))
  := by
    apply Basis.ext β
    intro g
    simp [unitor_left_inv,Alg_unit_1_lemma]
    simp [Alg_mul_ββ_lemma, Alg_mul_on_basis]

theorem Alg_mul_one :
  ( Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G))
  ∘ₗ (LinearMap.lTensor Alg Alg_unit : (@Alg K G) ⊗[K] K  →ₗ[K]  (@Alg K G) ⊗[K] (@Alg K G))
  ∘ₗ (unitor_right_inv Alg :  (@Alg K G) →ₗ[K] ((@Alg K G) ⊗[K] K))
  =
  (LinearMap.id : (@Alg K G) →ₗ[K] (@Alg K G))
  := by
    apply Basis.ext β
    intro g
    simp [unitor_right_inv,Alg_unit_1_lemma]
    simp [Alg_mul_ββ_lemma, Alg_mul_on_basis]

theorem Alg_mul_assoc :
  ( Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G))
  ∘ₗ (LinearMap.rTensor Alg Alg_mul
      : ((@Alg K G) ⊗[K] (@Alg K G)) ⊗[K] (@Alg K G) →ₗ[K] ((@Alg K G) ⊗[K] (@Alg K G)))
  =
  ( Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G))
  ∘ₗ (LinearMap.lTensor Alg Alg_mul
      : (@Alg K G) ⊗[K] ((@Alg K G) ⊗[K] (@Alg K G)) →ₗ[K] ((@Alg K G) ⊗[K] (@Alg K G)))
  ∘ₗ (TensorProduct.assoc K (@Alg K G) (@Alg K G) (@Alg K G)
      : ((@Alg K G) ⊗[K] (@Alg K G)) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] ((@Alg K G) ⊗[K] (@Alg K G)))
  := by
    apply Basis.ext βββ
    intro ((g,h),k)
    simp [βββ,ββ]
    simp [Alg_mul_ββ_lemma, Alg_mul_on_basis]
    rw [mul_assoc]

noncomputable instance : AlgebraTens K (@Alg K G) where
  mul := Alg_mul
  unit := Alg_unit
  one_mul := Alg_one_mul
  mul_one := Alg_mul_one
  mul_assoc := Alg_mul_assoc

/- --- Coalgebra structure on function algebra --- -/

noncomputable def Alg_comul_on_basis : G → (@Alg K G) ⊗[K] (@Alg K G)
  := fun g ↦ β g ⊗ₜ[K] β g

noncomputable def Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) :=
  Basis.constr β K Alg_comul_on_basis

noncomputable def Alg_counit_on_basis : G → K := fun _ ↦ 1

noncomputable def Alg_counit : (@Alg K G) →ₗ[K] K :=
  Basis.constr β K Alg_counit_on_basis

theorem Alg_coone_comul :
  (unitor_left Alg : K ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G))
  ∘ₗ (LinearMap.rTensor Alg Alg_counit : (@Alg K G) ⊗[K] (@Alg K G)  →ₗ[K]  K ⊗[K] (@Alg K G))
  ∘ₗ ( Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G))
  =
  (LinearMap.id : (@Alg K G) →ₗ[K] (@Alg K G))
  := by
    apply Basis.ext β
    intro g
    simp [unitor_left,
      Alg_comul,Alg_comul_on_basis]
    simp [Alg_counit,Alg_counit_on_basis]

theorem Alg_comul_coone :
  (unitor_right Alg :  (@Alg K G) ⊗[K] K →ₗ[K] (@Alg K G))
  ∘ₗ (LinearMap.lTensor Alg Alg_counit : (@Alg K G) ⊗[K] (@Alg K G)  →ₗ[K]  (@Alg K G) ⊗[K] K)
  ∘ₗ ( Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G))
  =
  (LinearMap.id : (@Alg K G) →ₗ[K] (@Alg K G))
  := by
    apply Basis.ext β
    intro g
    simp [unitor_right,
      Alg_comul,Alg_comul_on_basis]
    simp [Alg_counit,Alg_counit_on_basis]

theorem Alg_comul_coassoc :
  (TensorProduct.assoc K (@Alg K G) (@Alg K G) (@Alg K G)
      : ((@Alg K G) ⊗[K] (@Alg K G)) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] ((@Alg K G) ⊗[K] (@Alg K G)))
  ∘ₗ (LinearMap.rTensor Alg Alg_comul
      : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] ((@Alg K G) ⊗[K] (@Alg K G)) ⊗[K] (@Alg K G))
  ∘ₗ ( Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G))
  =
  (LinearMap.lTensor Alg Alg_comul
      : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] ((@Alg K G) ⊗[K] (@Alg K G)))
  ∘ₗ ( Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G))
  := by
    apply Basis.ext β
    intro g
    simp [Alg_comul,Alg_comul_on_basis]

noncomputable instance : CoalgebraTens K (@Alg K G) where
  comul := Alg_comul
  counit := Alg_counit
  coone_comul := Alg_coone_comul
  comul_coone := Alg_comul_coone
  comul_coassoc := Alg_comul_coassoc


/- --- Hopf algebra structure on function algebra --- -/

noncomputable def Alg_anti_on_basis : G → (@Alg K G)
  := fun g ↦ β g⁻¹

noncomputable def Alg_anti : (@Alg K G) →ₗ[K] (@Alg K G) :=
  Basis.constr β K Alg_anti_on_basis

theorem Alg_comul_mul :
  ( mulAA : ((@Alg K G) ⊗[K] (@Alg K G)) ⊗[K] ((@Alg K G) ⊗[K] (@Alg K G)) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) )
  ∘ₗ
  ( TensorProduct.map Alg_comul Alg_comul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] ((@Alg K G) ⊗[K] (@Alg K G)) ⊗[K] ((@Alg K G) ⊗[K] (@Alg K G)) )
  =
  ( Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) )
  ∘ₗ
  ( Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G))
  := by
    apply Basis.ext ββ
    intro (g,h)
    simp [ββ,
      Alg_mul_ββ_lemma,Alg_mul_on_basis]
    simp [Alg_comul,Alg_comul_on_basis]
    simp [mulAA_tmul,AlgebraTens.mul]
    simp [Alg_mul_ββ_lemma,Alg_mul_on_basis]

theorem Alg_comul_unit :
  ( Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) )
  ∘ₗ
  ( Alg_unit : K →ₗ[K] (@Alg K G) )
  =
  ( (TensorProduct.map Alg_unit Alg_unit) : K ⊗[K] K →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) )
  ∘ₗ
  ( unitor_left_inv K : K →ₗ[K] K⊗[K] K )
  := by
    apply Basis.ext βK
    intro i
    simp [unitor_left_inv]
    simp [Alg_unit_βK_lemma,Alg_unit_1_lemma]
    simp [Alg_comul,Alg_comul_on_basis]

theorem Alg_counit_mul :
  ( Alg_counit : (@Alg K G) →ₗ[K] K )
  ∘ₗ
  ( Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G))
  =
  ( unitor_left K : K ⊗[K] K →ₗ[K] K )
  ∘ₗ
  ( (TensorProduct.map Alg_counit Alg_counit) : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] K ⊗[K] K )
  := by
    apply Basis.ext ββ
    intro (g,h)
    simp [unitor_left,ββ]
    simp [Alg_mul_ββ_lemma,Alg_mul_on_basis]
    simp [Alg_counit,Alg_counit_on_basis]

theorem Alg_counit_unit :
  ( Alg_counit : (@Alg K G) →ₗ[K] K )
  ∘ₗ
  ( Alg_unit : K →ₗ[K] (@Alg K G) )
  =
  ( LinearMap.id : K →ₗ[K] K )
  := by
    apply Basis.ext βK
    intro i
    simp [Alg_unit_βK_lemma,
      Alg_counit,Alg_counit_on_basis]
    simp [βK]

theorem Alg_anti_left :
  ( Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) )
  ∘ₗ
  ( LinearMap.lTensor Alg Alg_anti : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) )
  ∘ₗ
  ( Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) )
  =
  ( Alg_unit : K →ₗ[K] (@Alg K G) )
  ∘ₗ
  ( Alg_counit : (@Alg K G) →ₗ[K] K )
  := by
    apply Basis.ext β
    intro g
    simp [Alg_comul,Alg_comul_on_basis]
    simp [Alg_counit,Alg_counit_on_basis,Alg_unit_1_lemma]
    simp [Alg_anti,Alg_anti_on_basis]
    simp [Alg_mul_ββ_lemma,Alg_mul_on_basis]

theorem Alg_anti_right :
  ( Alg_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) )
  ∘ₗ
  ( LinearMap.rTensor Alg Alg_anti : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) )
  ∘ₗ
  ( Alg_comul : (@Alg K G) →ₗ[K] (@Alg K G) ⊗[K] (@Alg K G) )
  =
  ( Alg_unit : K →ₗ[K] (@Alg K G) )
  ∘ₗ
  ( Alg_counit : (@Alg K G) →ₗ[K] K )
  := by
    apply Basis.ext β
    intro g
    simp [Alg_comul,Alg_comul_on_basis]
    simp [Alg_counit,Alg_counit_on_basis,Alg_unit_1_lemma]
    simp [Alg_anti,Alg_anti_on_basis]
    simp [Alg_mul_ββ_lemma,Alg_mul_on_basis]

noncomputable instance : BialgebraTens K (@Alg K G) where
  comul_mul := Alg_comul_mul
  comul_unit := Alg_comul_unit
  counit_mul := Alg_counit_mul
  counit_unit := Alg_counit_unit

open AlgebraTens CoalgebraTens

noncomputable instance : HopfAlgebraTens K (@Alg K G) where
  anti := Alg_anti
  hasAntipodeProp :=
  {
    left := by
      simp [mul,comul,unit,counit]; rw[Alg_anti_left]
    right := by
      simp [mul,comul,unit,counit]; rw[Alg_anti_right]
  }

end GroupAlgebra
