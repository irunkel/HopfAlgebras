import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HopfAlgebra.Basic

open BigOperators
open Finset
open scoped TensorProduct
open Hopf

namespace FunctionsOnGroup

variable {G : Type} [Group G] [Finite G] [DecidableEq G]
variable {K : Type} [CommRing K]

-- Fintype is needed for the Bigoperators to work, Σ etc.
noncomputable instance : Fintype G := Fintype.ofFinite G

abbrev Fun
  := G → K

noncomputable def βK : Basis (Fin 1) K K
  := Basis.singleton (Fin 1) K

noncomputable def β : Basis G K (@Fun G K)
  := Pi.basisFun K G

noncomputable def ββ : Basis (Prod G G) K ((@Fun G K) ⊗[K] (@Fun G K))
  := Basis.tensorProduct β β

noncomputable def βββ : Basis ((G × G) × G) K
  (((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K))
  := Basis.tensorProduct ββ β

/- --- Algebra structure on function algebra --- -/

noncomputable def Fun_mul_on_basis : G × G → (@Fun G K) :=
  fun (a,b) ↦ if a=b then β a else 0

noncomputable def Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) :=
  Basis.constr ββ K Fun_mul_on_basis

theorem Fun_mul_ββ_lemma  {g h : G} : Fun_mul ((β g) ⊗ₜ[K] (β h)) = Fun_mul_on_basis (g,h)
  := by
    rw [Fun_mul]
    rw [← Basis.tensorProduct_apply, ← ββ]
    simp

theorem Fun_mul_assoc :
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (LinearMap.rTensorHom Fun Fun_mul
        : ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K) →ₗ[K] ((@Fun G K) ⊗[K] (@Fun G K)))
    =
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (LinearMap.lTensorHom Fun Fun_mul
        : (@Fun G K) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)) →ₗ[K] ((@Fun G K) ⊗[K] (@Fun G K)))
    ∘ₗ (TensorProduct.assoc K (@Fun G K) (@Fun G K) (@Fun G K)
        : ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)))
  := by
    apply Basis.ext βββ
    intro ⟨ ⟨a,b⟩ , c ⟩
    simp
    rw [βββ,ββ]
    simp [Fun_mul_ββ_lemma,Fun_mul_on_basis]
    cases (eq_or_ne a b) with
    | inl h =>
        simp [h]
        cases (eq_or_ne b c) with
        | inl hh => simp[hh]
        | inr hh => simp[hh,Fun_mul_ββ_lemma,Fun_mul_on_basis]
    | inr h =>
        simp [h]
        cases (eq_or_ne b c) with
        | inr hh => simp[hh]
        | inl hh =>
            simp[hh,Fun_mul_ββ_lemma,Fun_mul_on_basis]
            have : a ≠ c := by rw[hh] at h; exact h
            simp [this]

noncomputable def Fun_unit_el : (@Fun G K) := fun (_:G) ↦ (1:K)

open BigOperators

noncomputable def Fun_unit_el_bas : (@Fun G K)
  := ∑ x : G, β x

#check Finset.sum univ (fun x ↦ β x)

theorem Fun_units_agree :
  (Fun_unit_el : @Fun G K) = (Fun_unit_el_bas : @Fun G K)
  := by
    apply funext
    intro g
    rw [Fun_unit_el,Fun_unit_el_bas,β]
    simp -- I do not understand how simp closes the goal here,
         -- Tried to reproduce with rewrites, did not manage.

noncomputable def Fun_unit : K →ₗ[K] (@Fun G K) :=
  Basis.constr βK K (fun (_: Fin 1) ↦ Fun_unit_el_bas)

theorem Fun_one_mul :
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (LinearMap.rTensorHom Fun Fun_unit : K ⊗[K] (@Fun G K)  →ₗ[K]  (@Fun G K) ⊗[K] (@Fun G K))
    ∘ₗ (unitor_left_inv Fun : (@Fun G K) →ₗ[K] (K ⊗[K] (@Fun G K)))
    =
    (LinearMap.id : (@Fun G K) →ₗ[K] (@Fun G K))
    := by
      apply Basis.ext β
      intro i
      simp [unitor_left_inv,Fun_unit,Fun_unit_el_bas,βK,
        TensorProduct.sum_tmul,
        Fun_mul_ββ_lemma,Fun_mul_on_basis]

theorem Fun_mul_one :
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (LinearMap.lTensorHom Fun Fun_unit : (@Fun G K) ⊗[K] K  →ₗ[K]  (@Fun G K) ⊗[K] (@Fun G K))
    ∘ₗ (unitor_right_inv Fun :  (@Fun G K) →ₗ[K] ((@Fun G K) ⊗[K] K))
    =
    (LinearMap.id : (@Fun G K) →ₗ[K] (@Fun G K))
    := by
      apply Basis.ext β
      intro i
      simp [unitor_right_inv,Fun_unit,Fun_unit_el_bas,βK,
        TensorProduct.tmul_sum,
        Fun_mul_ββ_lemma,Fun_mul_on_basis]

noncomputable instance : AlgebraTens K (@Fun G K) where
  mul := Fun_mul
  unit := Fun_unit
  one_mul := Fun_one_mul
  mul_one := Fun_mul_one
  mul_assoc := Fun_mul_assoc

/- --- Coalgebra structure on function algebra --- -/

noncomputable def Fun_comul_on_basis : G → (@Fun G K) ⊗[K] (@Fun G K)
  := fun g ↦ ∑ h:G , β (g*h) ⊗ₜ[K] β h⁻¹

noncomputable def Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) :=
  Basis.constr β K Fun_comul_on_basis

noncomputable def Fun_counit_on_basis : G → K := fun g ↦
  if g = (1:G) then (1:K) else (0:K)

noncomputable def Fun_counit : (@Fun G K) →ₗ[K] K :=
  Basis.constr β K Fun_counit_on_basis

theorem Fun_coone_comul :
  (unitor_left Fun : K ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
  ∘ₗ (LinearMap.rTensorHom Fun Fun_counit : (@Fun G K) ⊗[K] (@Fun G K)  →ₗ[K]  K ⊗[K] (@Fun G K))
  ∘ₗ (Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K))
  =
  (LinearMap.id : (@Fun G K) →ₗ[K] (@Fun G K))
  := by
    sorry

theorem Fun_comul_coone :
  (unitor_right Fun :  (@Fun G K) ⊗[K] K →ₗ[K] (@Fun G K))
  ∘ₗ (LinearMap.lTensorHom Fun Fun_counit : (@Fun G K) ⊗[K] (@Fun G K)  →ₗ[K]  (@Fun G K) ⊗[K] K)
  ∘ₗ (Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K))
  =
  (LinearMap.id : (@Fun G K) →ₗ[K] (@Fun G K))
  := by
    sorry

theorem Fun_comul_coassoc :
  (TensorProduct.assoc K (@Fun G K) (@Fun G K) (@Fun G K)
      : ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)))
  ∘ₗ (LinearMap.rTensorHom Fun Fun_comul
      : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K))
  ∘ₗ (Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K))
  =
  (LinearMap.lTensorHom Fun Fun_comul
      : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)))
  ∘ₗ (Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K))
  := by
    sorry

noncomputable instance : CoalgebraTens K (@Fun G K) where
  comul := Fun_comul
  counit := Fun_counit
  coone_comul := Fun_coone_comul
  comul_coone := Fun_comul_coone
  comul_coassoc := Fun_comul_coassoc


/- --- Hopf algebra structure on function algebra --- -/

def Fun_anti : (@Fun G K) →ₗ[K] (@Fun G K) := sorry

theorem Fun_comul_mul :
  ( mulAA : ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( tensor_hom Fun_comul Fun_comul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)) )
  =
  ( Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
  := by
    sorry

theorem Fun_comul_unit :
  ( Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( Fun_unit : K →ₗ[K] (@Fun G K) )
  =
  ( (tensor_hom Fun_unit Fun_unit) : K ⊗[K] K →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( unitor_left_inv K : K →ₗ[K] K⊗[K] K )
  := by
    sorry

theorem Fun_counit_mul :
  ( Fun_counit : (@Fun G K) →ₗ[K] K )
  ∘ₗ
  ( Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
  =
  ( unitor_left K : K ⊗[K] K →ₗ[K] K )
  ∘ₗ
  ( (tensor_hom Fun_counit Fun_counit) : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] K ⊗[K] K )
  := by
    sorry

theorem Fun_counit_unit :
  ( Fun_counit : (@Fun G K) →ₗ[K] K )
  ∘ₗ
  ( Fun_unit : K →ₗ[K] (@Fun G K) )
  =
  ( LinearMap.id : K →ₗ[K] K )
  := by
    sorry

theorem Fun_anti_left :
  ( Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) )
  ∘ₗ
  ( LinearMap.lTensorHom Fun Fun_anti : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  =
  ( Fun_unit : K →ₗ[K] (@Fun G K) )
  ∘ₗ
  ( Fun_counit : (@Fun G K) →ₗ[K] K )
  := by
    sorry

theorem Fun_anti_right :
  ( Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) )
  ∘ₗ
  ( LinearMap.rTensorHom Fun Fun_anti : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  =
  ( Fun_unit : K →ₗ[K] (@Fun G K) )
  ∘ₗ
  ( Fun_counit : (@Fun G K) →ₗ[K] K )
  := by
    sorry

noncomputable instance : HopfAlgebraTens K (@Fun G K) where
  anti := Fun_anti
  comul_mul := Fun_comul_mul
  comul_unit := Fun_comul_unit
  counit_mul := Fun_counit_mul
  counit_unit := Fun_counit_unit
  anti_left := Fun_anti_left
  anti_right := Fun_anti_right


/- --- Function algebra for Z/4Z as an example --- -/

def C4 := Multiplicative (Fin 4)
instance : Group C4 := inferInstanceAs (Group (Multiplicative (Fin 4)))
instance : Finite C4 := inferInstanceAs (Finite (Fin 4))
abbrev FunC4 := @Fun C4 ℚ

example : Fun_mul_on_basis ( (3:Fin 4) , (3:Fin 4) ) = (β (3:Fin 4):FunC4) :=
  by
    simp [Fun_mul_on_basis]
    rfl

example : Fun_mul ( (β (3:Fin 4)) ⊗ₜ[K] (β (3:Fin 4)) ) = β (3:Fin 4) :=
  by simp [Fun_mul_ββ_lemma,Fun_mul_on_basis]

example : Fun_mul ( (β (2:Fin 4)) ⊗ₜ[K] (β (3:Fin 4)) ) = 0 :=
  by simp [Fun_mul_ββ_lemma,Fun_mul_on_basis]

end FunctionsOnGroup

-- This is in Mathlib as "MonoidAlgebra"
namespace GroupAlgebra

variable {K : Type} [CommRing K]
variable {G : Type} [Group G] [Finite G] [DecidableEq G]

abbrev Alg := G → K

noncomputable def β : Basis G K (@Alg K G)
  := Pi.basisFun K G

noncomputable def ββ : Basis (Prod G G) K ((@Alg K G) ⊗[K] (@Alg K G))
  := Basis.tensorProduct β β

noncomputable def AlgG_mul_on_basis : G × G → (@Alg K G) :=
  fun (a,b) ↦ β (a*b)

noncomputable def AlgG_mul : (@Alg K G) ⊗[K] (@Alg K G) →ₗ[K] (@Alg K G) :=
  Basis.constr ββ K AlgG_mul_on_basis

noncomputable def Alg_unit : K →ₗ[K] (@Alg K G) :=
{
  toFun := fun (a:K) ↦ a • (β (1:G))
  map_add' := by
    intro a b
    simp [add_smul]
  map_smul' := by
    intro a b
    dsimp
    rw [mul_smul (a:K) (b:K) (β 1)]
}


end GroupAlgebra
