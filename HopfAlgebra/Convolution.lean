import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HopfAlgebra.Basic

namespace Convolution

open scoped TensorProduct
open Hopf
open AlgebraTens CoalgebraTens HopfAlgebraTens

variable {R:Type} [CommSemiring R]
variable {H:Type} [AddCommMonoid H] [Module R H] [HopfAlgebraTens R H]

/- convAlg: the convolution algebra as an R-module -/
def convAlg := H →ₗ[R] H
instance : AddCommMonoid (@convAlg R _ H _ _) := inferInstanceAs (AddCommMonoid (LinearMap (RingHom.id R) H H))
instance : Module R (@convAlg R _ H _ _) := inferInstanceAs (Module R (LinearMap (RingHom.id R) H H))

/- The library function homTensorHomMap gives the linear equivalence
   End(H) ⊗ End(H) → End(H⊗H). This is then used to produce a linear map
   (End(H) ⊗ End(H)) ⊗ (H⊗H) → H⊗H.
   Finally from this the convolution product is build as
   H → H⊗H → (R⊗R)⊗(H⊗H) → (End(H) ⊗ End(H)) ⊗ (H⊗H) → H⊗H → H
-/

noncomputable def convAlg_mul_aux : ((@convAlg R _ H _ _) ⊗[R] (@convAlg R _ H _ _)) ⊗[R] H →ₗ[R] H :=
( let aux : ((@convAlg R _ H _ _) ⊗[R] (@convAlg R _ H _ _)) ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    TensorProduct.lift (TensorProduct.homTensorHomMap R H H H H : (convAlg ⊗[R] convAlg) →ₗ[R] (H ⊗[R] H) →ₗ[R] (H ⊗[R] H))

  (mul : H ⊗[R] H →ₗ[R] H)
  ∘ₗ
  (aux : (convAlg ⊗[R] convAlg) ⊗[R] (H ⊗[R] H) →ₗ[R] (H ⊗[R] H))
  ∘ₗ
  (LinearMap.lTensor (convAlg ⊗[R] convAlg) comul
    : (convAlg ⊗[R] convAlg) ⊗[R] H →ₗ[R] ((@convAlg R _ H _ _) ⊗[R] (@convAlg R _ H _ _)) ⊗[R] (H ⊗[R] H))
)

noncomputable def convAlg_mul : (@convAlg R _ H _ _) ⊗[R] (@convAlg R _ H _ _) →ₗ[R] (@convAlg R _ H _ _) :=
  TensorProduct.curry convAlg_mul_aux

variable (f g : (@convAlg R _ H _ _)) (x:H)

example : convAlg_mul_aux ((f ⊗ₜ[R] g) ⊗ₜ[R] x) = mul (((TensorProduct.homTensorHomMap R H H H H) (f ⊗ₜ[R] g)) (comul x))
  := by
    simp [convAlg_mul_aux]
    rw [← TensorProduct.homTensorHomMap_apply]
    rfl

theorem convAlg_mul_apply (f g : (@convAlg R _ H _ _)) :
  convAlg_mul (f ⊗ₜ[R] g) = mul ∘ₗ (TensorProduct.map f g) ∘ₗ comul
  := by
    apply LinearMap.ext
    intro x
    simp [convAlg_mul]

    calc
      ((TensorProduct.curry convAlg_mul_aux) (f ⊗ₜ[R] g)) x
        = convAlg_mul_aux ((f ⊗ₜ[R] g) ⊗ₜ[R] x)
            := TensorProduct.curry_apply convAlg_mul_aux (f ⊗ₜ[R] g) x
      _ = mul ((TensorProduct.map f g) (comul x))
            := by
            simp [convAlg_mul_aux]
            rw [← TensorProduct.homTensorHomMap_apply]
            rfl

def convAlg_unit_el : (@convAlg R _ H _ _) := (unit ∘ₗ counit : H →ₗ[R] H)

def convAlg_unit : R →ₗ[R] (@convAlg R _ H _ _) :=
  {
    toFun := fun r ↦ r • convAlg_unit_el
    map_add' := by intro r s; simp [add_smul]
    map_smul' := by intro r s; simp [mul_smul]
  }

-- OMG I am doing this so wrong.
theorem convAlg_one_mul_el (f : (@convAlg R _ H _ _)) :
  convAlg_mul (convAlg_unit_el ⊗ₜ[R] f) = f
  := by
    rw [convAlg_mul_apply]
    simp [convAlg_unit_el]
    calc
      mul ∘ₗ TensorProduct.map (unit ∘ₗ counit) f ∘ₗ comul
      = mul ∘ₗ TensorProduct.map (unit ∘ₗ counit) (f ∘ₗ LinearMap.id) ∘ₗ comul
            := by simp
      _ = mul ∘ₗ (TensorProduct.map unit f)
          ∘ₗ (TensorProduct.map counit LinearMap.id) ∘ₗ comul
            := by rw [TensorProduct.map_comp]; rfl
      _ = mul ∘ₗ (TensorProduct.map unit f) ∘ₗ ((unitor_left_inv H)
          ∘ₗ (unitor_left H))
          ∘ₗ (LinearMap.rTensor H counit) ∘ₗ comul
            := by simp [LinearMap.rTensor]; simp [unitor_left_inv_is_inv]
      _ = mul ∘ₗ (TensorProduct.map unit f) ∘ₗ (unitor_left_inv H)
          ∘ₗ (unitor_left H)
          ∘ₗ (LinearMap.rTensor H counit) ∘ₗ comul
            := by simp [LinearMap.comp_assoc]
      _ = mul ∘ₗ (TensorProduct.map unit f) ∘ₗ (unitor_left_inv H)
            := by simp [CoalgebraTens.coone_comul]
      _ = mul ∘ₗ (TensorProduct.map (unit ∘ₗ LinearMap.id) (LinearMap.id ∘ₗ f)) ∘ₗ (unitor_left_inv H)
            := by simp
      _ = mul ∘ₗ (TensorProduct.map unit LinearMap.id)
            ∘ₗ (TensorProduct.map LinearMap.id f)
            ∘ₗ (unitor_left_inv H)
            := by rw [TensorProduct.map_comp]; rfl
      _ = mul ∘ₗ (TensorProduct.map unit LinearMap.id)
            ∘ₗ ((unitor_left_inv H) ∘ₗ (unitor_left H))
            ∘ₗ (TensorProduct.map LinearMap.id f)
            ∘ₗ (unitor_left_inv H)
            := by simp [unitor_left_inv_is_inv]
      _ = (mul ∘ₗ (LinearMap.rTensor H unit)
            ∘ₗ (unitor_left_inv H)) ∘ₗ (unitor_left H)
            ∘ₗ (TensorProduct.map LinearMap.id f)
            ∘ₗ (unitor_left_inv H)
            := by simp [LinearMap.rTensor]; simp [LinearMap.comp_assoc]
      _ = (unitor_left H)
            ∘ₗ (TensorProduct.map LinearMap.id f)
            ∘ₗ (unitor_left_inv H)
            := by simp [AlgebraTens.one_mul]
      _ = f := by
        simp [unitor_left,unitor_left_inv]
        apply LinearMap.ext
        intro x
        simp

theorem convAlg_mul_one_el (f : (@convAlg R _ H _ _)) :
  convAlg_mul (f ⊗ₜ[R] convAlg_unit_el) = f
  := by
    rw [convAlg_mul_apply]
    simp [convAlg_unit_el]
    calc
      mul ∘ₗ TensorProduct.map f (unit ∘ₗ counit) ∘ₗ comul
      = mul ∘ₗ TensorProduct.map (f ∘ₗ LinearMap.id) (unit ∘ₗ counit) ∘ₗ comul
            := by simp
      _ = mul ∘ₗ (TensorProduct.map f unit)
          ∘ₗ (TensorProduct.map LinearMap.id counit) ∘ₗ comul
            := by rw [TensorProduct.map_comp]; rfl
      _ = mul ∘ₗ (TensorProduct.map f unit) ∘ₗ ((unitor_right_inv H)
          ∘ₗ (unitor_right H))
          ∘ₗ (LinearMap.lTensor H counit) ∘ₗ comul
            := by simp [LinearMap.lTensor]; simp [unitor_right_inv_is_inv]
      _ = mul ∘ₗ (TensorProduct.map f unit) ∘ₗ (unitor_right_inv H)
          ∘ₗ (unitor_right H)
          ∘ₗ (LinearMap.lTensor H counit) ∘ₗ comul
            := by simp [LinearMap.comp_assoc]
      _ = mul ∘ₗ (TensorProduct.map f unit) ∘ₗ (unitor_right_inv H)
            := by simp [CoalgebraTens.comul_coone]
      _ = mul ∘ₗ (TensorProduct.map (LinearMap.id ∘ₗ f) (unit ∘ₗ LinearMap.id))
          ∘ₗ (unitor_right_inv H)
            := by simp
      _ = mul ∘ₗ (TensorProduct.map LinearMap.id unit)
            ∘ₗ (TensorProduct.map f LinearMap.id)
            ∘ₗ (unitor_right_inv H)
            := by rw [TensorProduct.map_comp]; rfl
      _ = mul ∘ₗ (TensorProduct.map LinearMap.id unit)
            ∘ₗ ((unitor_right_inv H) ∘ₗ (unitor_right H))
            ∘ₗ (TensorProduct.map f LinearMap.id)
            ∘ₗ (unitor_right_inv H)
            := by simp [unitor_right_inv_is_inv]
      _ = (mul ∘ₗ (LinearMap.lTensor H unit)
            ∘ₗ (unitor_right_inv H)) ∘ₗ (unitor_right H)
            ∘ₗ (TensorProduct.map f LinearMap.id)
            ∘ₗ (unitor_right_inv H)
            := by simp [LinearMap.lTensor]; simp [LinearMap.comp_assoc]
      _ = (unitor_right H)
            ∘ₗ (TensorProduct.map f LinearMap.id)
            ∘ₗ (unitor_right_inv H)
            := by simp [AlgebraTens.mul_one]
      _ = f := by
        simp [unitor_right,unitor_right_inv]
        apply LinearMap.ext
        intro x
        simp

theorem convAlg_mul_assoc_el (f g h: (@convAlg R _ H _ _)) :
  convAlg_mul (f ⊗ₜ[R] (convAlg_mul (g ⊗ₜ[R] h))) =
    convAlg_mul ((convAlg_mul (f ⊗ₜ[R] g)) ⊗ₜ[R] h)
  := by
    simp [convAlg_mul_apply]
    sorry

noncomputable instance : AlgebraTens R (@convAlg R _ H _ _) where
  mul := convAlg_mul
  unit := convAlg_unit

  one_mul := by
    apply LinearMap.ext
    intro f
    simp [unitor_left_inv,convAlg_unit]
    exact convAlg_one_mul_el f

  mul_one := by
    apply LinearMap.ext
    intro f
    simp [unitor_right_inv,convAlg_unit]
    exact convAlg_mul_one_el f

  mul_assoc := by
    apply TensorProduct.ext_threefold
    intro f g h
    simp [convAlg_mul_assoc_el]

theorem tensor_id_f (f:H →ₗ[R] H): TensorProduct.map LinearMap.id f = LinearMap.lTensor H f
  := by simp [LinearMap.lTensor]

theorem tensor_f_id (f:H →ₗ[R] H): TensorProduct.map f LinearMap.id = LinearMap.rTensor H f
  := by simp [LinearMap.rTensor]

theorem conv_id_S : convAlg_mul ((LinearMap.id : H →ₗ[R] H) ⊗ₜ[R] anti) = convAlg_unit_el
  := by
    rw [convAlg_mul_apply]
    rw [tensor_id_f]
    rw [hasAntipodeProp.left]
    rw [convAlg_unit_el]

theorem conv_S_id : convAlg_mul (anti ⊗ₜ[R] (LinearMap.id : H →ₗ[R] H)) = convAlg_unit_el
  := by
    rw [convAlg_mul_apply]
    rw [tensor_f_id]
    rw [hasAntipodeProp.right]
    rw [convAlg_unit_el]

theorem HopfAntipodeUnique (f : H →ₗ[R] H) (h: AntipodeProp f) :
  f = anti
  := by
    let u : @convAlg R _ H _ _ := convAlg_unit_el
    have : convAlg_mul (f ⊗ₜ[R] LinearMap.id) = u
      := by
        rw [convAlg_mul_apply]
        rw [tensor_f_id]
        rw [h.right]
        simp [u,convAlg_unit_el]

    calc
      f = convAlg_mul ( f ⊗ₜ[R] u ) := by rw [convAlg_mul_one_el]
      _ = convAlg_mul ( f ⊗ₜ[R] (convAlg_mul ( LinearMap.id ⊗ₜ[R] anti )) ) := by rw [conv_id_S]
      _ = convAlg_mul ( (convAlg_mul (f ⊗ₜ[R] LinearMap.id)) ⊗ₜ[R] anti ) := by rw [convAlg_mul_assoc_el]
      _ = convAlg_mul ( u ⊗ₜ[R] anti ) := by rw [this]
      _ = anti := by rw [convAlg_one_mul_el]

end Convolution
