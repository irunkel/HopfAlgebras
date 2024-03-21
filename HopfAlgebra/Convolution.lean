import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HopfAlgebra.Basic

namespace Convolution

open scoped TensorProduct
open LinearMap
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
  (lTensor (convAlg ⊗[R] convAlg) comul
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
      = mul ∘ₗ TensorProduct.map (unit ∘ₗ counit) (f ∘ₗ id) ∘ₗ comul
            := by simp
      _ = mul ∘ₗ (TensorProduct.map unit f)
          ∘ₗ (TensorProduct.map counit id) ∘ₗ comul
            := by rw [TensorProduct.map_comp]; rfl
      _ = mul ∘ₗ (TensorProduct.map unit f) ∘ₗ ((unitor_left_inv H)
          ∘ₗ (unitor_left H))
          ∘ₗ (rTensor H counit) ∘ₗ comul
            := by simp [rTensor]; simp [unitor_left_inv_is_inv]
      _ = mul ∘ₗ (TensorProduct.map unit f) ∘ₗ (unitor_left_inv H)
          ∘ₗ (unitor_left H)
          ∘ₗ (rTensor H counit) ∘ₗ comul
            := by simp [comp_assoc]
      _ = mul ∘ₗ (TensorProduct.map unit f) ∘ₗ (unitor_left_inv H)
            := by simp [CoalgebraTens.coone_comul]
      _ = mul ∘ₗ (TensorProduct.map (unit ∘ₗ id) (id ∘ₗ f)) ∘ₗ (unitor_left_inv H)
            := by simp
      _ = mul ∘ₗ (TensorProduct.map unit id)
            ∘ₗ (TensorProduct.map id f)
            ∘ₗ (unitor_left_inv H)
            := by rw [TensorProduct.map_comp]; rfl
      _ = mul ∘ₗ (TensorProduct.map unit id)
            ∘ₗ ((unitor_left_inv H) ∘ₗ (unitor_left H))
            ∘ₗ (TensorProduct.map id f)
            ∘ₗ (unitor_left_inv H)
            := by simp [unitor_left_inv_is_inv]
      _ = (mul ∘ₗ (rTensor H unit)
            ∘ₗ (unitor_left_inv H)) ∘ₗ (unitor_left H)
            ∘ₗ (TensorProduct.map id f)
            ∘ₗ (unitor_left_inv H)
            := by simp [rTensor]; simp [comp_assoc]
      _ = (unitor_left H)
            ∘ₗ (TensorProduct.map id f)
            ∘ₗ (unitor_left_inv H)
            := by simp [AlgebraTens.one_mul]
      _ = f := by
        simp [unitor_left,unitor_left_inv]
        apply ext
        intro x
        simp

theorem convAlg_mul_one_el (f : (@convAlg R _ H _ _)) :
  convAlg_mul (f ⊗ₜ[R] convAlg_unit_el) = f
  := by
    rw [convAlg_mul_apply]
    simp [convAlg_unit_el]
    calc
      mul ∘ₗ TensorProduct.map f (unit ∘ₗ counit) ∘ₗ comul
      = mul ∘ₗ TensorProduct.map (f ∘ₗ id) (unit ∘ₗ counit) ∘ₗ comul
            := by simp
      _ = mul ∘ₗ (TensorProduct.map f unit)
          ∘ₗ (TensorProduct.map id counit) ∘ₗ comul
            := by rw [TensorProduct.map_comp]; rfl
      _ = mul ∘ₗ (TensorProduct.map f unit) ∘ₗ ((unitor_right_inv H)
          ∘ₗ (unitor_right H))
          ∘ₗ (lTensor H counit) ∘ₗ comul
            := by simp [lTensor]; simp [unitor_right_inv_is_inv]
      _ = mul ∘ₗ (TensorProduct.map f unit) ∘ₗ (unitor_right_inv H)
          ∘ₗ (unitor_right H)
          ∘ₗ (lTensor H counit) ∘ₗ comul
            := by simp [comp_assoc]
      _ = mul ∘ₗ (TensorProduct.map f unit) ∘ₗ (unitor_right_inv H)
            := by simp [CoalgebraTens.comul_coone]
      _ = mul ∘ₗ (TensorProduct.map (id ∘ₗ f) (unit ∘ₗ id))
          ∘ₗ (unitor_right_inv H)
            := by simp
      _ = mul ∘ₗ (TensorProduct.map id unit)
            ∘ₗ (TensorProduct.map f id)
            ∘ₗ (unitor_right_inv H)
            := by rw [TensorProduct.map_comp]; rfl
      _ = mul ∘ₗ (TensorProduct.map id unit)
            ∘ₗ ((unitor_right_inv H) ∘ₗ (unitor_right H))
            ∘ₗ (TensorProduct.map f id)
            ∘ₗ (unitor_right_inv H)
            := by simp [unitor_right_inv_is_inv]
      _ = (mul ∘ₗ (lTensor H unit)
            ∘ₗ (unitor_right_inv H)) ∘ₗ (unitor_right H)
            ∘ₗ (TensorProduct.map f id)
            ∘ₗ (unitor_right_inv H)
            := by simp [lTensor]; simp [comp_assoc]
      _ = (unitor_right H)
            ∘ₗ (TensorProduct.map f id)
            ∘ₗ (unitor_right_inv H)
            := by simp [AlgebraTens.mul_one]
      _ = f := by
        simp [unitor_right,unitor_right_inv]
        apply ext
        intro x
        simp

theorem convAlg_mul_assoc_el (f g h: (@convAlg R _ H _ _)) :
  convAlg_mul (f ⊗ₜ[R] (convAlg_mul (g ⊗ₜ[R] h))) =
    convAlg_mul ((convAlg_mul (f ⊗ₜ[R] g)) ⊗ₜ[R] h)
  := by
  simp [convAlg_mul_apply]
  calc
  mul
  ∘ₗ TensorProduct.map f (mul ∘ₗ TensorProduct.map g h ∘ₗ comul)
  ∘ₗ comul
  =
  mul
  ∘ₗ TensorProduct.map (id ∘ₗ (f ∘ₗ id)) (mul ∘ₗ (TensorProduct.map g h ∘ₗ comul))
  ∘ₗ comul
      := by simp
  _ =
  mul
  ∘ₗ TensorProduct.map id mul
  ∘ₗ TensorProduct.map (f ∘ₗ id) (TensorProduct.map g h ∘ₗ comul)
  ∘ₗ comul
      := by rw [TensorProduct.map_comp]; simp [comp_assoc]
  _ =
  (mul
  ∘ₗ TensorProduct.map id mul)
  ∘ₗ TensorProduct.map f (TensorProduct.map g h)
  ∘ₗ (TensorProduct.map id comul
  ∘ₗ comul)
      := by rw [TensorProduct.map_comp]; simp [comp_assoc]
  _ =
  (mul
  ∘ₗ lTensor H mul)
  ∘ₗ TensorProduct.map f (TensorProduct.map g h)
  ∘ₗ (lTensor H comul
  ∘ₗ comul)
      := by simp [lTensor]
  _ =
  (mul
  ∘ₗ lTensor H mul)
  ∘ₗ (assoc H H H
  ∘ₗ assoc_inv H H H)
  ∘ₗ TensorProduct.map f (TensorProduct.map g h)
  ∘ₗ (assoc H H H
  ∘ₗ rTensor H comul
  ∘ₗ comul)
      := by
        rw [assoc_inv_is_inv']
        rw [← CoalgebraTens.comul_coassoc]
        simp [comp_assoc,assoc]
  _ =
  (mul
  ∘ₗ lTensor H mul
  ∘ₗ assoc H H H)
  ∘ₗ (assoc_inv H H H
  ∘ₗ TensorProduct.map f (TensorProduct.map g h)
  ∘ₗ assoc H H H)
  ∘ₗ (rTensor H comul
  ∘ₗ comul)
      := by simp [comp_assoc]
  _ =
  (mul
  ∘ₗ rTensor H mul)
  ∘ₗ (assoc_inv H H H
  ∘ₗ assoc H H H
  ∘ₗ TensorProduct.map (TensorProduct.map f g) h)
  ∘ₗ (rTensor H comul
  ∘ₗ comul)
      := by
        rw [AlgebraTens.mul_assoc]
        nth_rw 2 [assoc]
        rw [TensorProduct.map_map_comp_assoc_eq f g h]
        rw [← assoc]
  _ =
  mul
  ∘ₗ rTensor H mul
  ∘ₗ (assoc_inv H H H
  ∘ₗ assoc H H H)
  ∘ₗ TensorProduct.map (TensorProduct.map f g) h
  ∘ₗ rTensor H comul
  ∘ₗ comul
      := by simp [comp_assoc]
  _ =
  mul
  ∘ₗ rTensor H mul
  ∘ₗ TensorProduct.map (TensorProduct.map f g) h
  ∘ₗ rTensor H comul
  ∘ₗ comul
      := by rw [assoc_inv_is_inv]; simp
  _ =
  mul
  ∘ₗ TensorProduct.map mul id
  ∘ₗ TensorProduct.map (TensorProduct.map f g) h
  ∘ₗ TensorProduct.map comul id
  ∘ₗ comul
      := by simp [rTensor]
  _ =
  mul
  ∘ₗ TensorProduct.map (mul ∘ₗ TensorProduct.map f g) (id ∘ₗ h)
  ∘ₗ TensorProduct.map comul id
  ∘ₗ comul
      := by rw [TensorProduct.map_comp]; simp [comp_assoc]
  _ =
  mul
  ∘ₗ TensorProduct.map ((mul ∘ₗ TensorProduct.map f g) ∘ₗ comul) ((id ∘ₗ h) ∘ₗ id)
  ∘ₗ comul
      := by nth_rw 2 [TensorProduct.map_comp]; simp [comp_assoc]
  _ =
    mul
    ∘ₗ TensorProduct.map (mul ∘ₗ TensorProduct.map f g ∘ₗ comul) h
    ∘ₗ comul
      := by simp [comp_assoc]

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

theorem tensor_id_f (f:H →ₗ[R] H): TensorProduct.map id f = lTensor H f
  := by simp [lTensor]

theorem tensor_f_id (f:H →ₗ[R] H): TensorProduct.map f id = rTensor H f
  := by simp [rTensor]

theorem conv_id_S : convAlg_mul ((id : H →ₗ[R] H) ⊗ₜ[R] anti) = convAlg_unit_el
  := by
    rw [convAlg_mul_apply]
    rw [tensor_id_f]
    rw [hasAntipodeProp.left]
    rw [convAlg_unit_el]

theorem conv_S_id : convAlg_mul (anti ⊗ₜ[R] (id : H →ₗ[R] H)) = convAlg_unit_el
  := by
    rw [convAlg_mul_apply]
    rw [tensor_f_id]
    rw [hasAntipodeProp.right]
    rw [convAlg_unit_el]

theorem HopfAntipodeUnique (f : H →ₗ[R] H) (h: AntipodeProp f) :
  f = anti
  := by
    let u : @convAlg R _ H _ _ := convAlg_unit_el
    have : convAlg_mul (f ⊗ₜ[R] id) = u
      := by
        rw [convAlg_mul_apply]
        rw [tensor_f_id]
        rw [h.right]
        simp [u,convAlg_unit_el]

    calc
      f = convAlg_mul ( f ⊗ₜ[R] u ) := by rw [convAlg_mul_one_el]
      _ = convAlg_mul ( f ⊗ₜ[R] (convAlg_mul ( id ⊗ₜ[R] anti )) ) := by rw [conv_id_S]
      _ = convAlg_mul ( (convAlg_mul (f ⊗ₜ[R] id)) ⊗ₜ[R] anti ) := by rw [convAlg_mul_assoc_el]
      _ = convAlg_mul ( u ⊗ₜ[R] anti ) := by rw [this]
      _ = anti := by rw [convAlg_one_mul_el]

end Convolution
