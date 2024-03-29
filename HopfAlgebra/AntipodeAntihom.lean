import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HopfAlgebra.Basic

open LinearMap TensorProduct
open Hopf
open AlgebraTens CoalgebraTens BialgebraTens HopfAlgebraTens

variable {R:Type} [CommSemiring R]
variable {H:Type} [AddCommMonoid H] [Module R H] [HopfAlgebraTens R H]

namespace AntipodeProperties

/- See Klimyk, Schmudgen, Quantum groups and their representations (Springer 1997),
   Sec 1.2.4 Prop. 5 -/

theorem Antipode_unit :
  (anti : H →ₗ[R] H)
  ∘ₗ
  (unit : R →ₗ[R] H)
  =
  (unit : R →ₗ[R] H)

  := by
  apply Eq.symm
  calc
  ( unit : R →ₗ[R] H )
  =
  (( unit : R →ₗ[R] H )
  ∘ₗ ( counit : H →ₗ[R] R ))
  ∘ₗ ( unit : R →ₗ[R] H )
      := by simp [comp_assoc]; rw [counit_unit]; simp
  _ =
  ( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map id anti : H ⊗[R] H →ₗ[R] H ⊗[R] H )
  ∘ₗ ( comul : H →ₗ[R] H ⊗[R] H )
  ∘ₗ ( unit : R →ₗ[R] H )
      := by rw [← hasAntipodeProp.left]; simp [comp_assoc]
  _ =
  ( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map id anti : H ⊗[R] H →ₗ[R] H ⊗[R] H )
  ∘ₗ ( map unit unit : R ⊗[R] R →ₗ[R] H ⊗[R] H )
  ∘ₗ ( unitor_left_inv R : R →ₗ[R] R ⊗[R] R )
      := by rw [← comul_unit]
  _ =
  ( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map (id ∘ₗ unit) (anti ∘ₗ unit) : R ⊗[R] R →ₗ[R] H ⊗[R] H )
  ∘ₗ ( unitor_left_inv R : R →ₗ[R] R ⊗[R] R )
      := by rw [map_comp]; simp [comp_assoc]
  _ =
  ( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ (( map unit id : R ⊗[R] H →ₗ[R] H ⊗[R] H )
  ∘ₗ ( map id (anti ∘ₗ unit) : R ⊗[R] R →ₗ[R] R ⊗[R] H ))
  ∘ₗ ( unitor_left_inv R : R →ₗ[R] R ⊗[R] R )
      := by rw [← map_comp]; simp [comp_assoc]
  _ =
  ( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map unit id : R ⊗[R] H →ₗ[R] H ⊗[R] H )
  ∘ₗ (( unitor_left_inv H : H →ₗ[R] R ⊗[R] H )
  ∘ₗ ( unitor_left H : R ⊗[R] H →ₗ[R] H ))
  ∘ₗ ( map id (anti ∘ₗ unit) : R ⊗[R] R →ₗ[R] R ⊗[R] H )
  ∘ₗ ( unitor_left_inv R : R →ₗ[R] R ⊗[R] R )
      := by simp [comp_assoc]
  _ =
  (( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map unit id : R ⊗[R] H →ₗ[R] H ⊗[R] H )
  ∘ₗ ( unitor_left_inv H : H →ₗ[R] R ⊗[R] H ))
  ∘ₗ ( unitor_left H : R ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map id (anti ∘ₗ unit) : R ⊗[R] R →ₗ[R] R ⊗[R] H )
  ∘ₗ ( unitor_left_inv R : R →ₗ[R] R ⊗[R] R )
      := by simp only [comp_assoc]
  _ =
  (( unitor_left H : R ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map id (anti ∘ₗ unit) : R ⊗[R] R →ₗ[R] R ⊗[R] H ))
  ∘ₗ ( unitor_left_inv R : R →ₗ[R] R ⊗[R] R )
      := by rw[AlgebraTens.one_mul]; simp [comp_assoc]
  _ =
  ( anti ∘ₗ unit : R →ₗ[R] H )
  ∘ₗ ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ ( unitor_left_inv R : R →ₗ[R] R ⊗[R] R )
      := by rw[unitor_left_nat]; simp [comp_assoc]
  _ =
  ( anti ∘ₗ unit : R →ₗ[R] H )
    := by simp

theorem Antipode_counit :
  (counit : H →ₗ[R] R)
  ∘ₗ
  (anti : H →ₗ[R] H)
  =
  (counit : H →ₗ[R] R)

  := by
  apply Eq.symm
  calc
  ( counit : H →ₗ[R] R )
  =
  (( counit : H →ₗ[R] R )
  ∘ₗ ( unit : R →ₗ[R] H ))
  ∘ₗ ( counit : H →ₗ[R] R )
      := by rw [counit_unit]; simp
  _ =
  ( counit : H →ₗ[R] R )
  ∘ₗ (( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map id anti : H ⊗[R] H →ₗ[R] H ⊗[R] H )
  ∘ₗ ( comul : H →ₗ[R] H ⊗[R] H ))
      := by rw [hasAntipodeProp.left]; simp [comp_assoc]
  _ =
  (( counit : H →ₗ[R] R )
  ∘ₗ ( mul : H ⊗[R] H →ₗ[R] H ))
  ∘ₗ ( map id anti : H ⊗[R] H →ₗ[R] H ⊗[R] H )
  ∘ₗ ( comul : H →ₗ[R] H ⊗[R] H )
      := by simp [comp_assoc]
  _ =
  ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ ( map counit counit : H ⊗[R] H →ₗ[R] R ⊗[R] R )
  ∘ₗ ( map id anti : H ⊗[R] H →ₗ[R] H ⊗[R] H )
  ∘ₗ ( comul : H →ₗ[R] H ⊗[R] H )
      := by rw [counit_mul]; simp [comp_assoc]
  _ =
  ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ ( map (counit ∘ₗ id) (counit ∘ₗ anti) : H ⊗[R] H →ₗ[R] R ⊗[R] R )
  ∘ₗ ( comul : H →ₗ[R] H ⊗[R] H )
      := by rw [map_comp]; simp [comp_assoc]
  _ =
  ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ (( map id (counit ∘ₗ anti) : R ⊗[R] H →ₗ[R] R ⊗[R] R )
  ∘ₗ ( map counit id : H ⊗[R] H →ₗ[R] R ⊗[R] H ))
  ∘ₗ ( comul : H →ₗ[R] H ⊗[R] H )
      := by rw [← map_comp]; simp [comp_assoc]
  _ =
  ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ ( map id (counit ∘ₗ anti) : R ⊗[R] H →ₗ[R] R ⊗[R] R )
  ∘ₗ (( unitor_left_inv H : H →ₗ[R] R ⊗[R] H )
  ∘ₗ ( unitor_left H : R ⊗[R] H →ₗ[R] H ))
  ∘ₗ ( map counit id : H ⊗[R] H →ₗ[R] R ⊗[R] H )
  ∘ₗ ( comul : H →ₗ[R] H ⊗[R] H )
      := by simp [comp_assoc]
  _ =
  ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ ( map id (counit ∘ₗ anti) : R ⊗[R] H →ₗ[R] R ⊗[R] R )
  ∘ₗ ( unitor_left_inv H : H →ₗ[R] R ⊗[R] H )
  ∘ₗ (( unitor_left H : R ⊗[R] H →ₗ[R] H )
  ∘ₗ ( map counit id : H ⊗[R] H →ₗ[R] R ⊗[R] H )
  ∘ₗ ( comul : H →ₗ[R] H ⊗[R] H ))
      := by simp only [comp_assoc]
  _ =
  ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ ( map id (counit ∘ₗ anti) : R ⊗[R] H →ₗ[R] R ⊗[R] R )
  ∘ₗ ( unitor_left_inv H : H →ₗ[R] R ⊗[R] H )
      := by rw[CoalgebraTens.coone_comul]; simp [comp_assoc]
  _ =
  (( counit ∘ₗ anti : H →ₗ[R] R )
  ∘ₗ ( unitor_left H : R ⊗[R] H →ₗ[R] H ))
  ∘ₗ ( unitor_left_inv H : H →ₗ[R] R ⊗[R] H )
      := by rw[← unitor_left_nat]; simp [comp_assoc]
  _ =
  ( counit ∘ₗ anti : H →ₗ[R] R )
  ∘ₗ ( unitor_left H : R ⊗[R] H →ₗ[R] H )
  ∘ₗ ( unitor_left_inv H : H →ₗ[R] R ⊗[R] H )
      := by simp [comp_assoc]
  _ =
  ( counit ∘ₗ anti : H →ₗ[R] R )
    := by simp

/- *** Below  are only temporary attempts *** -/
section Work_in_progress_needs_a_different_approach

/- TODO: How do I make it forget the temporary assignments?
   I failed putting it into the theorem with let, that gave a
   type error (that I did not understand)-/

noncomputable abbrev mapA : H ⊗[R] H →ₗ[R] H ⊗[R] (H ⊗[R] H) :=
  ( map id (TensorProduct.comm R H H) : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] (H ⊗[R] H) )
  ∘ₗ
  ( assoc H H H : (H ⊗[R] H) ⊗[R] H →ₗ[R] H ⊗[R] (H ⊗[R] H) )
  ∘ₗ
  ( map comul id : H ⊗[R] H →ₗ[R] (H ⊗[R] H) ⊗[R] H )

noncomputable abbrev lhs : H ⊗[R] H →ₗ[R] H :=
  ( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ
  ( map anti anti : H ⊗[R] H →ₗ[R] H ⊗[R] H )

noncomputable abbrev step1a : H ⊗[R] (H ⊗[R] R) →ₗ[R] (H ⊗[R] H) ⊗[R] (R ⊗[R] R) :=
  ( map id (map counit id) : (H ⊗[R] H) ⊗[R] (H ⊗[R] R) →ₗ[R] (H ⊗[R] H) ⊗[R] (R ⊗[R] R) )
  ∘ₗ
  ( assoc (H ⊗[R] H) H R : ((H ⊗[R] H) ⊗[R] H) ⊗[R] R →ₗ[R] (H ⊗[R] H) ⊗[R] (H ⊗[R] R) )
  ∘ₗ
  ( map (assoc_inv H H H) id : (H ⊗[R] (H ⊗[R] H)) ⊗[R] R →ₗ[R] ((H ⊗[R] H) ⊗[R] H) ⊗[R] R )
  ∘ₗ
  ( assoc_inv H (H ⊗[R] H) R : H ⊗[R] ((H ⊗[R] H) ⊗[R] R) →ₗ[R] (H ⊗[R] (H ⊗[R] H)) ⊗[R] R )
  ∘ₗ
  ( map id (map comul id) : H ⊗[R] (H ⊗[R] R) →ₗ[R] H ⊗[R] ((H ⊗[R] H) ⊗[R] R) )

noncomputable abbrev step1 : H ⊗[R] H →ₗ[R] H :=
  ( mul : H ⊗[R] H →ₗ[R] H )
  ∘ₗ
  ( map id unit : H ⊗[R] R →ₗ[R] H ⊗[R] H )
  ∘ₗ
  ( map lhs (unitor_left R) : (H ⊗[R] H) ⊗[R] (R ⊗[R] R) →ₗ[R] H ⊗[R] R )
  ∘ₗ
  step1a
  ∘ₗ
  ( map id (map id counit) : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] (H ⊗[R] R) )
  ∘ₗ
  mapA

lemma lhs_to_step1_aux1 :
  ( map id (map id counit) : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] (H ⊗[R] R) )
  ∘ₗ ( mapA : H ⊗[R] H →ₗ[R] H ⊗[R] (H ⊗[R] H) )
  =
  ( map id (unitor_right_inv H) : H ⊗[R] H →ₗ[R] H ⊗[R] (H ⊗[R] R) )
  := by
  calc
  ( map id (map id counit) : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] (H ⊗[R] R) )
  ∘ₗ mapA
  =
  (( map id (TensorProduct.comm R R H) : H ⊗[R] (R ⊗[R] H) →ₗ[R] H ⊗[R] (H ⊗[R] R) )
  ∘ₗ
  ( map id (map counit id) : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] (R ⊗[R] H) ))
  ∘ₗ
  ( assoc H H H : (H ⊗[R] H) ⊗[R] H →ₗ[R] H ⊗[R] (H ⊗[R] H) )
  ∘ₗ
  ( map comul id : H ⊗[R] H →ₗ[R] (H ⊗[R] H) ⊗[R] H )
      := by
        unfold mapA
        rw [← map_comp]
        rw [← map_comp_comm_eq]
        rw [map_comp]
        simp [comp_assoc]
  _ =
  ( map id (unitor_right_inv H) : H ⊗[R] H →ₗ[R] H ⊗[R] (H ⊗[R] R) )
      := sorry

lemma lhs_to_step1 : (lhs = (step1 : H ⊗[R] H →ₗ[R] H))
  := by
  unfold lhs step1
  sorry

noncomputable abbrev mapB : H ⊗[R] H →ₗ[R] H := sorry

noncomputable abbrev step2 : H ⊗[R] H →ₗ[R] H := sorry

lemma step1_to_step2 : (step1 = (step2 : H ⊗[R] H →ₗ[R] H))
  := by
  sorry

-- etc

noncomputable abbrev step11 : H ⊗[R] H →ₗ[R] H := sorry

noncomputable abbrev rhs : H ⊗[R] H →ₗ[R] H :=
  (anti : H →ₗ[R] H)
  ∘ₗ
  (mul : H ⊗[R] H →ₗ[R] H)
  ∘ₗ
  (TensorProduct.comm R H H : H ⊗[R] H →ₗ[R] H ⊗[R] H)

lemma step11_to_rhs : (step11 = (rhs : H ⊗[R] H →ₗ[R] H))
  := by
  sorry

theorem Antipode_mul :
  (mul : H ⊗[R] H →ₗ[R] H)
  ∘ₗ
  (map anti anti : H ⊗[R] H →ₗ[R] H ⊗[R] H)
  =
  (anti : H →ₗ[R] H)
  ∘ₗ
  (mul : H ⊗[R] H →ₗ[R] H)
  ∘ₗ
  (TensorProduct.comm R H H : H ⊗[R] H →ₗ[R] H ⊗[R] H)
:= by
calc
  (mul : H ⊗[R] H →ₗ[R] H)
  ∘ₗ (map anti anti : H ⊗[R] H →ₗ[R] H ⊗[R] H)
  = lhs := by unfold lhs; rfl
  _ = step1 := lhs_to_step1
  _ = step2 := step1_to_step2
-- etc
  _ = step11 := by sorry
  _ = rhs := step11_to_rhs
  _ = anti ∘ₗ mul ∘ₗ (TensorProduct.comm R H H)
    := by unfold rhs; rfl


theorem Antipode_comul :
  (comul : H →ₗ[R] H ⊗[R] H)
  ∘ₗ
  (anti : H →ₗ[R] H)
  =
  (map anti anti : H ⊗[R] H →ₗ[R] H ⊗[R] H)
  ∘ₗ
  (TensorProduct.comm R H H : H ⊗[R] H →ₗ[R] H ⊗[R] H)
  ∘ₗ
  (comul : H →ₗ[R] H ⊗[R] H)
  := by
    sorry

end Work_in_progress_needs_a_different_approach

end AntipodeProperties
