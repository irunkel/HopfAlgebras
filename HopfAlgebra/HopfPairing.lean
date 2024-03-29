import Mathlib.LinearAlgebra.TensorProduct.Basic
import HopfAlgebra.Basic

namespace HopfPairing

variable {R:Type} [CommSemiring R]

open LinearMap TensorProduct Hopf AlgebraTens CoalgebraTens HopfAlgebraTens

-- the canonical pairing on R ⊗ R → R
noncomputable def ωR : R ⊗[R] R →ₗ[R] R := unitor_left R

/- the pairing (A⊗A) ⊗ (B⊗B) → R (inner with
   inner and outer with outer) -/
noncomputable def sq
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  :
  (A ⊗[R] A) ⊗[R] (B ⊗[R] B) →ₗ[R] R
  :=
  ( ω : A ⊗[R] B →ₗ[R] R )
  ∘ₗ
  ( map (unitor_right A) id : (A ⊗[R] R) ⊗[R] B →ₗ[R] A ⊗[R] B )
  ∘ₗ
  ( map (map id ω) id : (A ⊗[R] (A ⊗[R] B)) ⊗[R] B →ₗ[R] (A ⊗[R] R) ⊗[R] B )
  ∘ₗ
  ( map (assoc A A B) id : ((A ⊗[R] A) ⊗[R] B) ⊗[R] B →ₗ[R] (A ⊗[R] (A ⊗[R] B)) ⊗[R] B )
  ∘ₗ
  ( assoc_inv (A ⊗[R] A) B B : (A ⊗[R] A) ⊗[R] (B ⊗[R] B) →ₗ[R] ((A ⊗[R] A) ⊗[R] B) ⊗[R] B )

variable  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  (a1 a2 : A) (b1 b2 : B)

theorem sq_tmul
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  (a1 a2 : A) (b1 b2 : B)
  :
  (sq ω) ( (a1 ⊗ₜ[R] a2) ⊗ₜ[R] (b1 ⊗ₜ[R] b2) )
  = (ω (a1 ⊗ₜ[R] b2)) * (ω (a2 ⊗ₜ[R] b1))
  := by
    unfold sq
    simp [TensorProduct.smul_tmul]
    rw [mul_comm]

structure Pairing
  (A B:Type)
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [BialgebraTens R A] [BialgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
where

  unitA_counitB :
    ( ω : A ⊗[R] B →ₗ[R] R )
    ∘ₗ ( map unit id : R ⊗[R] B →ₗ[R] A ⊗[R] B )
    =
    ( ωR : R ⊗[R] R →ₗ[R] R )
    ∘ₗ ( map id counit : R ⊗[R] B →ₗ[R] R ⊗[R] R )

  counitA_unitB :
    ( ωR : R ⊗[R] R →ₗ[R] R )
    ∘ₗ ( map counit id : A ⊗[R] R →ₗ[R] R ⊗[R] R )
    =
    ( ω : A ⊗[R] B →ₗ[R] R )
    ∘ₗ ( map id unit : A ⊗[R] R →ₗ[R] A ⊗[R] B )

  mulA_comulB :
    ( ω : A ⊗[R] B →ₗ[R] R )
    ∘ₗ ( map mul id : (A ⊗[R] A) ⊗[R] B →ₗ[R] A ⊗[R] B )
    =
    ( sq ω : (A ⊗[R] A) ⊗[R] (B ⊗[R] B) →ₗ[R] R )
    ∘ₗ ( map id comul : (A ⊗[R] A) ⊗[R] B →ₗ[R] (A ⊗[R] A) ⊗[R] (B ⊗[R] B) )

  comulA_mulB :
    ( sq ω : (A ⊗[R] A) ⊗[R] (B ⊗[R] B) →ₗ[R] R )
    ∘ₗ ( map comul id : A ⊗[R] (B ⊗[R] B) →ₗ[R] (A ⊗[R] A) ⊗[R] (B ⊗[R] B) )
    =
    ( ω : A ⊗[R] B →ₗ[R] R )
    ∘ₗ ( map id mul : A ⊗[R] (B ⊗[R] B) →ₗ[R] A ⊗[R] B )

/- See Klimyk, Schmudgen, Quantum groups and their representations (Springer 1997),
   Sec 1.2.5 Prop. 9 -/

section Auxilliary
namespace PairingAntipode

noncomputable def reass :=
  ( assoc ((A ⊗[R] A) ⊗[R] A) B (B ⊗[R] B) : (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) ⊗[R] (B ⊗[R] B) →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) )
  ∘ₗ ( assoc (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) B B : ((((A ⊗[R] A) ⊗[R] A) ⊗[R] B) ⊗[R] B) ⊗[R] B →ₗ[R] (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) ⊗[R] (B ⊗[R] B) )

noncomputable def reass_inv :=
  ( assoc_inv (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) B B : (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) ⊗[R] (B ⊗[R] B) →ₗ[R] ((((A ⊗[R] A) ⊗[R] A) ⊗[R] B) ⊗[R] B) ⊗[R] B )
  ∘ₗ ( assoc_inv ((A ⊗[R] A) ⊗[R] A) B (B ⊗[R] B) : ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) →ₗ[R] (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) ⊗[R] (B ⊗[R] B) )

lemma reass_is_inv :
  reass ∘ₗ reass_inv
  = (LinearMap.id : ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) )
  := by
    simp [reass,reass_inv]
    calc
      (assoc ((A ⊗[R] A) ⊗[R] A) B (B ⊗[R] B) ∘ₗ assoc (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) B B)
      ∘ₗ assoc_inv (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) B B ∘ₗ assoc_inv ((A ⊗[R] A) ⊗[R] A) B (B ⊗[R] B)
      =
      assoc ((A ⊗[R] A) ⊗[R] A) B (B ⊗[R] B) ∘ₗ (assoc (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) B B
      ∘ₗ assoc_inv (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) B B) ∘ₗ assoc_inv ((A ⊗[R] A) ⊗[R] A) B (B ⊗[R] B)
          := by simp only [comp_assoc]
      _ =
      LinearMap.id := by simp

noncomputable def H3r
  (C : Type)
  [AddCommMonoid C]
  [Module R C]
  [HopfAlgebraTens R C]
  : C →ₗ[R] C ⊗[R] (C ⊗[R] C)
  :=
  ( map id comul : C ⊗[R] C →ₗ[R] C ⊗[R] (C ⊗[R] C) )
  ∘ₗ ( map anti id : C ⊗[R] C →ₗ[R] C ⊗[R] C )
  ∘ₗ ( comul : C →ₗ[R] C ⊗[R] C )

noncomputable def H3l
  (C : Type)
  [AddCommMonoid C]
  [Module R C]
  [HopfAlgebraTens R C]
  : C →ₗ[R] (C ⊗[R] C) ⊗[R] C
  :=
  ( map (map anti id) id : (C ⊗[R] C) ⊗[R] C →ₗ[R] (C ⊗[R] C) ⊗[R] C )
  ∘ₗ ( map comul id : C ⊗[R] C →ₗ[R] (C ⊗[R] C) ⊗[R] C )
  ∘ₗ ( comul : C →ₗ[R] C ⊗[R] C )

lemma auxH3
  (C : Type)
  [AddCommMonoid C]
  [Module R C]
  [HopfAlgebraTens R C]
  :
  H3r C
  =
  (assoc C C C : (C ⊗[R] C) ⊗[R] C →ₗ[R] C ⊗[R] (C ⊗[R] C) )
  ∘ₗ ( H3l C )
  := by
  calc
  ( map id comul ) ∘ₗ ( map anti id ) ∘ₗ comul
    = (( map (id ∘ₗ anti) (comul ∘ₗ id) )) ∘ₗ comul := by rw [map_comp]; simp [comp_assoc]
  _ = (( map (anti ∘ₗ id) (id ∘ₗ comul) )) ∘ₗ comul := by simp
  _ = ( map anti id ) ∘ₗ ( map id comul ) ∘ₗ comul := by rw [map_comp]; simp [comp_assoc]
  _ = (( map anti (map id id) ) ∘ₗ (assoc C C C )) ∘ₗ ( map comul id ) ∘ₗ comul
        := by rw[← comul_coassoc]; simp [comp_assoc]
  _ = (assoc C C C) ∘ₗ ( map (map anti id) id ) ∘ₗ (map comul id ) ∘ₗ comul
        := by rw [assoc_nat]; simp [comp_assoc]

noncomputable def om3a
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [HopfAlgebraTens R A] [HopfAlgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  :=
    ( ω : A ⊗[R] B →ₗ[R] R )
    ∘ₗ ( map (unitor_right A) id : (A ⊗[R] R) ⊗[R] B →ₗ[R] A ⊗[R] B )
    ∘ₗ ( map (map id (sq ω)) id : (A ⊗[R] ((A ⊗[R] A) ⊗[R] (B ⊗[R] B))) ⊗[R] B →ₗ[R] (A ⊗[R] R) ⊗[R] B )
    ∘ₗ ( map (assoc A (A ⊗[R] A) (B ⊗[R] B)) id : ((A ⊗[R] (A ⊗[R] A)) ⊗[R] (B ⊗[R] B)) ⊗[R] B →ₗ[R] (A ⊗[R] ((A ⊗[R] A) ⊗[R] (B ⊗[R] B))) ⊗[R] B )
    ∘ₗ ( assoc_inv (A ⊗[R] (A ⊗[R] A)) (B ⊗[R] B) B : (A ⊗[R] (A ⊗[R] A)) ⊗[R] ((B ⊗[R] B) ⊗[R] B) →ₗ[R] ((A ⊗[R] (A ⊗[R] A)) ⊗[R] (B ⊗[R] B)) ⊗[R] B )

noncomputable def om3b
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [HopfAlgebraTens R A] [HopfAlgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  :=
    ( sq ω : (A ⊗[R] A) ⊗[R] (B ⊗[R] B) →ₗ[R] R )
    ∘ₗ ( map (unitor_right (A ⊗[R] A)) id : ((A ⊗[R] A) ⊗[R] R) ⊗[R] (B ⊗[R] B) →ₗ[R] (A ⊗[R] A) ⊗[R] (B ⊗[R] B) )
    ∘ₗ ( map (map id ω) id : ((A ⊗[R] A) ⊗[R] (A ⊗[R] B)) ⊗[R] (B ⊗[R] B) →ₗ[R] ((A ⊗[R] A) ⊗[R] R) ⊗[R] (B ⊗[R] B) )
    ∘ₗ ( map (assoc (A ⊗[R] A) A B) id : (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) ⊗[R] (B ⊗[R] B) →ₗ[R] ((A ⊗[R] A) ⊗[R] (A ⊗[R] B)) ⊗[R] (B ⊗[R] B) )
    ∘ₗ ( assoc_inv ((A ⊗[R] A) ⊗[R] A) B (B ⊗[R] B) : ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) →ₗ[R] (((A ⊗[R] A) ⊗[R] A) ⊗[R] B) ⊗[R] (B ⊗[R] B) )

lemma om3aom3b
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [HopfAlgebraTens R A] [HopfAlgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  : (om3a ω) ∘ₗ (map (assoc A A A) (assoc_inv B B B)) = (om3b ω) :=
  by
    have : (om3a ω) ∘ₗ (map (assoc A A A) (assoc_inv B B B)) ∘ₗ reass = (om3b ω) ∘ₗ reass
      := by
        apply TensorProduct.ext
        apply TensorProduct.ext
        apply TensorProduct.ext
        apply TensorProduct.ext
        apply TensorProduct.ext
        ext a1 a2 a3 b1 b2 b3
        simp [reass,om3a,om3b]
        simp [smul_tmul]
        simp [sq_tmul]
        ring
    calc
      (om3a ω) ∘ₗ (map (assoc A A A) (assoc_inv B B B))
        = (om3a ω) ∘ₗ (map (assoc A A A) (assoc_inv B B B)) ∘ₗ reass ∘ₗ reass_inv
            := by rw [reass_is_inv]; simp
      _ = ((om3a ω) ∘ₗ (map (assoc A A A) (assoc_inv B B B)) ∘ₗ reass) ∘ₗ reass_inv
            := by simp [comp_assoc]
      _ = (om3b ω) ∘ₗ reass ∘ₗ reass_inv
            := by rw [this]; simp [comp_assoc]
      _ = (om3b ω) := by rw [reass_is_inv]; simp

lemma aux_om3a
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [HopfAlgebraTens R A] [HopfAlgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  {h : Pairing A B ω}
  :
  (om3a ω) ∘ₗ ( map (map id comul) id )
    = (sq ω) ∘ₗ map (map id id) ((map mul id))
  := by
  calc
  (om3a ω) ∘ₗ ( map (map id comul) id )
  =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map (map id (sq ω)) id )
    ∘ₗ ( map (assoc A (A ⊗[R] A) (B ⊗[R] B)) id )
    ∘ₗ (( assoc_inv (A ⊗[R] (A ⊗[R] A)) (B ⊗[R] B) B )
    ∘ₗ ( map (map id comul) (map id id)) )
        := by simp [om3a,comp_assoc]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map (map id (sq ω)) id )
    ∘ₗ (( map (assoc A (A ⊗[R] A) (B ⊗[R] B)) id )
    ∘ₗ ( map (map (map id comul) id) id ))
    ∘ₗ ( assoc_inv (A ⊗[R] A) (B ⊗[R] B) B )
        := by rw [← assoc_inv_nat]; simp [comp_assoc]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map ((map id (sq ω)) ∘ₗ (assoc A (A ⊗[R] A) (B ⊗[R] B)) ∘ₗ (map (map id comul) id)) (id ∘ₗ id ∘ₗ id) )
    ∘ₗ ( assoc_inv (A ⊗[R] A) (B ⊗[R] B) B )
        := by rw [map_comp,map_comp]; simp [comp_assoc]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map (((map id (sq ω)) ∘ₗ (map id (map comul id))) ∘ₗ (assoc A A (B ⊗[R] B))) (id ∘ₗ id ∘ₗ id) )
    ∘ₗ ( assoc_inv (A ⊗[R] A) (B ⊗[R] B) B )
        := by rw [← assoc_nat]; simp [comp_assoc]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map ((map (id ∘ₗ id) ((sq ω) ∘ₗ (map comul id))) ∘ₗ (assoc A A (B ⊗[R] B))) (id ∘ₗ id ∘ₗ id) )
    ∘ₗ ( assoc_inv (A ⊗[R] A) (B ⊗[R] B) B )
        := by rw [← map_comp]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map ((map (id ∘ₗ id) (ω ∘ₗ (map id mul))) ∘ₗ (assoc A A (B ⊗[R] B))) (id ∘ₗ id ∘ₗ id) )
    ∘ₗ ( assoc_inv (A ⊗[R] A) (B ⊗[R] B) B )
        := by rw [h.comulA_mulB]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map ((map id ω) ∘ₗ (map id (map id mul)) ∘ₗ (assoc A A (B ⊗[R] B))) (id ∘ₗ id ∘ₗ id) )
    ∘ₗ ( assoc_inv (A ⊗[R] A) (B ⊗[R] B) B )
        := by nth_rw 2 [map_comp]; simp [comp_assoc]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map ((map id ω) ∘ₗ (assoc A A B) ∘ₗ (map (map id id) mul)) (id ∘ₗ id ∘ₗ id) )
    ∘ₗ ( assoc_inv (A ⊗[R] A) (B ⊗[R] B) B )
        := by rw [assoc_nat]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map (map id ω) id )
    ∘ₗ ( map (assoc A A B) id )
    ∘ₗ ( map (map (map id id) mul) id )
    ∘ₗ ( assoc_inv (A ⊗[R] A) (B ⊗[R] B) B )
        := by rw [map_comp,map_comp]; simp[comp_assoc]
  _ =
    ω ∘ₗ ( map (unitor_right A) id )
    ∘ₗ ( map (map id ω) id )
    ∘ₗ ( map (assoc A A B) id )
    ∘ₗ ( assoc_inv (A ⊗[R] A) B B )
    ∘ₗ ( map (map id id) ((map mul id)) )
        := by rw [assoc_inv_nat]
  _ = (sq ω) ∘ₗ map (map id id) ((map mul id))
        := by unfold sq; simp [comp_assoc]

lemma aux_om3b
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [HopfAlgebraTens R A] [HopfAlgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  {h : Pairing A B ω}
  :
  (om3b ω) ∘ₗ ( map id (map id comul) )
    = ( (sq ω) ∘ₗ map (map mul id) (map id id)
        : ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] B) →ₗ[R] R)
  := by
  calc
  (om3b ω) ∘ₗ ( map id (map id comul) )
  =
    ( sq ω  )
    ∘ₗ ( map (unitor_right (A ⊗[R] A)) id )
    ∘ₗ ( map (map id ω) id )
    ∘ₗ ( map (assoc (A ⊗[R] A) A B) id  )
    ∘ₗ (( assoc_inv ((A ⊗[R] A) ⊗[R] A) B (B ⊗[R] B) )
    ∘ₗ ( map (map id id) (map id comul)))
        := by simp [om3b,comp_assoc]
  _ =
    ( sq ω  )
    ∘ₗ (( map (unitor_right (A ⊗[R] A)) id )
    ∘ₗ ( map (map id ω) id )
    ∘ₗ ( map (assoc (A ⊗[R] A) A B) id  )
    ∘ₗ ( map (map (map id id) id) comul))
    ∘ₗ ( assoc_inv ((A ⊗[R] A) ⊗[R] A) B B )
        := by rw [← assoc_inv_nat]; simp [comp_assoc]
  _ =
    ( sq ω  )
    ∘ₗ ( map ((unitor_right (A ⊗[R] A)) ∘ₗ (map id ω) ∘ₗ (assoc (A ⊗[R] A) A B)) comul )
    ∘ₗ ( assoc_inv ((A ⊗[R] A) ⊗[R] A) B B )
        := by rw [← map_comp,← map_comp,← map_comp]; simp
  _ =
    ( sq ω  )
    ∘ₗ (( map id comul )
    ∘ₗ ( map ((unitor_right (A ⊗[R] A)) ∘ₗ (map id ω) ∘ₗ (assoc (A ⊗[R] A) A B)) id ))
    ∘ₗ ( assoc_inv ((A ⊗[R] A) ⊗[R] A) B B )
        := by rw [← map_comp]; simp [comp_assoc]
  _ =
    (( ω
    ∘ₗ ( map mul id ))
    ∘ₗ ( map ((unitor_right (A ⊗[R] A)) ∘ₗ (map id ω) ∘ₗ (assoc (A ⊗[R] A) A B)) id ))
    ∘ₗ ( assoc_inv ((A ⊗[R] A) ⊗[R] A) B B )
        := by rw[Pairing.mulA_comulB]; simp [comp_assoc]; exact h
  _ = (sq ω) ∘ₗ map (map mul id) (map id id)
        := by
          have : ( ω ∘ₗ ( map mul id ))
                  ∘ₗ ( map ((unitor_right (A ⊗[R] A)) ∘ₗ (map id ω) ∘ₗ (assoc (A ⊗[R] A) A B)) id )
                = (sq ω) ∘ₗ map (map mul id) (map id id) ∘ₗ ( assoc ((A ⊗[R] A) ⊗[R] A) B B )
                  := by
                    apply TensorProduct.ext
                    apply TensorProduct.ext
                    apply TensorProduct.ext
                    apply TensorProduct.ext
                    ext a1 a2 a3 b1 b2
                    simp [sq,assoc_inv]
          rw [this]
          simp [comp_assoc]

lemma init1_lhs
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [HopfAlgebraTens R A] [HopfAlgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  {h : Pairing A B ω}
  :
  ( (om3a ω) : (A ⊗[R] (A ⊗[R] A)) ⊗[R] ((B ⊗[R] B) ⊗[R] B) →ₗ[R] R )
  ∘ₗ ( map (H3r A) (H3l B) : A ⊗[R] B →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] ((B ⊗[R] B) ⊗[R] B) )
  =
  ( ω : A ⊗[R] B →ₗ[R] R )
  ∘ₗ ( map anti id : A ⊗[R] B →ₗ[R] A ⊗[R] B )
:= by

  have init1_lhs_aux :
    (sq ω) ∘ₗ (map (map id id) (map unit id))
    = ω ∘ₗ (map ((unitor_right A) ∘ₗ (map id counit)) (unitor_left B))
   := by
     apply ext_fourfold'
     intro a1 a2 r b
     simp [unit,sq_tmul,smul_tmul]
     calc
       ω (a1 ⊗ₜ[R] b) * ω (a2 ⊗ₜ[R] unit r)
         = ω (a1 ⊗ₜ[R] b) * ((ω ∘ₗ (map id unit)) (a2 ⊗ₜ[R] r))
             := by simp
       _ = ω (a1 ⊗ₜ[R] b) * ((ω ∘ₗ (map id unit)) (a2 ⊗ₜ[R] r))
             := by simp
       _ = ω (a1 ⊗ₜ[R] b) * ((ωR ∘ₗ (map counit id)) (a2 ⊗ₜ[R] r))
              := by rw [←Pairing.counitA_unitB]; exact h
       _ = r * (counit a2 * ω (a1 ⊗ₜ[R] b))
             := by simp [ωR,unitor_left]; ring

  calc
    (om3a ω) ∘ₗ ( map (H3r A) (H3l B) )
      = (om3a ω) ∘ₗ ( map ((map id comul) ∘ₗ (map anti id) ∘ₗ comul) ((map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) )
          := by simp [H3r,H3l]
    _ = (om3a ω)
        ∘ₗ ( map ((map id comul) ∘ₗ ((map anti id) ∘ₗ comul)) (id ∘ₗ (map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) )
          := by simp [comp_assoc]
    _ = (om3a ω)
        ∘ₗ ( map ((map id comul)) id )
        ∘ₗ ( map (((map anti id) ∘ₗ comul)) ((map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) )
          := by rw [map_comp]
    _ = ((sq ω)
        ∘ₗ map (map id id) (map mul id))
        ∘ₗ ( map ((map anti id) ∘ₗ comul) ((map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) )
          := by rw [← aux_om3a ω]; simp [comp_assoc]; exact h
    _ = (sq ω)
        ∘ₗ ( map (map id id) (map mul id) )
        ∘ₗ ( map ((map anti id) ∘ₗ comul) ((map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) )
          := by simp [comp_assoc]
    _ = (sq ω)
        ∘ₗ (map ((map anti id) ∘ₗ comul) (((map mul id) ∘ₗ (map (map anti id) id) ∘ₗ (map comul id)) ∘ₗ comul))
          := by rw [← map_comp]; simp [comp_assoc]
    _ = (sq ω)
        ∘ₗ (map ((map anti id) ∘ₗ comul) ((map (mul ∘ₗ (map anti id) ∘ₗ comul) id) ∘ₗ comul))
          := by rw [← map_comp,← map_comp]; simp [comp_assoc]
    _ = (sq ω)
        ∘ₗ (map ((map anti id) ∘ₗ comul) ((map (unit ∘ₗ counit) (id ∘ₗ id)) ∘ₗ comul))
          := by rw [hasAntipodeProp.right]; simp
    _ = (sq ω)
        ∘ₗ (map ((map anti id) ∘ₗ comul) ((map unit id) ∘ₗ (map counit id) ∘ₗ comul))
          := by nth_rw 2 [map_comp]; simp [comp_assoc]
    _ = (sq ω)
        ∘ₗ (map ((map id id) ∘ₗ (map anti id) ∘ₗ comul) ((map unit id) ∘ₗ (unitor_left_inv B)))
          := by rw [coone_comul']; simp
    _ = ((sq ω)
        ∘ₗ (map (map id id) (map unit id)))
        ∘ₗ (map ((map anti id) ∘ₗ comul) (unitor_left_inv B))
          := by rw [map_comp]; simp [comp_assoc]
    _ = ω
        ∘ₗ (map ((unitor_right A) ∘ₗ (map id counit)) (unitor_left B))
        ∘ₗ (map ((map anti id) ∘ₗ comul) (unitor_left_inv B))
          := by rw [init1_lhs_aux]; simp [comp_assoc]
    _ = ω
        ∘ₗ (map ((unitor_right A) ∘ₗ ((map id counit) ∘ₗ (map anti id)) ∘ₗ comul) ((unitor_left B) ∘ₗ (unitor_left_inv B)))
          := by rw [← map_comp]; simp [comp_assoc]
    _ = ω
        ∘ₗ (map ((unitor_right A) ∘ₗ ((map anti id) ∘ₗ (map id counit)) ∘ₗ comul) id)
          := by rw [←map_comp, ←map_comp]; simp
    _ = ω
        ∘ₗ (map (((unitor_right A) ∘ₗ (map anti id)) ∘ₗ (map id counit) ∘ₗ comul) id)
          := by simp [comp_assoc]
    _ = ω
        ∘ₗ (map (anti ∘ₗ (unitor_right A) ∘ₗ (unitor_right_inv A)) id)
          := by rw [unitor_right_nat,comul_coone']; simp [comp_assoc]
    _ = ω ∘ₗ ( map anti id ) := by simp


lemma init2_rhs
  {A B : Type}
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [HopfAlgebraTens R A] [HopfAlgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  {h : Pairing A B ω}
  :
  ( (om3b ω) : ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) →ₗ[R] R )
  ∘ₗ ( map (H3l A) (H3r B) : A ⊗[R] B →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) )
  =
  ( ω : A ⊗[R] B →ₗ[R] R )
  ∘ₗ ( map id anti : A ⊗[R] B →ₗ[R] A ⊗[R] B )
  := by

  have init2_rhs_aux :
   (sq ω) ∘ₗ (map (map unit id) (map id id))
   = ω ∘ₗ (map (unitor_left A) ((unitor_right B) ∘ₗ (map id counit)))
   := by
     apply ext_fourfold'
     intro r a b1 b2
     simp [unit,sq_tmul,smul_tmul]
     calc
       ω (unit r ⊗ₜ[R] b2) * ω (a ⊗ₜ[R] b1)
         = ((ω ∘ₗ (map unit id)) (r ⊗ₜ[R] b2)) * ω (a ⊗ₜ[R] b1)
             := by simp
       _ = ((ωR ∘ₗ (map id counit)) (r ⊗ₜ[R] b2)) * ω (a ⊗ₜ[R] b1)
             := by rw [Pairing.unitA_counitB]; exact h
       _ = counit b2 * (r * ω (a ⊗ₜ[R] b1))
             := by simp [ωR,unitor_left]; ring
  calc
    (om3b ω) ∘ₗ ( map (H3l A) (H3r B) )
      = (om3b ω) ∘ₗ ( map ((map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) ((map id comul) ∘ₗ (map anti id) ∘ₗ comul) )
          := by simp [H3r,H3l]
    _ = (om3b ω)
        ∘ₗ ( map (id ∘ₗ (map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) ((map id comul) ∘ₗ ((map anti id) ∘ₗ comul)) )
          := by simp [comp_assoc]
    _ = (om3b ω)
        ∘ₗ ( map id ((map id comul)) )
        ∘ₗ ( map ((map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) (((map anti id) ∘ₗ comul)) )
          := by rw [map_comp]
    _ = ((sq ω)
        ∘ₗ map (map mul id) (map id id))
        ∘ₗ ( map ((map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) ((map anti id) ∘ₗ comul) )
          := by rw [← aux_om3b ω]; simp [comp_assoc]; exact h
    _ = (sq ω)
        ∘ₗ ( map (map mul id) (map id id) )
        ∘ₗ ( map ((map (map anti id) id) ∘ₗ (map comul id) ∘ₗ comul) ((map anti id) ∘ₗ comul) )
          := by simp [comp_assoc]
    _ = (sq ω)
        ∘ₗ ( map (((map mul id) ∘ₗ (map (map anti id) id) ∘ₗ (map comul id)) ∘ₗ comul) (((map id id) ∘ₗ (map anti id)) ∘ₗ comul) )
          := by rw [← map_comp]; simp [comp_assoc]
    _ = (sq ω)
        ∘ₗ (map ((map (mul ∘ₗ (map anti id) ∘ₗ comul) id) ∘ₗ comul) ((map anti id) ∘ₗ comul))
          := by rw [← map_comp,← map_comp,← map_comp]; simp [comp_assoc]
    _ = (sq ω)
        ∘ₗ (map ((map (unit ∘ₗ counit) (id ∘ₗ id)) ∘ₗ comul) ((map anti id) ∘ₗ comul))
          := by rw [hasAntipodeProp.right]; simp
    _ = (sq ω)
        ∘ₗ (map ((map unit id) ∘ₗ (map counit id) ∘ₗ comul) ((map anti id) ∘ₗ comul))
          := by nth_rw 2 [map_comp]; simp [comp_assoc]
    _ = (sq ω)
        ∘ₗ (map ((map unit id) ∘ₗ (unitor_left_inv A)) ((map id id) ∘ₗ (map anti id) ∘ₗ comul))
          := by rw [coone_comul']; simp
    _ = ((sq ω)
        ∘ₗ (map (map unit id) (map id id)))
        ∘ₗ (map (unitor_left_inv A) ((map anti id) ∘ₗ comul))
          := by rw [map_comp]; simp [comp_assoc]
    _ = ω
        ∘ₗ (map (unitor_left A) ((unitor_right B) ∘ₗ (map id counit)))
        ∘ₗ (map (unitor_left_inv A) ((map anti id) ∘ₗ comul))
          := by rw [init2_rhs_aux]; simp [comp_assoc]
    _ = ω
        ∘ₗ (map ((unitor_left A) ∘ₗ (unitor_left_inv A)) ((unitor_right B) ∘ₗ ((map id counit) ∘ₗ (map anti id)) ∘ₗ comul))
          := by rw [← map_comp]; simp [comp_assoc]
    _ = ω
        ∘ₗ (map id ((unitor_right B) ∘ₗ ((map anti id) ∘ₗ (map id counit)) ∘ₗ comul))
          := by rw [←map_comp, ←map_comp]; simp
    _ = ω
        ∘ₗ (map id (((unitor_right B) ∘ₗ (map anti id)) ∘ₗ (map id counit) ∘ₗ comul))
          := by simp [comp_assoc]
    _ = ω
        ∘ₗ (map id (anti ∘ₗ (unitor_right B) ∘ₗ (unitor_right_inv B)))
          := by rw [unitor_right_nat,comul_coone']; simp [comp_assoc]
    _ = ω ∘ₗ ( map id anti ) := by simp

end PairingAntipode
end Auxilliary

theorem PairingAntipode
  (A B : Type)
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  [HopfAlgebraTens R A] [HopfAlgebraTens R B]
  (ω : A ⊗[R] B →ₗ[R] R)
  {h : Pairing A B ω}
  :
  ( ω : A ⊗[R] B →ₗ[R] R )
  ∘ₗ ( map anti id : A ⊗[R] B →ₗ[R] A ⊗[R] B )
  =
  ( ω : A ⊗[R] B →ₗ[R] R )
  ∘ₗ ( map id anti : A ⊗[R] B →ₗ[R] A ⊗[R] B )

  := by

let init1 :=
    ( (PairingAntipode.om3a ω) : (A ⊗[R] (A ⊗[R] A)) ⊗[R] ((B ⊗[R] B) ⊗[R] B) →ₗ[R] R )
    ∘ₗ ( map (PairingAntipode.H3r A) (PairingAntipode.H3l B) : A ⊗[R] B →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] ((B ⊗[R] B) ⊗[R] B) )

let init2 :=
    ( (PairingAntipode.om3b ω) : ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) →ₗ[R] R )
    ∘ₗ ( map (PairingAntipode.H3l A) (PairingAntipode.H3r B) : A ⊗[R] B →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) )

have init1_init2 : init1 = init2 :=
  by
    have : assoc_inv B B B ∘ₗ assoc B B B ∘ₗ PairingAntipode.H3l B
           = (PairingAntipode.H3l B : B →ₗ[R] (B ⊗[R] B) ⊗[R] B)
      := by
      calc
        assoc_inv B B B ∘ₗ assoc B B B ∘ₗ PairingAntipode.H3l B
        = (assoc_inv B B B ∘ₗ assoc B B B) ∘ₗ PairingAntipode.H3l B := by simp only [comp_assoc]
        _ = PairingAntipode.H3l B := by simp

    simp [init1,init2]
    rw [← PairingAntipode.om3aom3b]
    simp [comp_assoc]
    rw [← map_comp]
    rw [← PairingAntipode.auxH3 A]
    rw [PairingAntipode.auxH3 B]
    rw [this]

calc
  ω ∘ₗ ( map anti id )
    = (PairingAntipode.om3a ω) ∘ₗ ( map (PairingAntipode.H3r A) (PairingAntipode.H3l B) )
        := by rw [← PairingAntipode.init1_lhs]; exact h
  _ = init1 := by simp
  _ = init2 := init1_init2
  _ = (PairingAntipode.om3b ω) ∘ₗ ( map (PairingAntipode.H3l A) (PairingAntipode.H3r B) )  := by simp
  _ = ω ∘ₗ ( map id anti )
        := by rw [PairingAntipode.init2_rhs]; exact h

end HopfPairing
