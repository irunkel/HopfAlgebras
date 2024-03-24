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

/- TODO: tried to make this a "def" but the all basis accesses
   below fail as it seems to forget that Fun is an arrow type
   and I did not manage to show that β g g = 1, should make
   this a question. -/
abbrev Fun := G → K

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

/- TODO: Is there any way to just write Fun rather than always (@Fun G K)?
   It seems to produce "typeclass instance problem is stuck"-/
noncomputable def Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) :=
  Basis.constr ββ K Fun_mul_on_basis

theorem Fun_mul_ββ_lemma  {g h : G} : Fun_mul ((β g) ⊗ₜ[K] (β h)) = Fun_mul_on_basis (g,h)
  := by
    rw [Fun_mul]
    rw [← Basis.tensorProduct_apply, ← ββ]
    simp

theorem Fun_mul_assoc :
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (TensorProduct.map Fun_mul LinearMap.id
        : ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K) →ₗ[K] ((@Fun G K) ⊗[K] (@Fun G K)))
    =
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (TensorProduct.map LinearMap.id Fun_mul
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

theorem Fun_units_agree :
  (Fun_unit_el : @Fun G K) = (Fun_unit_el_bas : @Fun G K)
  := by
    apply funext
    intro g
    rw [Fun_unit_el,Fun_unit_el_bas]
    simp [β]

noncomputable def Fun_unit : K →ₗ[K] (@Fun G K) :=
  Basis.constr βK K (fun (_: Fin 1) ↦ Fun_unit_el_bas)

theorem Fun_one_mul :
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (TensorProduct.map Fun_unit LinearMap.id : K ⊗[K] (@Fun G K)  →ₗ[K]  (@Fun G K) ⊗[K] (@Fun G K))
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
    ∘ₗ (TensorProduct.map LinearMap.id Fun_unit : (@Fun G K) ⊗[K] K  →ₗ[K]  (@Fun G K) ⊗[K] (@Fun G K))
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

-- TODO: should the next two helper theorems not be in the library?
theorem mul_inv_one_iff_eq_inv (g h : G) :
  g * h = 1 ↔ g = h⁻¹
  := by
    apply Iff.intro
    case mp => exact eq_inv_of_mul_eq_one_left
    case mpr => intro a2; rw [a2,mul_left_inv]

theorem mul_inv_one_iff_eq_inv' (g h : G) :
  g * h = 1 ↔ h = g⁻¹
  := by
    apply Iff.intro
    case mp => exact eq_inv_of_mul_eq_one_right
    case mpr => intro a2; rw [a2,mul_right_inv]

theorem Fun_coone_comul :
  (unitor_left Fun : K ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
  ∘ₗ (TensorProduct.map Fun_counit LinearMap.id : (@Fun G K) ⊗[K] (@Fun G K)  →ₗ[K]  K ⊗[K] (@Fun G K))
  ∘ₗ (Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K))
  =
  (LinearMap.id : (@Fun G K) →ₗ[K] (@Fun G K))
  := by
    apply Basis.ext β
    intro g
    simp [Fun_comul,Fun_comul_on_basis,
      Fun_counit,Fun_counit_on_basis,
      unitor_left]
    have : ∀ x:G, (if g*x = 1 then β x⁻¹ else (0:@Fun G K))
      = (if x = g⁻¹ then β g else (0:@Fun G K) )
      := by
        intro x
        cases (eq_or_ne x g⁻¹) with
        | inl a1 => simp [a1]
        | inr a1 =>
            have : g * x ≠ 1 := by
              have a2 : g * x = 1 ↔ x = g⁻¹ := mul_inv_one_iff_eq_inv' g x
              rw [← not_iff_not] at a2
              simp [a2,a1]
            simp [this,a1]
    simp [this]

theorem Fun_comul_coone :
  (unitor_right Fun :  (@Fun G K) ⊗[K] K →ₗ[K] (@Fun G K))
  ∘ₗ (TensorProduct.map LinearMap.id Fun_counit : (@Fun G K) ⊗[K] (@Fun G K)  →ₗ[K]  (@Fun G K) ⊗[K] K)
  ∘ₗ (Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K))
  =
  (LinearMap.id : (@Fun G K) →ₗ[K] (@Fun G K))
  := by
    apply Basis.ext β
    intro g
    simp [unitor_right]
    simp [Fun_comul,Fun_comul_on_basis]
    simp [Fun_counit,Fun_counit_on_basis]

-- TODO: Is that already in the library?
theorem group_sum_shift_left {α : Type} [AddCommMonoid α] (s : G) (f:G → α) :
  ∑ g:G, f g = ∑ g:G, f (s*g)
  := by
    let e := Equiv.mulLeft s
    have a1 (x:G) : e x = s*x := rfl
    apply Eq.symm
    rw [Fintype.sum_equiv e]
    simp [a1]

theorem group_sum_shift_right {α : Type} [AddCommMonoid α] (s : G) (f:G → α) :
  ∑ g:G, f g = ∑ g:G, f (g*s)
  := by
    let e := Equiv.mulRight s
    have a1 (x:G) : e x = x*s := rfl
    apply Eq.symm
    rw [Fintype.sum_equiv e]
    simp [a1]

theorem group_sum_inv {α : Type} [AddCommMonoid α] (f:G → α) :
  ∑ g:G, f g = ∑ g:G, f g⁻¹
  := by
    let e := Equiv.inv G
    have a1 (x:G) : e x = x⁻¹ := rfl
    apply Eq.symm
    rw [Fintype.sum_equiv e]
    simp [a1]

theorem Fun_comul_coassoc :
  (TensorProduct.assoc K (@Fun G K) (@Fun G K) (@Fun G K)
      : ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)))
  ∘ₗ (TensorProduct.map Fun_comul LinearMap.id
      : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K))
  ∘ₗ (Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K))
  =
  (TensorProduct.map LinearMap.id Fun_comul
      : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)))
  ∘ₗ (Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K))
  := by
    apply Basis.ext β
    intro g
    simp [Fun_comul,Fun_comul_on_basis,
      TensorProduct.tmul_sum,TensorProduct.sum_tmul]
    nth_rw 2 [Finset.sum_comm]
    have a1 : ∀ x:G, ∑ y:G, β (g * x * y) ⊗ₜ[K] β y⁻¹
      = (∑ z:G, β (g * z) ⊗ₜ[K] β (z⁻¹ * x)
      : (@Fun G K) ⊗[K] (@Fun G K))
      := by
        intro x
        rw [group_sum_shift_left x⁻¹]
        simp [mul_assoc]
    have a2 : ∀ x:G, ∑ y:G, β (g * x * y) ⊗ₜ[K] β y⁻¹ ⊗ₜ[K] β x⁻¹
      = (∑ z:G, β (g * z) ⊗ₜ[K] β (z⁻¹ * x) ⊗ₜ[K] β x⁻¹
      : (@Fun G K) ⊗[K] (@Fun G K) ⊗[K] (@Fun G K))
      := by
        intro x
        have : (TensorProduct.assoc K (@Fun G K) (@Fun G K) (@Fun G K))
                  ( (∑ y:G, β (g * x * y) ⊗ₜ[K] β y⁻¹) ⊗ₜ[K] β x⁻¹ )
                = (TensorProduct.assoc K (@Fun G K) (@Fun G K) (@Fun G K))
                  ( (∑ z:G, β (g * z) ⊗ₜ[K] β (z⁻¹ * x)) ⊗ₜ[K] β x⁻¹ )
          := by simp [a1]
        simp [TensorProduct.sum_tmul] at this
        simp [this]
    simp [a2]

noncomputable instance : CoalgebraTens K (@Fun G K) where
  comul := Fun_comul
  counit := Fun_counit
  coone_comul := Fun_coone_comul
  comul_coone := Fun_comul_coone
  comul_coassoc := Fun_comul_coassoc


/- --- Hopf algebra structure on function algebra --- -/

noncomputable def Fun_anti_on_basis : G → (@Fun G K) := fun g ↦
  β g⁻¹

noncomputable def Fun_anti : (@Fun G K) →ₗ[K] (@Fun G K) :=
  Basis.constr β K Fun_anti_on_basis

theorem tensor_right_if (g:G) (a b : G → (@Fun G K)) :
  ∀ h:G , (a h) ⊗ₜ[K] (if g=h then (b h) else 0)
            = if g=h then (a g) ⊗ₜ[K] (b g) else 0
  := by
    intro h
    cases (eq_or_ne g h) with
    | inl a2 => simp [a2]
    | inr a2 => simp [a2]

-- TODO: This is way too complicated, try to split into easier statements
theorem Fun_comul_mul :
  ( mulAA : ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( TensorProduct.map Fun_comul Fun_comul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] ((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] ((@Fun G K) ⊗[K] (@Fun G K)) )
  =
  ( Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
  := by
    apply Basis.ext ββ
    intro (g,h)
    simp [Fun_mul]
    simp [Fun_mul_on_basis]
    simp [Fun_comul,ββ,Fun_comul_on_basis]
    simp [TensorProduct.sum_tmul]
    simp [TensorProduct.tmul_sum]
    simp [mulAA_tmul]
    simp [AlgebraTens.mul,Fun_mul_ββ_lemma,Fun_mul_on_basis]
    nth_rw 3 [β]
    nth_rw 3 [β]
    have a1 : ∀ x:G , ∑ z:G, (if g * x = h * z then β (g * x) else 0)
        ⊗ₜ[K] (if x = z then β x⁻¹ else 0)
        = (if g=h then β (g * x) ⊗ₜ[K] β x⁻¹ else 0 : (@Fun G K) ⊗[K] (@Fun G K))
      := by
        intro x
        have : ∀ z:G, (if g * x = h * z then β (g * x) else 0) ⊗ₜ[K] (if x = z then β x⁻¹ else 0)
          = (if z=x then (if g * x = h * z then β (g * x) else 0) ⊗ₜ[K] β x⁻¹ else (0 : (@Fun G K) ⊗[K] (@Fun G K)) )
          := by
            intro z
            rw [tensor_right_if x (fun z ↦ (if g * x = h * z then β (g * x) else 0)) (fun _ ↦ β x⁻¹ : G → @Fun G K)]
            cases (eq_or_ne z x) with
            | inl a2 => simp [a2]
            | inr a2 =>
                simp [a2]
                have : x ≠ z := Ne.symm a2
                simp [this]
        simp [this]
        cases (eq_or_ne g h) with
        | inl a2 => simp [a2]
        | inr a2 => simp [a2]
    simp [a1]
    cases (eq_or_ne g h) with
    | inl a2 => simp [a2]
    | inr a2 => simp [a2]

theorem Fun_comul_unit :
  ( Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( Fun_unit : K →ₗ[K] (@Fun G K) )
  =
  ( (TensorProduct.map Fun_unit Fun_unit) : K ⊗[K] K →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( unitor_left_inv K : K →ₗ[K] K⊗[K] K )
  := by
    apply Basis.ext βK
    intro i
    rw [βK,Basis.singleton_apply]
    simp [unitor_left_inv]
    simp [Fun_unit,Fun_unit_el_bas,βK]
    simp [Fun_comul,Fun_comul_on_basis]
    simp [TensorProduct.sum_tmul,TensorProduct.tmul_sum]
    nth_rw 1 [Finset.sum_comm]
    nth_rw 1 [group_sum_inv]
    simp
    have : ∀ x:G, ∑ z : G, β (z * x⁻¹) ⊗ₜ[K] β x
      = ∑ w : G, (β w ⊗ₜ[K] β x : (@Fun G K) ⊗[K] (@Fun G K))
      := by
        intro x
        rw [group_sum_shift_right x]
        simp
    simp [this]

theorem Fun_counit_mul :
  ( Fun_counit : (@Fun G K) →ₗ[K] K )
  ∘ₗ
  ( Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
  =
  ( unitor_left K : K ⊗[K] K →ₗ[K] K )
  ∘ₗ
  ( (TensorProduct.map Fun_counit Fun_counit) : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] K ⊗[K] K )
  := by
    apply Basis.ext ββ
    intro (g,h)
    simp [Fun_mul]
    simp [Fun_mul_on_basis] -- If one combines this with the privous one it introduces a sum for some reason
    simp [Fun_counit,Fun_counit_on_basis]
    simp [β,ββ,unitor_left,Fun_counit,Fun_counit_on_basis]
    cases (eq_or_ne g 1) with
    | inl a1 =>
        simp [a1]
        cases (eq_or_ne h 1) with
        | inl a2 => simp [a2]
        | inr a2 =>
            have : 1 ≠ h := by exact Ne.symm a2 -- Why oh why does the simplifier not see this?
            simp [a2,this]
    | inr a1 =>
        simp [a1]
        cases (eq_or_ne h 1) with
        | inl a2 => simp [a1,a2]
        | inr a2 =>
            cases (eq_or_ne g h) with
            | inl a3 => simp [a3,a2]
            | inr a3 => simp [a3]

theorem Fun_counit_unit :
  ( Fun_counit : (@Fun G K) →ₗ[K] K )
  ∘ₗ
  ( Fun_unit : K →ₗ[K] (@Fun G K) )
  =
  ( LinearMap.id : K →ₗ[K] K )
  := by
    apply Basis.ext βK
    intro i
    simp [βK,Fun_unit,Fun_unit_el_bas,
      Fun_counit,Fun_counit_on_basis]

theorem Fun_anti_left :
  ( Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) )
  ∘ₗ
  ( TensorProduct.map LinearMap.id Fun_anti : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  =
  ( Fun_unit : K →ₗ[K] (@Fun G K) )
  ∘ₗ
  ( Fun_counit : (@Fun G K) →ₗ[K] K )
  := by
    apply Basis.ext β
    intro g
    simp [Fun_comul,Fun_comul_on_basis,
      Fun_anti,Fun_anti_on_basis,
      Fun_mul_ββ_lemma,Fun_mul_on_basis]
    simp [Fun_counit,Fun_counit_on_basis,
      Fun_unit,Fun_unit_el_bas,βK]
    cases (eq_or_ne g 1) with
    | inl a1 => simp [a1]
    | inr a1 => simp [a1]

theorem Fun_anti_right :
  ( Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) )
  ∘ₗ
  ( TensorProduct.map Fun_anti LinearMap.id : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  ∘ₗ
  ( Fun_comul : (@Fun G K) →ₗ[K] (@Fun G K) ⊗[K] (@Fun G K) )
  =
  ( Fun_unit : K →ₗ[K] (@Fun G K) )
  ∘ₗ
  ( Fun_counit : (@Fun G K) →ₗ[K] K )
  := by
    apply Basis.ext β
    intro g
    simp [Fun_comul,Fun_comul_on_basis,
      Fun_anti,Fun_anti_on_basis,
      Fun_mul_ββ_lemma,Fun_mul_on_basis]
    simp [Fun_counit,Fun_counit_on_basis,
      Fun_unit,Fun_unit_el_bas,βK]
    cases (eq_or_ne g 1) with
    | inl a1 => simp [a1]; rw [group_sum_inv]; simp
    | inr a1 => simp [a1]

noncomputable instance : BialgebraTens K (@Fun G K) where
  comul_mul := Fun_comul_mul
  comul_unit := Fun_comul_unit
  counit_mul := Fun_counit_mul
  counit_unit := Fun_counit_unit

open AlgebraTens CoalgebraTens

noncomputable instance : HopfAlgebraTens K (@Fun G K) where
  anti := Fun_anti
  hasAntipodeProp :=
  {
    left := by
      simp [mul,comul,unit,counit]; rw[Fun_anti_left]
    right := by
      simp [mul,comul,unit,counit]; rw[Fun_anti_right]
  }


/- --- Function algebra for C2 as an example --- -/

--def C2 := Multiplicative (Fin 2) -- tried this but could not get it to work

inductive C2 where
| e : C2
| m : C2
deriving DecidableEq, Repr

def isEquivFin2 : Equiv C2 (Fin 2) :=
  {
    toFun := fun x ↦ match x with
      | C2.e => 0
      | C2.m => 1
    invFun := fun x ↦ match x with
      | 0 => C2.e
      | 1 => C2.m
    left_inv := by intro x; cases x <;> rfl
    right_inv := by
      intro x
      match x with
      | 0 => rfl
      | 1 => rfl
  }

instance : Finite C2 := Finite.intro isEquivFin2

instance : Group C2 where
  mul := fun a b ↦
    match a,b with
    | C2.e,x => x
    | x,C2.e => x
    | C2.m,C2.m => C2.e

  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl

  one := C2.e

  one_mul := by
    intro a
    cases a <;> rfl

  mul_one := by
    intro a
    cases a <;> rfl

  inv := id

  mul_left_inv := by
    intro a
    cases a <;> rfl

example : C2.m * C2.m = C2.e := rfl

abbrev FunC2 := @Fun C2 ℚ

open HopfAlgebraTens AlgebraTens CoalgebraTens

#check ( (β C2.m) : FunC2 )

example : mul ( (β C2.m) ⊗ₜ[ℚ] (β C2.m) ) = ( (β C2.m) : FunC2 ) :=
  by simp [mul,Fun_mul_ββ_lemma,Fun_mul_on_basis]

example : mul ( (β C2.e) ⊗ₜ[ℚ] (β C2.m) ) = ( 0 : FunC2 ) :=
  by simp [mul,Fun_mul_ββ_lemma,Fun_mul_on_basis]

-- TODO: this cannot be the easiest way to do this
theorem sumC2 {α:Type} [AddCommMonoid α] (f : C2 → α):
  ∑ h : C2 , f h = f C2.e + f C2.m
  := by
    have a1 : ({C2.e,C2.m} : Finset C2) = Finset.univ := by
      ext x
      simp
      match x with
      | C2.e => left; rfl
      | C2.m => right; rfl
    rw [← a1,Finset.sum_pair ((by simp) : C2.e ≠ C2.m)]

example : comul ( (β C2.m : FunC2) )
  = (
      (β C2.e) ⊗ₜ[ℚ] (β C2.m)
      +
      (β C2.m) ⊗ₜ[ℚ] (β C2.e)
      : FunC2 ⊗[ℚ] FunC2 )
  := by
    simp [comul,Fun_comul,Fun_comul_on_basis]
    rw [sumC2]
    -- simp -- fails: TODO: why does simp not find the computation below?
    calc
    β (C2.m * C2.e) ⊗ₜ[ℚ] β C2.e⁻¹ + β (C2.m * C2.m) ⊗ₜ[ℚ] β C2.m⁻¹
      = β C2.m ⊗ₜ[ℚ] β C2.e + β C2.e ⊗ₜ[ℚ] β C2.m := by rfl
    _ = β C2.e ⊗ₜ[ℚ] β C2.m + β C2.m ⊗ₜ[ℚ] β C2.e := by rw [add_comm]

end FunctionsOnGroup
