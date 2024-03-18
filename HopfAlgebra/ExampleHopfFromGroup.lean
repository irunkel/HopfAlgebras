import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HopfAlgebra.Basic

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

#check range 4

#check Finset.sum s f
#check Finset.prod s f
open BigOperators
open Finset
example : s.sum f = ∑ x in s, f x := rfl

example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

open scoped TensorProduct
open Hopf

namespace FunctionsOnGroup

variable {G : Type} [Group G] [Finite G] [DecidableEq G]
variable {K : Type} [CommRing K]

abbrev Fun
  := G → K

variable (k : Type*) [CommSemiring k]

instance : Group G := inferInstanceAs

#check inferInstanceAs (Inhabited Nat)

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The average of all elements of the group `G`, considered as an element of `MonoidAlgebra k G`.
-/
noncomputable def average : MonoidAlgebra k G :=
  ⅟ (Fintype.card G : k) • ∑ g : G, of k G g
#align group_algebra.average GroupAlgebra.average


def ss : Finset G := sorry

noncomputable def βK : Basis (Fin 1) K K
  := Basis.singleton (Fin 1) K

noncomputable def β : Basis G K (@Fun G K)
  := Pi.basisFun K G

noncomputable def ββ : Basis (Prod G G) K ((@Fun G K) ⊗[K] (@Fun G K))
  := Basis.tensorProduct β β

noncomputable def βββ : Basis ((G × G) × G) K
  (((@Fun G K) ⊗[K] (@Fun G K)) ⊗[K] (@Fun G K))
  := Basis.tensorProduct ββ β

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

#check Finset G

example : ∑ x in G, (1:Nat) = 0 := sorry

noncomputable def Fun_unit_el_bas : (@Fun G K)
  := ∑ x in (Finset G), β x

#check fun (_: Fin 1) ↦ Fun_unit_el

noncomputable def Fun_unit : K →ₗ[K] (@Fun G K) :=
  Basis.constr βK K (fun (_: Fin 1) ↦ Fun_unit_el)

theorem Fun_one_mul :
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (LinearMap.rTensorHom Fun Fun_unit : K ⊗[K] (@Fun G K)  →ₗ[K]  (@Fun G K) ⊗[K] (@Fun G K))
    ∘ₗ (unitor_left_inv Fun : (@Fun G K) →ₗ[K] (K ⊗[K] (@Fun G K)))
    =
    (LinearMap.id : (@Fun G K) →ₗ[K] (@Fun G K))
    := by
      apply Basis.ext β
      intro i
      simp [unitor_left_inv,Fun_unit]
      sorry

theorem Fun_mul_one :
    (Fun_mul : (@Fun G K) ⊗[K] (@Fun G K) →ₗ[K] (@Fun G K))
    ∘ₗ (LinearMap.lTensorHom Fun Fun_unit : (@Fun G K) ⊗[K] K  →ₗ[K]  (@Fun G K) ⊗[K] (@Fun G K))
    ∘ₗ (unitor_right_inv Fun :  (@Fun G K) →ₗ[K] ((@Fun G K) ⊗[K] K))
    =
    (LinearMap.id : (@Fun G K) →ₗ[K] (@Fun G K))
    := by
      sorry

noncomputable instance : AlgebraTens K (@Fun G K) where
  mul := Fun_mul
  unit := Fun_unit
  one_mul := Fun_one_mul
  mul_one := Fun_mul_one
  mul_assoc := Fun_mul_assoc

abbrev C4 := Multiplicative (Fin 4)
abbrev FunC4 := @Fun C4 ℚ

#check (3:Fin 4)

#check (β (3:Fin 4) : FunC4)

example : Fun_mul_on_basis ( (3:Fin 4) , (3:Fin 4) ) = (β (3:Fin 4):FunC4) :=
  by
    simp [Fun_mul_on_basis]
    rfl

example : Fun_mul ( (β (3:Fin 4) : FunC4) ⊗[ℚ] (β (3:Fin 4) : FunC4) ) = 0 :=
  by
    sorry

def testinstance (A : Type) [AlgebraTens ℚ C2] : Nat := 0

example : testinstance (Multiplicative (Fin 2)) = 0 := rfl

end FunctionsOnGroup

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
