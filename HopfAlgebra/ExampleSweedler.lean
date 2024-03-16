import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HopfAlgebra.HopfDefs

namespace SweedlerHopfAlgebra

/- Sweedler's Hopf algebra is 4 dimensional, has a nilpotent
   element x, and a group-like g, so we will use e, x, g, gx
   to denote the basis vectors.
-/
inductive bas where
| e : bas
| x : bas
| g : bas
| gx : bas
deriving DecidableEq

-- provide a proof that bas indeed has 4 elements
def isEquivFin4 : Equiv bas (Fin 4) :=
  {
    toFun := fun x ↦ match x with
      | bas.e => 0
      | bas.x => 1
      | bas.g => 2
      | bas.gx => 3
    invFun := fun x ↦ match x with
      | 0 => bas.e
      | 1 => bas.x
      | 2 => bas.g
      | 3 => bas.gx
    left_inv := by intro x; cases x <;> rfl
    right_inv := by
      -- intro x; cases x <;> rfl
      /- TODO: above does not work, how can
         one avoid matching through all cases? -/
      intro x
      match x with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | 3 => rfl
  }

-- and with that we can declare that bas is finite
instance inst_finite_bas : Finite bas := Finite.intro isEquivFin4

/- TODO: I wanted to do this with my own type via "abbrev sha := bas → ℚ",
   but then it forgets all properties and I was not able to reprove e.g.
   AddCommGroup, eg I failed with zsmul_zero' etc.
-/
abbrev sha := bas → ℚ

-- this turns functions into a basis
noncomputable def β : Basis bas ℚ sha
  := Pi.basisFun ℚ bas

noncomputable abbrev βe  := β bas.e
noncomputable abbrev βx  := β bas.x
noncomputable abbrev βg  := β bas.g
noncomputable abbrev βgx  := β bas.gx


/- It might be better to define algebra from scratch as
   map A ⊗ A → A plus conditions, rather than a ring with
   a map to the centre, which is how it is done in the
   library (which will use semirings instead)
   So let's try.
-/



/-
  basis of the tensor product sha ⊗ sha
  (will use ⊗ below, but want to use full notation at
   least once to start with)
-/
noncomputable def ββ : Basis (Prod bas bas) ℚ (TensorProduct ℚ sha sha)
  := Basis.tensorProduct β β

-- mathlib docu says I should do this to use ⊗
open scoped TensorProduct
open Hopf


/- --- Algebra structure for Sweedler --- -/

-- product of basis vectors
noncomputable def sha_mul_on_basis : bas × bas → sha := fun (a,b) ↦
  match a,b with
  | bas.e,_ => β b
  | _,bas.e => β a
  | bas.x , bas.x => 0
  | bas.x , bas.g => - βgx
  | bas.x , bas.gx => 0
  | bas.g , bas.x => βgx
  | bas.g , bas.g => βe
  | bas.g , bas.gx => βx
  | bas.gx , bas.x => 0
  | bas.gx , bas.g => - βx
  | bas.gx , bas.gx => 0

example : sha_mul_on_basis (bas.e , bas.e) = βe := by rfl

/- and the corresponding linear map on the tensor product
   Note that sha ⊗[ℚ] sha → sha is also accepted here, but then
   the below we cannot use that sha_mul is a linear map.
-/
noncomputable def sha_mul : sha ⊗[ℚ] sha →ₗ[ℚ] sha :=
  Basis.constr ββ ℚ sha_mul_on_basis

theorem sha_mul_ββ_lemma : sha_mul ((β i) ⊗ₜ[ℚ] (β j)) = sha_mul_on_basis (i,j)
  := by
    rw [sha_mul]
    rw [← Basis.tensorProduct_apply, ← ββ]
    simp

/- try it. TensorProduct.tmul R m n gives the tensor product
   on elements, it is abbreviated as m ⊗ₜ[R] n
   The dot •, \bu, is the scalar action. To access it directly
   one has to hunt it down through the type classes
   (just smul or Module.smul does not work), it is hidden
   in SMul. This gives the 2nd version of the rhs below.
-/

example : sha_mul ( βg ⊗ₜ[ℚ] βx - βx ⊗ₜ[ℚ] βg ) = (2:Rat) • βgx
-- the dot is the action of ℚ on sha, in long form: = SMul.smul (2:ℚ) (β bas.gx:sha)
  := by
  calc
  sha_mul ( βg ⊗ₜ[ℚ] βx - βx ⊗ₜ[ℚ] βg )
    = sha_mul ( βg ⊗ₜ[ℚ] βx ) - sha_mul ( βx ⊗ₜ[ℚ] βg ) := by simp
  _ = sha_mul_on_basis ( bas.g , bas.x )
      - sha_mul_on_basis ( bas.x , bas.g )
      := by rw [sha_mul_ββ_lemma,sha_mul_ββ_lemma]
  _ = βgx + βgx := by simp [sha_mul_on_basis]
  _ = (2:Rat) • βgx := by rw [two_smul];
  -- there is a way to make it use "(2:Nat) * vector" directly - TODO

noncomputable def βββ : Basis ((bas × bas) × bas) ℚ ((sha ⊗[ℚ] sha) ⊗[ℚ] sha)
  := Basis.tensorProduct ββ β

theorem tensor_sub_right (a b : sha): a ⊗ₜ[ℚ] (-b) = - (a ⊗ₜ[ℚ] b)
  := by
    calc
      a ⊗ₜ[ℚ] (-b)
        = a ⊗ₜ[ℚ] ((-1) • b) := by simp
      _ = (-1) • (a ⊗ₜ[ℚ] b) := by rw [TensorProduct.tmul_smul]
      _ = - (a ⊗ₜ[ℚ] b) := by simp

theorem tensor_sub_left (a b : sha): (-a) ⊗ₜ[ℚ] b = - (a ⊗ₜ[ℚ] b)
  := by
    calc
      (-a) ⊗ₜ[ℚ] b
        = ((-1) • a) ⊗ₜ[ℚ] b := by simp
      _ = (-1) • (a ⊗ₜ[ℚ] b) := by rw [TensorProduct.smul_tmul']
      _ = - (a ⊗ₜ[ℚ] b) := by simp

theorem sha_mul_assoc :
  (sha_mul
  ∘ₗ (LinearMap.rTensorHom sha sha_mul) :
  (sha ⊗[ℚ] sha) ⊗[ℚ] sha →ₗ[ℚ] sha)
  =
  (sha_mul
  ∘ₗ (LinearMap.lTensorHom sha sha_mul)
  ∘ₗ (TensorProduct.assoc ℚ sha sha sha)
  :
  (sha ⊗[ℚ] sha) ⊗[ℚ] sha →ₗ[ℚ] sha)
  := by
    apply Basis.ext βββ
    intro ⟨ ⟨a,b⟩ , c ⟩
    simp
    rw [βββ,ββ]
    simp [sha_mul_ββ_lemma]
    cases a <;> cases b <;> cases c <;>
      repeat simp [sha_mul_on_basis,sha_mul_ββ_lemma,
        tensor_sub_left,tensor_sub_right];

/-
      ( repeat simp [sha_mul_on_basis];
        repeat simp [sha_mul_ββ_lemma];
        repeat simp [sha_mul_on_basis];
        repeat simp [tensor_sub_left];
        repeat simp [tensor_sub_right];
        repeat simp [sha_mul_ββ_lemma];
        repeat simp [sha_mul_on_basis];
      )
-/
/- surely somewhere there should be R -> M as a linear map
   which takes 1 in R to some basis vector b in M predefined
-/
noncomputable def sha_unit : ℚ →ₗ[ℚ] sha := {
  toFun := fun a ↦ a • βe
  map_add' := by
    intro a b
    simp [add_smul]
  map_smul' := by
    intro a b
    dsimp
    rw [mul_smul (a:Rat) (b:Rat) βe]
  }

noncomputable def sha_g : ℚ →ₗ[ℚ] sha := {
  toFun := fun a ↦ a • βg
  map_add' := by
    intro a b
    simp [add_smul]
  map_smul' := by
    intro a b
    dsimp
    rw [mul_smul (a:Rat) (b:Rat) βg]
  }

--#check (TensorProduct.lid ℚ sha).invFun

/- surely this exists? Ah, is done automatically
   by coersion, but I do not fully understand the
   mechanism. But simp can deal with it then.

theorem linfun_from_linequiv {R:Type u1} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (f : M ≃ₗ[R] N)
  : M →ₗ[R] N := {
    toFun := f.toFun
    map_add' := f.map_add'
    map_smul' := f.map_smul'
  }
-/

theorem sha_one_mul :
  ( (sha_mul : sha ⊗[ℚ] sha →ₗ[ℚ] sha)
  ∘ₗ (LinearMap.rTensorHom sha sha_unit : ℚ ⊗[ℚ] sha  →ₗ[ℚ]  sha ⊗[ℚ] sha)
  ∘ₗ (LinearEquiv.symm (TensorProduct.lid ℚ sha) :  sha →ₗ[ℚ] (ℚ ⊗[ℚ] sha))
  : sha →ₗ[ℚ] sha)
  =
  (LinearMap.id
  : sha →ₗ[ℚ] sha)
  := by
    apply Basis.ext β
    intro i
    simp [sha_unit]
    cases i <;> simp [sha_mul_ββ_lemma,sha_mul_on_basis]

theorem sha_mul_one :
  ( (sha_mul : sha ⊗[ℚ] sha →ₗ[ℚ] sha)
  ∘ₗ (LinearMap.lTensorHom sha sha_unit : sha ⊗[ℚ] ℚ  →ₗ[ℚ]  sha ⊗[ℚ] sha)
  ∘ₗ (LinearEquiv.symm (TensorProduct.rid ℚ sha) :  sha →ₗ[ℚ] (sha ⊗[ℚ] ℚ))
  : sha →ₗ[ℚ] sha)
  =
  (LinearMap.id
  : sha →ₗ[ℚ] sha)
  := by
    apply Basis.ext β
    intro i
    simp [sha_unit]
    cases i <;> simp [sha_mul_ββ_lemma,sha_mul_on_basis]

noncomputable instance : AlgebraTens ℚ sha where
  mul := sha_mul
  unit := sha_unit
  one_mul := sha_one_mul
  mul_one := sha_mul_one
  mul_assoc := sha_mul_assoc

/- --- Coalgebra structure for Sweedler --- -/

noncomputable def sha_comul_on_basis : bas → sha ⊗[ℚ] sha := fun a ↦
  match a with
  | bas.e => βe ⊗ₜ[ℚ] βe
  | bas.x => βe ⊗ₜ[ℚ] βx + βx ⊗ₜ[ℚ] βg
  | bas.g => βg ⊗ₜ[ℚ] βg
  | bas.gx => βg ⊗ₜ[ℚ] βgx + βgx ⊗ₜ[ℚ] βe


noncomputable def sha_comul : sha  →ₗ[ℚ]  sha ⊗[ℚ] sha :=
  Basis.constr β ℚ sha_comul_on_basis

noncomputable def sha_counit_on_basis : bas → ℚ := fun a ↦
  match a with
  | bas.e => 1
  | bas.x => 0
  | bas.g => 1
  | bas.gx => 0

noncomputable def sha_counit : sha  →ₗ[ℚ] ℚ :=
  Basis.constr β ℚ sha_counit_on_basis

example :
  ( mulAA ∘ₗ (tensor_f_g sha_comul sha_comul) ) (βg ⊗ₜ[ℚ] βx)
  = sha_comul βgx
  := by
    simp [tensor_f_g,sha_comul,sha_comul_on_basis,
      TensorProduct.tmul_add,mulAA_tmul,AlgebraTens.mul,
      sha_mul_ββ_lemma,sha_mul_on_basis]


theorem sha_coone_comul  :
  (TensorProduct.lid ℚ sha :  ℚ ⊗[ℚ] sha →ₗ[ℚ] sha)
  ∘ₗ (LinearMap.rTensorHom sha sha_counit : sha ⊗[ℚ] sha  →ₗ[ℚ]  ℚ ⊗[ℚ] sha)
  ∘ₗ (sha_comul : sha →ₗ[ℚ] sha ⊗[ℚ] sha)
  =
  (LinearMap.id : sha →ₗ[ℚ] sha)
  :=
  by
    apply Basis.ext β
    intro i
    simp [sha_comul]
    cases i <;> simp [sha_comul_on_basis,sha_counit,sha_counit_on_basis]

theorem sha_comul_coone :
  (TensorProduct.rid ℚ sha :  sha ⊗[ℚ] ℚ →ₗ[ℚ] sha)
  ∘ₗ (LinearMap.lTensorHom sha sha_counit : sha ⊗[ℚ] sha  →ₗ[ℚ]  sha ⊗[ℚ] ℚ)
  ∘ₗ (sha_comul : sha →ₗ[ℚ] sha ⊗[ℚ] sha)
  =
  (LinearMap.id : sha →ₗ[ℚ] sha)
  :=
  by
    apply Basis.ext β
    intro i
    simp [sha_comul]
    cases i <;> simp [sha_comul_on_basis,sha_counit,sha_counit_on_basis]


theorem sha_comul_coassoc :
  (TensorProduct.assoc ℚ sha sha sha
      : (sha ⊗[ℚ] sha) ⊗[ℚ] sha →ₗ[ℚ] sha ⊗[ℚ] (sha ⊗[ℚ] sha))
  ∘ₗ (LinearMap.rTensorHom sha sha_comul
      : sha ⊗[ℚ] sha →ₗ[ℚ] (sha ⊗[ℚ] sha) ⊗[ℚ] sha)
  ∘ₗ (sha_comul : sha →ₗ[ℚ] sha ⊗[ℚ] sha)
  =
  (LinearMap.lTensorHom sha sha_comul
      : sha ⊗[ℚ] sha →ₗ[ℚ] sha ⊗[ℚ] (sha ⊗[ℚ] sha))
  ∘ₗ (sha_comul : sha →ₗ[ℚ] sha ⊗[ℚ] sha)
  :=
  by
    apply Basis.ext β
    intro i
    simp [sha_comul]
    match i with
    | bas.e => simp [sha_comul_on_basis]
    | bas.x => simp [sha_comul_on_basis,TensorProduct.add_tmul,TensorProduct.tmul_add]; rw [add_assoc]
    | bas.g => simp [sha_comul_on_basis] --,TensorProduct.add_tmul,TensorProduct.tmul_add]; sorry
    | bas.gx => simp [sha_comul_on_basis,TensorProduct.add_tmul,TensorProduct.tmul_add]; rw [add_assoc]


noncomputable instance : CoalgebraTens ℚ sha where
  comul := sha_comul
  counit := sha_counit
  coone_comul := sha_coone_comul
  comul_coone := sha_comul_coone
  comul_coassoc := sha_comul_coassoc


/- --- Check that it is a Hopf algebra --- -/

noncomputable def sha_anti_on_basis : bas → sha := fun a ↦
  match a with
  | bas.e => βe
  | bas.x => βgx
  | bas.g => βg
  | bas.gx => -βx

noncomputable def sha_anti : sha →ₗ[ℚ] sha :=
  Basis.constr β ℚ sha_anti_on_basis


noncomputable def sha_g_conj : sha →ₗ[ℚ] sha :=
  (sha_mul : sha ⊗[ℚ] sha →ₗ[ℚ] sha)
  ∘ₗ
  (LinearMap.rTensorHom sha sha_mul : (sha ⊗[ℚ] sha) ⊗[ℚ] sha →ₗ[ℚ] sha ⊗[ℚ] sha)
  ∘ₗ
  (LinearMap.rTensorHom sha (LinearMap.rTensorHom sha sha_g) : (ℚ ⊗[ℚ] sha) ⊗[ℚ] sha →ₗ[ℚ] (sha ⊗[ℚ] sha) ⊗[ℚ] sha)
  ∘ₗ
  (LinearMap.rTensorHom sha (unitor_left_inv sha) : sha ⊗[ℚ] sha →ₗ[ℚ] (ℚ ⊗[ℚ] sha) ⊗[ℚ] sha)
  ∘ₗ
  (LinearMap.lTensorHom sha sha_g : sha ⊗[ℚ] ℚ →ₗ[ℚ] sha ⊗[ℚ] sha)
  ∘ₗ
  (unitor_right_inv sha : sha →ₗ[ℚ] sha ⊗[ℚ] ℚ)

-- the antipode squares to conjugating with g
example : sha_anti ∘ₗ sha_anti = sha_g_conj
  := by
    apply Basis.ext β
    intro i
    cases i <;> simp [sha_anti,sha_anti_on_basis,
      sha_mul_ββ_lemma,sha_mul_on_basis,
      sha_g_conj,sha_g,
      unitor_right_inv,unitor_left_inv]

theorem sha_comul_mul :
  ( mulAA : (sha ⊗[ℚ] sha) ⊗[ℚ] (sha ⊗[ℚ] sha) →ₗ[ℚ] sha ⊗[ℚ] sha )
  ∘ₗ
  ( tensor_f_g sha_comul sha_comul : sha ⊗[ℚ] sha →ₗ[ℚ] (sha ⊗[ℚ] sha) ⊗[ℚ] (sha ⊗[ℚ] sha) )
  =
  ( sha_comul : sha →ₗ[ℚ] sha ⊗[ℚ] sha )
  ∘ₗ
  ( sha_mul : sha ⊗[ℚ] sha →ₗ[ℚ] sha)
  := by
    apply Basis.ext ββ
    intro (a,b)
    simp [tensor_f_g,ββ,sha_mul_ββ_lemma]
    cases a <;> cases b <;>
      repeat simp [sha_mul_on_basis,sha_comul,
          sha_comul_on_basis,
          TensorProduct.tmul_add, TensorProduct.add_tmul,
          tensor_sub_left, tensor_sub_right,
          mulAA_tmul,AlgebraTens.mul,sha_mul_ββ_lemma,
          add_comm]

noncomputable def βℚ : Basis (Fin 1) ℚ ℚ
  := Basis.singleton (Fin 1) ℚ

theorem sha_comul_unit :
  ( sha_comul : sha →ₗ[ℚ] sha ⊗[ℚ] sha )
  ∘ₗ
  ( sha_unit : ℚ →ₗ[ℚ] sha )
  =
  ( (tensor_f_g sha_unit sha_unit) : ℚ ⊗[ℚ] ℚ →ₗ[ℚ] sha ⊗[ℚ] sha )
  ∘ₗ
  ( LinearEquiv.symm (TensorProduct.lid ℚ ℚ) : ℚ →ₗ[ℚ] ℚ⊗[ℚ] ℚ )
  := by
    apply Basis.ext βℚ
    intro i
    rw [βℚ,Basis.singleton_apply]
    simp [tensor_f_g,sha_unit,sha_comul,sha_comul_on_basis]

theorem sha_counit_mul :
  ( sha_counit : sha →ₗ[ℚ] ℚ )
  ∘ₗ
  ( sha_mul : sha ⊗[ℚ] sha →ₗ[ℚ] sha)
  =
  ( TensorProduct.lid ℚ ℚ : ℚ ⊗[ℚ] ℚ →ₗ[ℚ] ℚ )
  ∘ₗ
  ( (tensor_f_g sha_counit sha_counit) : sha ⊗[ℚ] sha →ₗ[ℚ] ℚ ⊗[ℚ] ℚ )
  := by
    apply Basis.ext ββ
    intro (a,b)
    simp [tensor_f_g,ββ,sha_mul_ββ_lemma]
    cases a <;> cases b <;>
      simp [sha_counit,sha_counit_on_basis,sha_mul_on_basis]

theorem sha_counit_unit :
  ( sha_counit : sha →ₗ[ℚ] ℚ )
  ∘ₗ
  ( sha_unit : ℚ →ₗ[ℚ] sha )
  =
  ( LinearMap.id : ℚ →ₗ[ℚ] ℚ )
  := by
    apply Basis.ext βℚ
    intro i
    rw [βℚ,Basis.singleton_apply]
    simp [sha_unit, sha_counit, sha_counit_on_basis]

theorem sha_anti_left :
  ( sha_mul : sha ⊗[ℚ] sha →ₗ[ℚ] sha )
  ∘ₗ
  ( LinearMap.lTensorHom sha sha_anti : sha ⊗[ℚ] sha →ₗ[ℚ] sha ⊗[ℚ] sha )
  ∘ₗ
  ( sha_comul : sha →ₗ[ℚ] sha ⊗[ℚ] sha )
  =
  ( sha_unit : ℚ →ₗ[ℚ] sha )
  ∘ₗ
  ( sha_counit : sha →ₗ[ℚ] ℚ )
  := by
    apply Basis.ext β
    intro i
    cases i <;> simp [sha_unit,sha_counit,sha_counit_on_basis,
      sha_comul,sha_comul_on_basis,
      sha_anti,sha_anti_on_basis,
      tensor_sub_right,
      sha_mul_ββ_lemma,sha_mul_on_basis]

theorem sha_anti_right :
  ( sha_mul : sha ⊗[ℚ] sha →ₗ[ℚ] sha )
  ∘ₗ
  ( LinearMap.rTensorHom sha sha_anti : sha ⊗[ℚ] sha →ₗ[ℚ] sha ⊗[ℚ] sha )
  ∘ₗ
  ( sha_comul : sha →ₗ[ℚ] sha ⊗[ℚ] sha )
  =
  ( sha_unit : ℚ →ₗ[ℚ] sha )
  ∘ₗ
  ( sha_counit : sha →ₗ[ℚ] ℚ )
  := by
    apply Basis.ext β
    intro i
    cases i <;> simp [sha_unit,sha_counit,sha_counit_on_basis,
      sha_comul,sha_comul_on_basis,
      sha_anti,sha_anti_on_basis,
      tensor_sub_left,
      sha_mul_ββ_lemma,sha_mul_on_basis]

noncomputable instance : HopfAlgebraTens ℚ sha where
  anti := sha_anti
  comul_mul := sha_comul_mul
  comul_unit := sha_comul_unit
  counit_mul := sha_counit_mul
  counit_unit := sha_counit_unit
  anti_left := sha_anti_left
  anti_right := sha_anti_right

end SweedlerHopfAlgebra
