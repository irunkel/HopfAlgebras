import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HopfAlgebra.Basic

namespace SweedlerHopfAlgebra

variable {K : Type} [CommRing K]

-- TODO: maybe not define it over Q from the start but keep ring arbitrary

/- Sweedler's Hopf algebra is 4 dimensional, has a nilpotent
   element x, and a group-like g, so we will use e, x, g, gx
   to denote the basis vectors.
   This follows Kassel "Quantum groups" Ch VIII.2 Example 2,
   with the convention x -> g, y -> x
-/
inductive bas where
| e : bas
| x : bas
| g : bas
| gx : bas
deriving DecidableEq

-- provide a proof that bas indeed has 4 elements
-- TODO: Can this be done more easily?
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
instance : Finite bas := Finite.intro isEquivFin4

/- TODO: I wanted to do this with my own type via "abbrev sha := bas → K",
   but then it forgets all properties and I was not able to reprove e.g.
   AddCommGroup, eg I failed with zsmul_zero' etc.
-/
-- sha = *S*weedler's *H*opf *a*lgebra
def sha := bas → K
instance : AddCommGroup (@sha K) := inferInstanceAs (AddCommGroup (bas → K))
  -- if one uses AddCommMonoid here, the "a-b" operation below will
  -- complain that it cannot instantiate "Neg".
instance : Module K (@sha K) := inferInstanceAs (Module K (bas → K))

-- this turns functions into a basis
noncomputable def β : Basis bas K (@sha K)
  := Pi.basisFun K bas

noncomputable abbrev βe  := (β bas.e  : @sha K)
noncomputable abbrev βx  := (β bas.x  : @sha K)
noncomputable abbrev βg  := (β bas.g  : @sha K)
noncomputable abbrev βgx := (β bas.gx : @sha K)


/-
  basis of the tensor product sha ⊗ sha
  (will use ⊗ below, but want to use full notation at
   least once to start with)
-/
noncomputable def ββ : Basis (Prod bas bas) K (TensorProduct K (@sha K) (@sha K))
  := Basis.tensorProduct β β

-- mathlib docu says "open scoped TensorProduct" to use ⊗, and "open" for all (unprotected) defs
open LinearMap TensorProduct Hopf


/- --- Algebra structure for Sweedler --- -/

-- product of basis vectors
noncomputable def sha_mul_on_basis : bas × bas → (@sha K) := fun (a,b) ↦
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

example : sha_mul_on_basis (bas.e , bas.e) = ( βe : @sha K )
  := by rfl

/- and the corresponding linear map on the tensor product
   Note that sha ⊗[K] sha → sha is also accepted here, but then
   below we cannot use that sha_mul is a linear map.
-/
noncomputable def sha_mul : (@sha K) ⊗[K] (@sha K) →ₗ[K] (@sha K) :=
  Basis.constr ββ K sha_mul_on_basis

theorem sha_mul_ββ_lemma : sha_mul ((β i) ⊗ₜ[K] (β j)) = sha_mul_on_basis (i,j)
  := by
    rw [sha_mul]
    rw [← Basis.tensorProduct_apply, ← ββ]
    simp

/- TensorProduct.tmul R m n gives the tensor product
   on elements, it is abbreviated as m ⊗ₜ[R] n
   The dot •, \bu, is the scalar action. To access it directly
   one has to hunt it down through the type classes
   (just smul or Module.smul does not work), it is hidden
   in SMul. This gives the 2nd version of the rhs below.
-/

example : sha_mul ( βg ⊗ₜ[K] βx - βx ⊗ₜ[K] βg ) = (2:K) • ( βgx : @sha K )
-- the dot is the action of K on sha, in long form: = SMul.smul (2:K) (β bas.gx:sha)
  := by
  calc
  sha_mul ( βg ⊗ₜ[K] βx - βx ⊗ₜ[K] βg )
    = sha_mul ( βg ⊗ₜ[K] βx ) - sha_mul ( βx ⊗ₜ[K] βg ) := by simp
  _ = sha_mul_on_basis ( bas.g , bas.x )
      - sha_mul_on_basis ( bas.x , bas.g )
      := by rw [sha_mul_ββ_lemma,sha_mul_ββ_lemma]
  _ = βgx + βgx := by simp [sha_mul_on_basis]
  _ = (2:K) • βgx := by rw [two_smul];

noncomputable def βββ : Basis ((bas × bas) × bas) K (((@sha K) ⊗[K] (@sha K)) ⊗[K] (@sha K))
  := Basis.tensorProduct ββ β

theorem tensor_sub_right (a b : (@sha K)): a ⊗ₜ[K] (-b) = - (a ⊗ₜ[K] b)
  := by
    calc
      a ⊗ₜ[K] (-b)
        = a ⊗ₜ[K] ((-1) • b) := by simp
      _ = (-1) • (a ⊗ₜ[K] b) := by rw [tmul_smul]
      _ = - (a ⊗ₜ[K] b) := by simp

theorem tensor_sub_left (a b : (@sha K)): (-a) ⊗ₜ[K] b = - (a ⊗ₜ[K] b)
  := by
    calc
      (-a) ⊗ₜ[K] b
        = ((-1) • a) ⊗ₜ[K] b := by simp
      _ = (-1) • (a ⊗ₜ[K] b) := by rw [smul_tmul']
      _ = - (a ⊗ₜ[K] b) := by simp

theorem sha_mul_assoc :
  (sha_mul
  ∘ₗ (map sha_mul id) :
  (sha ⊗[K] sha) ⊗[K] sha →ₗ[K] sha)
  =
  (sha_mul
  ∘ₗ (map id sha_mul)
  ∘ₗ (assoc (@sha K) (@sha K) (@sha K))
  :
  (sha ⊗[K] sha) ⊗[K] sha →ₗ[K] sha)
  := by
    apply Basis.ext βββ
    intro ⟨ ⟨a,b⟩ , c ⟩
    simp
    rw [βββ,ββ]
    simp [sha_mul_ββ_lemma]
    cases a <;> cases b <;> cases c <;>
      repeat simp [sha_mul_on_basis,sha_mul_ββ_lemma,
        tensor_sub_left,tensor_sub_right];

/- TODO: surely somewhere there should be R -> M as a linear map
   which takes 1 in R to some basis vector b in M predefined
-/
noncomputable def sha_unit : K →ₗ[K] (@sha K) := {
  toFun := fun a ↦ a • βe
  map_add' := by
    intro a b
    simp [add_smul]
  map_smul' := by
    intro a b
    dsimp
    rw [mul_smul (a:K) (b:K) βe]
  }

noncomputable def sha_g : K →ₗ[K] (@sha K) := {
  toFun := fun a ↦ a • βg
  map_add' := by
    intro a b
    simp [add_smul]
  map_smul' := by
    intro a b
    dsimp
    rw [mul_smul (a:K) (b:K) βg]
  }

theorem sha_one_mul :
  ( (sha_mul : sha ⊗[K] sha →ₗ[K] sha)
  ∘ₗ (map sha_unit id : K ⊗[K] sha  →ₗ[K]  sha ⊗[K] sha)
  ∘ₗ (unitor_left_inv sha :  sha →ₗ[K] (K ⊗[K] sha))
  : sha →ₗ[K] sha)
  =
  (id
  : sha →ₗ[K] sha)
  := by
    apply Basis.ext β
    intro i
    simp [sha_unit]
    cases i <;> simp [sha_mul_ββ_lemma,sha_mul_on_basis]

theorem sha_mul_one :
  ( (sha_mul : sha ⊗[K] sha →ₗ[K] sha)
  ∘ₗ (map id sha_unit : sha ⊗[K] K  →ₗ[K]  sha ⊗[K] sha)
  ∘ₗ (unitor_right_inv sha :  sha →ₗ[K] (sha ⊗[K] K))
  : sha →ₗ[K] sha)
  =
  (id
  : sha →ₗ[K] sha)
  := by
    apply Basis.ext β
    intro i
    simp [sha_unit]
    cases i <;> simp [sha_mul_ββ_lemma,sha_mul_on_basis]

noncomputable instance : AlgebraTens K (@sha K) where
  mul := sha_mul
  unit := sha_unit
  one_mul := sha_one_mul
  mul_one := sha_mul_one
  mul_assoc := sha_mul_assoc

/- --- Coalgebra structure for Sweedler --- -/

noncomputable def sha_comul_on_basis : bas → (@sha K) ⊗[K] (@sha K) := fun a ↦
  match a with
  | bas.e => βe ⊗ₜ[K] βe
  | bas.x => βe ⊗ₜ[K] βx + βx ⊗ₜ[K] βg
  | bas.g => βg ⊗ₜ[K] βg
  | bas.gx => βg ⊗ₜ[K] βgx + βgx ⊗ₜ[K] βe

noncomputable def sha_comul : (@sha K)  →ₗ[K]  (@sha K) ⊗[K] (@sha K) :=
  Basis.constr β K sha_comul_on_basis

noncomputable def sha_counit_on_basis : bas → K := fun a ↦
  match a with
  | bas.e => 1
  | bas.x => 0
  | bas.g => 1
  | bas.gx => 0

noncomputable def sha_counit : (@sha K)  →ₗ[K] K :=
  Basis.constr β K sha_counit_on_basis

/-
  this checks that the definition of the coproduct indeed
  satisfies Δ(g)Δ(x) = Δ(gx)
  TODO: Maybe the rules used below should be added to the
  simplifier?
-/
example :
  ( mulAA ∘ₗ (map sha_comul sha_comul) ) (βg ⊗ₜ[K] βx)
  = sha_comul βgx
  := by
    simp [sha_comul,sha_comul_on_basis,
      tmul_add,mulAA_tmul,AlgebraTens.mul,
      sha_mul_ββ_lemma,sha_mul_on_basis]


theorem sha_coone_comul  :
  (unitor_left sha :  K ⊗[K] sha →ₗ[K] sha)
  ∘ₗ (map sha_counit id : sha ⊗[K] sha  →ₗ[K]  K ⊗[K] sha)
  ∘ₗ (sha_comul : sha →ₗ[K] sha ⊗[K] sha)
  =
  (id : sha →ₗ[K] sha)
  :=
  by
    apply Basis.ext β
    intro i
    simp [sha_comul]
    cases i <;> simp [sha_comul_on_basis,sha_counit,sha_counit_on_basis]

theorem sha_comul_coone :
  (unitor_right sha :  sha ⊗[K] K →ₗ[K] sha)
  ∘ₗ (map id sha_counit : sha ⊗[K] sha  →ₗ[K]  sha ⊗[K] K)
  ∘ₗ (sha_comul : sha →ₗ[K] sha ⊗[K] sha)
  =
  (id : sha →ₗ[K] sha)
  :=
  by
    apply Basis.ext β
    intro i
    simp [sha_comul]
    cases i <;> simp [sha_comul_on_basis,sha_counit,sha_counit_on_basis]

theorem sha_comul_coassoc :
  (assoc (@sha K) (@sha K) (@sha K)
      : (sha ⊗[K] sha) ⊗[K] sha →ₗ[K] sha ⊗[K] (sha ⊗[K] sha))
  ∘ₗ (map sha_comul id
      : sha ⊗[K] sha →ₗ[K] (sha ⊗[K] sha) ⊗[K] sha)
  ∘ₗ (sha_comul : sha →ₗ[K] sha ⊗[K] sha)
  =
  (map id sha_comul
      : sha ⊗[K] sha →ₗ[K] sha ⊗[K] (sha ⊗[K] sha))
  ∘ₗ (sha_comul : sha →ₗ[K] sha ⊗[K] sha)
  :=
  by
    apply Basis.ext β
    intro i
    simp [sha_comul]
    match i with
    | bas.e => simp [sha_comul_on_basis]
    | bas.x => simp [sha_comul_on_basis,add_tmul,tmul_add]; rw [add_assoc]
    | bas.g => simp [sha_comul_on_basis]
    | bas.gx => simp [sha_comul_on_basis,add_tmul,tmul_add]; rw [add_assoc]


noncomputable instance : CoalgebraTens K (@sha K) where
  comul := sha_comul
  counit := sha_counit
  coone_comul := sha_coone_comul
  comul_coone := sha_comul_coone
  comul_coassoc := sha_comul_coassoc


/- --- Check that it is a Hopf algebra --- -/

noncomputable def sha_anti_on_basis : bas → (@sha K) := fun a ↦
  match a with
  | bas.e => βe
  | bas.x => βgx
  | bas.g => βg
  | bas.gx => -βx

noncomputable def sha_anti : (@sha K) →ₗ[K] (@sha K) :=
  Basis.constr β K sha_anti_on_basis


-- the map x ↦ g x g⁻¹ , but here g⁻¹ = g.
noncomputable def sha_g_conj : (@sha K) →ₗ[K] (@sha K) :=
  (sha_mul : sha ⊗[K] sha →ₗ[K] sha)
  ∘ₗ
  (map sha_mul id : (sha ⊗[K] sha) ⊗[K] sha →ₗ[K] sha ⊗[K] sha)
  ∘ₗ
  (map (map sha_g id) id : (K ⊗[K] sha) ⊗[K] sha →ₗ[K] (sha ⊗[K] sha) ⊗[K] sha)
  ∘ₗ
  (map (unitor_left_inv sha) id : sha ⊗[K] sha →ₗ[K] (K ⊗[K] sha) ⊗[K] sha)
  ∘ₗ
  (map id sha_g : sha ⊗[K] K →ₗ[K] sha ⊗[K] sha)
  ∘ₗ
  (unitor_right_inv sha : sha →ₗ[K] sha ⊗[K] K)

-- the antipode squares to conjugating with g
example : ( sha_anti ∘ₗ sha_anti : (@sha K) →ₗ[K] (@sha K))
  = ( sha_g_conj : (@sha K) →ₗ[K] (@sha K))
  := by
    apply Basis.ext β
    intro i
    cases i <;> simp [sha_anti,sha_anti_on_basis,
      sha_mul_ββ_lemma,sha_mul_on_basis,
      sha_g_conj,sha_g]

theorem sha_comul_mul :
  ( mulAA : (sha ⊗[K] sha) ⊗[K] (sha ⊗[K] sha) →ₗ[K] sha ⊗[K] sha )
  ∘ₗ
  ( map sha_comul sha_comul : sha ⊗[K] sha →ₗ[K] (sha ⊗[K] sha) ⊗[K] (sha ⊗[K] sha) )
  =
  ( sha_comul : sha →ₗ[K] sha ⊗[K] sha )
  ∘ₗ
  ( sha_mul : sha ⊗[K] sha →ₗ[K] sha)
  := by
    apply Basis.ext ββ
    intro (a,b)
    simp [ββ,sha_mul_ββ_lemma]
    cases a <;> cases b <;>
      repeat simp [sha_mul_on_basis,sha_comul,
          sha_comul_on_basis,
          tmul_add, add_tmul,
          tensor_sub_left, tensor_sub_right,
          mulAA_tmul,AlgebraTens.mul,sha_mul_ββ_lemma,
          add_comm]

noncomputable def βK : Basis (Fin 1) K K
  := Basis.singleton (Fin 1) K

theorem sha_comul_unit :
  ( sha_comul : sha →ₗ[K] sha ⊗[K] sha )
  ∘ₗ
  ( sha_unit : K →ₗ[K] sha )
  =
  ( (map sha_unit sha_unit) : K ⊗[K] K →ₗ[K] sha ⊗[K] sha )
  ∘ₗ
  ( unitor_left_inv K : K →ₗ[K] K⊗[K] K )
  := by
    apply Basis.ext βK
    intro i
    rw [βK,Basis.singleton_apply]
    simp [sha_unit,sha_comul,sha_comul_on_basis]

theorem sha_counit_mul :
  ( sha_counit : sha →ₗ[K] K )
  ∘ₗ
  ( sha_mul : sha ⊗[K] sha →ₗ[K] sha)
  =
  ( unitor_left K : K ⊗[K] K →ₗ[K] K )
  ∘ₗ
  ( (map sha_counit sha_counit) : sha ⊗[K] sha →ₗ[K] K ⊗[K] K )
  := by
    apply Basis.ext ββ
    intro (a,b)
    simp [ββ,sha_mul_ββ_lemma]
    cases a <;> cases b <;>
      simp [sha_counit,sha_counit_on_basis,sha_mul_on_basis]

theorem sha_counit_unit :
  ( sha_counit : sha →ₗ[K] K )
  ∘ₗ
  ( sha_unit : K →ₗ[K] sha )
  =
  ( id : K →ₗ[K] K )
  := by
    apply Basis.ext βK
    intro i
    rw [βK,Basis.singleton_apply]
    simp [sha_unit, sha_counit, sha_counit_on_basis]

theorem sha_anti_left :
  ( sha_mul : sha ⊗[K] sha →ₗ[K] sha )
  ∘ₗ
  ( map id sha_anti : sha ⊗[K] sha →ₗ[K] sha ⊗[K] sha )
  ∘ₗ
  ( sha_comul : sha →ₗ[K] sha ⊗[K] sha )
  =
  ( sha_unit : K →ₗ[K] sha )
  ∘ₗ
  ( sha_counit : sha →ₗ[K] K )
  := by
    apply Basis.ext β
    intro i
    cases i <;> simp [sha_unit,sha_counit,sha_counit_on_basis,
      sha_comul,sha_comul_on_basis,
      sha_anti,sha_anti_on_basis,
      tensor_sub_right,
      sha_mul_ββ_lemma,sha_mul_on_basis]

theorem sha_anti_right :
  ( sha_mul : sha ⊗[K] sha →ₗ[K] sha )
  ∘ₗ
  ( map sha_anti id : sha ⊗[K] sha →ₗ[K] sha ⊗[K] sha )
  ∘ₗ
  ( sha_comul : sha →ₗ[K] sha ⊗[K] sha )
  =
  ( sha_unit : K →ₗ[K] sha )
  ∘ₗ
  ( sha_counit : sha →ₗ[K] K )
  := by
    apply Basis.ext β
    intro i
    cases i <;> simp [sha_unit,sha_counit,sha_counit_on_basis,
      sha_comul,sha_comul_on_basis,
      sha_anti,sha_anti_on_basis,
      tensor_sub_left,
      sha_mul_ββ_lemma,sha_mul_on_basis]

noncomputable instance : BialgebraTens K (@sha K) where
  comul_mul := sha_comul_mul
  comul_unit := sha_comul_unit
  counit_mul := sha_counit_mul
  counit_unit := sha_counit_unit

open AlgebraTens CoalgebraTens

noncomputable instance : HopfAlgebraTens K (@sha K) where
  anti := sha_anti
  hasAntipodeProp :=
  {
    left := by
      simp [mul,comul,unit,counit]; rw[sha_anti_left]
    right := by
      simp [mul,comul,unit,counit]; rw[sha_anti_right]
  }

end SweedlerHopfAlgebra
