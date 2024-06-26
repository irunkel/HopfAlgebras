import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic -- tensor product of two algebras

namespace Hopf

-- mathlib docu says I should do this to use ⊗
open LinearMap TensorProduct

/- --- Linear algebra helper definitions --- -/
section LinAlg


/- TensorProduct.lid is protected, so I cannot just write "lid"
   The following is still long, but I find it easier to remember -/
noncomputable abbrev unitor_left
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  R ⊗[R] M →ₗ[R] M := TensorProduct.lid R M

noncomputable abbrev unitor_left_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M →ₗ[R] R ⊗[R] M := LinearEquiv.symm (TensorProduct.lid R M)

theorem unitor_left_nat
  {R:Type} {M N:Type}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (f : M →ₗ[R] N) :
  ( unitor_left N : R ⊗[R] N →ₗ[R] N )
  ∘ₗ ( map id f : R ⊗[R] M →ₗ[R] R ⊗[R] N )
  =
  ( f : M →ₗ[R] N )
  ∘ₗ ( unitor_left M : R ⊗[R] M →ₗ[R] M )
  := by
    apply ext'
    simp [unitor_left]

noncomputable abbrev unitor_right
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M ⊗[R] R →ₗ[R] M := TensorProduct.rid R M

noncomputable abbrev unitor_right_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M →ₗ[R] M ⊗[R] R := LinearEquiv.symm (TensorProduct.rid R M)

theorem unitor_right_nat
  {R:Type} {M N:Type}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (f : M →ₗ[R] N) :
  ( unitor_right N : N ⊗[R] R →ₗ[R] N )
  ∘ₗ ( map f id : M ⊗[R] R →ₗ[R] N ⊗[R] R )
  =
  ( f : M →ₗ[R] N )
  ∘ₗ ( unitor_right M : M ⊗[R] R →ₗ[R] M )
  := by
    apply ext'
    simp [unitor_right]

/- assoc is a protected, so to just write "assoc", the following
   seems to be an option: -/
noncomputable abbrev assoc {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C)
  := TensorProduct.assoc R A B C

noncomputable abbrev assoc_inv {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C
  := (TensorProduct.assoc R A B C).symm

theorem assoc_nat {R : Type} (A B C A' B' C':Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  [AddCommMonoid A'] [Module R A']
  [AddCommMonoid B'] [Module R B']
  [AddCommMonoid C'] [Module R C']
  (f : A →ₗ[R] A')
  (g : B →ₗ[R] B')
  (h : C →ₗ[R] C')
  :
  ( map f (map g h) : A ⊗[R] (B ⊗[R] C) →ₗ[R] A' ⊗[R] (B' ⊗[R] C') )
  ∘ₗ
  ( assoc A B C : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C) )
  =
  ( assoc A' B' C' : (A' ⊗[R] B') ⊗[R] C' →ₗ[R] A' ⊗[R] (B' ⊗[R] C') )
  ∘ₗ
  ( map (map f g) h : (A ⊗[R] B) ⊗[R] C →ₗ[R] (A' ⊗[R] B') ⊗[R] C' )
  := by
    simp [assoc,map_map_comp_assoc_eq]

theorem assoc_inv_nat {R : Type} (A B C A' B' C':Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  [AddCommMonoid A'] [Module R A']
  [AddCommMonoid B'] [Module R B']
  [AddCommMonoid C'] [Module R C']
  (f : A →ₗ[R] A')
  (g : B →ₗ[R] B')
  (h : C →ₗ[R] C')
  :
  ( map (map f g) h : (A ⊗[R] B) ⊗[R] C →ₗ[R] (A' ⊗[R] B') ⊗[R] C' )
  ∘ₗ
  ( assoc_inv A B C : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C )
  =
  ( assoc_inv A' B' C' : A' ⊗[R] (B' ⊗[R] C') →ₗ[R] (A' ⊗[R] B') ⊗[R] C' )
  ∘ₗ
  ( map f (map g h) : A ⊗[R] (B ⊗[R] C) →ₗ[R] A' ⊗[R] (B' ⊗[R] C') )
  := by
    calc
      ( map (map f g) h ) ∘ₗ ( assoc_inv A B C )
        = (( assoc_inv A' B' C' ) ∘ₗ ( assoc A' B' C' )) ∘ₗ ( map (map f g) h ) ∘ₗ ( assoc_inv A B C )
            := by simp --rw [assoc_inv_is_inv]; simp
      _ = ( assoc_inv A' B' C' ) ∘ₗ (( assoc A' B' C' ) ∘ₗ ( map (map f g) h )) ∘ₗ ( assoc_inv A B C )
            := by simp only [LinearMap.comp_assoc]
      _ = ( assoc_inv A' B' C' ) ∘ₗ ( map f (map g h) ) ∘ₗ ( assoc A B C ) ∘ₗ ( assoc_inv A B C )
            := by rw [← assoc_nat]; simp [LinearMap.comp_assoc]
      _ = ( assoc_inv A' B' C' ) ∘ₗ ( map f (map g h) )
            := by simp

end LinAlg

/- --- Algebra definition --- -/
section AlgebraDef
/- This defines an associative unital algebra in terms of
   linear maps and tensor products (mathlib defines algebras
   as rings with a map of a commutative ring to the center
   instead).
   TODO: Is this maybe already in mathlib, too? -/

class AlgebraTens (R:Type) (A:Type)
  [CommSemiring R] [AddCommMonoid A] [Module R A] where

  mul : A ⊗[R] A →ₗ[R] A
  unit : R →ₗ[R] A

  one_mul :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (map unit id : R ⊗[R] A  →ₗ[R]  A ⊗[R] A)
    ∘ₗ (unitor_left_inv A :  A →ₗ[R] (R ⊗[R] A))
    =
    (id : A →ₗ[R] A)

  mul_one :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (map id unit : A ⊗[R] R  →ₗ[R]  A ⊗[R] A)
    ∘ₗ (unitor_right_inv A :  A →ₗ[R] (A ⊗[R] R))
    =
    (id : A →ₗ[R] A)

  mul_assoc :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (map mul id
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A))
    =
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (map id mul
        : A ⊗[R] (A ⊗[R] A) →ₗ[R] (A ⊗[R] A))
    ∘ₗ (assoc A A A
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))


namespace AlgebraTens

variable {A R : Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AlgebraTens R A]

lemma one_mul' :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (map unit id : R ⊗[R] A  →ₗ[R]  A ⊗[R] A)
    =
    (unitor_left A : R ⊗[R] A →ₗ[R] A)
  := by
  calc
    mul ∘ₗ (map unit id)
      = (mul ∘ₗ (map unit id) ∘ₗ (unitor_left_inv A)) ∘ₗ (unitor_left A)
        := by simp [comp_assoc]
    _ = (unitor_left A)
        := by rw [one_mul]; simp

lemma mul_one' :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (map id unit : A ⊗[R] R  →ₗ[R]  A ⊗[R] A)
    =
    (unitor_right A : A ⊗[R] R →ₗ[R] A)
  := by
  calc
    mul ∘ₗ (map id unit)
      = (mul ∘ₗ (map id unit) ∘ₗ (unitor_right_inv A)) ∘ₗ (unitor_right A)
        := by simp [comp_assoc]
    _ = (unitor_right A)
        := by rw [mul_one]; simp

lemma mul_assoc' :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (map id mul : A ⊗[R] (A ⊗[R] A) →ₗ[R] (A ⊗[R] A))
    =
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (map mul id : (A ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A))
    ∘ₗ (assoc_inv A A A
        : A ⊗[R] (A ⊗[R] A) →ₗ[R] (A ⊗[R] A) ⊗[R] A)
  := by
  calc
    mul ∘ₗ (map id mul)
      = mul ∘ₗ (map id mul) ∘ₗ (assoc A A A) ∘ₗ (assoc_inv A A A)
          := by simp
    _ = (mul ∘ₗ (map id mul) ∘ₗ (assoc A A A)) ∘ₗ (assoc_inv A A A)
          := by simp [comp_assoc]
    _ = mul ∘ₗ (map mul id) ∘ₗ (assoc_inv A A A)
          := by rw [assoc,← mul_assoc]; simp [comp_assoc]

variable {A R : Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AlgebraTens R A]

namespace fromAlgebra

variable {B :Type} [Semiring B] [Algebra R B]

noncomputable def bilin_aux (b1:B) : B →ₗ[R] B where
  toFun := fun b2 ↦ b1*b2
  map_add' := by
    intro x y
    dsimp
    rw [left_distrib]

  map_smul' := by
    intro r x
    dsimp
    -- simp also works at this point, but let's look in more detail
    rw [Algebra.smul_def',Algebra.smul_def']
    rw [← Semigroup.mul_assoc,← Semigroup.mul_assoc]
    rw [Algebra.commutes']

noncomputable def bilin : B →ₗ[R] (B →ₗ[R] B) where
  toFun := fun b1 ↦ bilin_aux b1
  map_add' := by
    intro x y
    dsimp
    apply LinearMap.ext
    intro b
    dsimp [bilin_aux]
    rw [right_distrib]

  map_smul' := by
    intro r x
    dsimp
    apply LinearMap.ext
    intro b
    simp [bilin_aux]

noncomputable def mul : B ⊗[R] B →ₗ[R] B :=
  TensorProduct.lift bilin

noncomputable def βR : Basis (Fin 1) R R
  := Basis.singleton (Fin 1) R

noncomputable def unit : R →ₗ[R] B :=
  Basis.constr βR R (fun (_: Fin 1) ↦ (1:B))

theorem one_mul :
    (mul : B ⊗[R] B →ₗ[R] B)
    ∘ₗ (map unit id : R ⊗[R] B  →ₗ[R]  B ⊗[R] B)
    ∘ₗ (unitor_left_inv B :  B →ₗ[R] (R ⊗[R] B))
    =
    (id : B →ₗ[R] B)
  := by
  apply LinearMap.ext
  intro b
  simp [unit,βR,mul,bilin,bilin_aux]

theorem mul_one :
    (mul : B ⊗[R] B →ₗ[R] B)
    ∘ₗ (map id unit : B ⊗[R] R  →ₗ[R]  B ⊗[R] B)
    ∘ₗ (unitor_right_inv B :  B →ₗ[R] (B ⊗[R] R))
    =
    (id : B →ₗ[R] B)
  := by
  apply LinearMap.ext
  intro b
  simp [unit,βR,mul,bilin,bilin_aux]

theorem mul_assoc :
    (mul : B ⊗[R] B →ₗ[R] B)
    ∘ₗ (map mul id
        : (B ⊗[R] B) ⊗[R] B →ₗ[R] (B ⊗[R] B))
    =
    (mul : B ⊗[R] B →ₗ[R] B)
    ∘ₗ (map id mul
        : B ⊗[R] (B ⊗[R] B) →ₗ[R] (B ⊗[R] B))
    ∘ₗ (assoc B B B
        : (B ⊗[R] B) ⊗[R] B →ₗ[R] B ⊗[R] (B ⊗[R] B))
  := by
  apply ext_threefold
  intro b1 b2 b3
  simp [mul,bilin,bilin_aux]
  rw [Semigroup.mul_assoc b1 b2 b3]

end fromAlgebra

/- the required instances automatically generate
   Module R B, see https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html#Algebra -/
noncomputable instance fromAlgebra {B : Type}
  [CommSemiring R]
  [Semiring B]
  [Algebra R B]
  : AlgebraTens R B where
  mul := fromAlgebra.mul
  unit := fromAlgebra.unit
  one_mul := fromAlgebra.one_mul
  mul_one := fromAlgebra.mul_one
  mul_assoc := fromAlgebra.mul_assoc

end AlgebraTens

end AlgebraDef

/- --- Coalgebra definition --- -/
section CoalgebraDef
/- This is basically the same as in mathlib -/

class CoalgebraTens (R:Type) (A:Type)
  [CommSemiring R] [AddCommMonoid A] [Module R A] where

  comul : A →ₗ[R] A ⊗[R] A
  counit : A →ₗ[R] R

  coone_comul :
    (unitor_left A : R ⊗[R] A →ₗ[R] A)
    ∘ₗ (map counit id : A ⊗[R] A  →ₗ[R]  R ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (id : A →ₗ[R] A)

  comul_coone :
    (unitor_right A :  A ⊗[R] R →ₗ[R] A)
    ∘ₗ (map id counit : A ⊗[R] A  →ₗ[R]  A ⊗[R] R)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (id : A →ₗ[R] A)

  comul_coassoc :
    (assoc A A A
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (map comul id
        : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (map id comul
        : A ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)

namespace CoalgebraTens

variable {A R : Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [CoalgebraTens R A]

lemma coone_comul' :
    (map counit id : A ⊗[R] A  →ₗ[R]  R ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (unitor_left_inv A : A →ₗ[R] R ⊗[R] A)
  := by
  calc
    (map counit id) ∘ₗ comul
      = ((unitor_left_inv A) ∘ₗ (unitor_left A)) ∘ₗ (map counit id) ∘ₗ comul
        := by simp
    _ = (unitor_left_inv A) ∘ₗ (unitor_left A) ∘ₗ (map counit id) ∘ₗ comul
        := by simp only [comp_assoc]
    _ = (unitor_left_inv A)
        := by rw [coone_comul]; simp

lemma comul_coone' :
    (map id counit : A ⊗[R] A →ₗ[R] A ⊗[R] R)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (unitor_right_inv A : A →ₗ[R] A ⊗[R] R)
  := by
  calc
    (map id counit) ∘ₗ comul
      = ((unitor_right_inv A) ∘ₗ (unitor_right A)) ∘ₗ (map id counit) ∘ₗ comul
        := by simp
    _ = (unitor_right_inv A) ∘ₗ (unitor_right A) ∘ₗ (map id counit) ∘ₗ comul
        := by simp only [comp_assoc]
    _ = (unitor_right_inv A)
        := by rw [comul_coone]; simp

lemma comul_coassoc' :
    (map comul id : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (assoc_inv A A A : A ⊗[R] (A ⊗[R] A) →ₗ[R] (A ⊗[R] A) ⊗[R] A)
    ∘ₗ (map id comul : A ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
  := by
  calc
    (map comul id) ∘ₗ comul
      = ((assoc_inv A A A) ∘ₗ (assoc A A A)) ∘ₗ (map comul id) ∘ₗ comul
          := by simp
    _ = (assoc_inv A A A) ∘ₗ (assoc A A A) ∘ₗ (map comul id) ∘ₗ comul
          := by simp only [comp_assoc]
    _ = (assoc_inv A A A) ∘ₗ (map id comul) ∘ₗ comul
          := by rw [← comul_coassoc]

end CoalgebraTens

end CoalgebraDef

open AlgebraTens CoalgebraTens

/- --- Bialgebra definition --- -/
section BialgebraDef
/-
  Just "def mulAA" Produced a compiler error
  "compiler IR check failed at 'Hopf.mulAA._rarg',
   error: unknown declaration 'addCommMonoid'"
  This is a known issue
  https://github.com/leanprover/lean4/issues/1785
  It just means that the definition has to be made noncomputable
-/
-- product on A ⊗ A
noncomputable def mulAA {R:Type} {A:Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AlgebraTens R A] :
  (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A
  := (

  let id_swap_id := (map (map id (TensorProduct.comm R A A)) id :
    (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A
    );

  -- the product on A ⊗ A
  (map mul mul : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A)
  ∘ₗ
  (assoc (A ⊗[R] A) A A : ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A))
  ∘ₗ
  (map (assoc_inv A A A) id : (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A)
  ∘ₗ
  (id_swap_id : (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A)
  ∘ₗ
  (map (assoc A A A) id : ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A)
  ∘ₗ
  (assoc_inv (A ⊗[R] A) A A : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A)

  )

-- mulAA on pure tensors : (a ⊗ b) * (c ⊗ d) = (a*c) ⊗ (b*d)
theorem mulAA_tmul {R:Type} {A:Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AlgebraTens R A] (a b c d : A) :
  mulAA ( (a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d) )
  =
  ( mul (a ⊗ₜ[R] c) ) ⊗ₜ[R] (mul (b ⊗ₜ[R] d) )
  := by simp [mulAA]

namespace fromAlgebra

variable {R B :Type} [CommSemiring R] [Semiring B] [Algebra R B]

-- show that mulAA agrees with the mathlib product on A ⊗ A
theorem mulAA_alg : mulAA = (AlgebraTens.mul : (B ⊗[R] B) ⊗[R] (B ⊗[R] B) →ₗ[R] B ⊗[R] B)
  := by
  apply TensorProduct.ext_fourfold'
  intro a b c d
  rw [mulAA_tmul]
  simp [AlgebraTens.mul,fromAlgebra.mul,
    fromAlgebra.bilin,fromAlgebra.bilin_aux]

end fromAlgebra


/- --- Bi- and Hopf algebra definition --- -/

class BialgebraTens (R A : Type)
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
extends AlgebraTens R A, CoalgebraTens R A where

  -- comul is algebra hom
  comul_mul :
  ( mulAA : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( map comul comul : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A) )
  =
  ( comul : A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( mul : A ⊗[R] A →ₗ[R] A)

  comul_unit :
  ( comul : A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( unit : R →ₗ[R] A )
  =
  ( (map unit unit) : R ⊗[R] R →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( unitor_left_inv R : R →ₗ[R] R⊗[R] R )

  -- counit is algebra hom
  counit_mul :
  ( counit : A →ₗ[R] R )
  ∘ₗ
  ( mul : A ⊗[R] A →ₗ[R] A)
  =
  ( unitor_left R : R ⊗[R] R →ₗ[R] R )
  ∘ₗ
  ( (map counit counit) : A ⊗[R] A →ₗ[R] R ⊗[R] R )

  counit_unit :
  ( counit : A →ₗ[R] R )
  ∘ₗ
  ( unit : R →ₗ[R] A )
  =
  ( id : R →ₗ[R] R )

end BialgebraDef

/- --- Hopf algebra definition --- -/
section HopfalgebraDef

open BialgebraTens

structure AntipodeProp {R:Type} {A:Type}
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
  [BialgebraTens R A]
  (anti : A →ₗ[R] A) where

  left : -- Δ ∘ (id ⊗ S) ∘ μ
  ( mul : A ⊗[R] A →ₗ[R] A )
  ∘ₗ
  ( map id anti : A ⊗[R] A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( comul : A →ₗ[R] A ⊗[R] A )
  =
  ( unit : R →ₗ[R] A )
  ∘ₗ
  ( counit : A →ₗ[R] R )

  right : -- Δ ∘ (S ⊗ id) ∘ μ
  ( mul : A ⊗[R] A →ₗ[R] A )
  ∘ₗ
  ( map anti id : A ⊗[R] A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( comul : A →ₗ[R] A ⊗[R] A )
  =
  ( unit : R →ₗ[R] A )
  ∘ₗ
  ( counit : A →ₗ[R] R )

class HopfAlgebraTens (R:Type) (A:Type)
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
extends BialgebraTens R A where
  anti : A →ₗ[R] A
  hasAntipodeProp : AntipodeProp anti

end HopfalgebraDef

end Hopf
