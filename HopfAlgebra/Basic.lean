import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace Hopf

-- mathlib docu says I should do this to use ⊗
open scoped TensorProduct

/- --- Linear algebra helper definitions --- -/
section LinAlg

/- Alternate names for unitors and associators
   This should probably be avoided in favour of the
   library to a large extend  -/

noncomputable def unitor_left
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  R ⊗[R] M →ₗ[R] M := TensorProduct.lid R M

noncomputable def unitor_left_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M →ₗ[R] R ⊗[R] M := LinearEquiv.symm (TensorProduct.lid R M)

theorem unitor_left_inv_is_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  unitor_left_inv M ∘ₗ unitor_left M = (LinearMap.id : R ⊗[R] M →ₗ[R] R ⊗[R] M)
  := by
    simp [unitor_left_inv,unitor_left]

theorem unitor_left_inv_is_inv'
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  unitor_left M ∘ₗ unitor_left_inv M = (LinearMap.id : M →ₗ[R] M)
  := by
    simp [unitor_left_inv,unitor_left]

theorem unitor_left_nat
  {R:Type} {M N:Type}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (f : M →ₗ[R] N) :
  ( unitor_left N : R ⊗[R] N →ₗ[R] N )
  ∘ₗ ( TensorProduct.map LinearMap.id f : R ⊗[R] M →ₗ[R] R ⊗[R] N )
  =
  ( f : M →ₗ[R] N )
  ∘ₗ ( unitor_left M : R ⊗[R] M →ₗ[R] M )
  := by
    apply TensorProduct.ext'
    simp [unitor_left]

noncomputable def unitor_right
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M ⊗[R] R →ₗ[R] M := TensorProduct.rid R M

noncomputable def unitor_right_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  M →ₗ[R] M ⊗[R] R := LinearEquiv.symm (TensorProduct.rid R M)

theorem unitor_right_inv_is_inv
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  unitor_right_inv M ∘ₗ unitor_right M = (LinearMap.id : M ⊗[R] R →ₗ[R] M ⊗[R] R)
  := by
    simp [unitor_right_inv,unitor_right]

theorem unitor_right_inv_is_inv'
  {R:Type} (M:Type)
  [CommSemiring R] [AddCommMonoid M] [Module R M] :
  unitor_right M ∘ₗ unitor_right_inv M = (LinearMap.id : M →ₗ[R] M)
  := by
    simp [unitor_right_inv,unitor_right]

theorem unitor_right_nat
  {R:Type} {M N:Type}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (f : M →ₗ[R] N) :
  ( unitor_right N : N ⊗[R] R →ₗ[R] N )
  ∘ₗ ( TensorProduct.map f LinearMap.id : M ⊗[R] R →ₗ[R] N ⊗[R] R )
  =
  ( f : M →ₗ[R] N )
  ∘ₗ ( unitor_right M : M ⊗[R] R →ₗ[R] M )
  := by
    apply TensorProduct.ext'
    simp [unitor_right]

noncomputable def assoc {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C)
  := TensorProduct.assoc R A B C

noncomputable def assoc_inv {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C
  := LinearEquiv.symm (TensorProduct.assoc R A B C)

theorem assoc_inv_is_inv  {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  :
  (assoc_inv A B C : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C)
  ∘ₗ
  (assoc A B C : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C))
  =
  (LinearMap.id : (A ⊗[R] B) ⊗[R] C →ₗ[R] (A ⊗[R] B) ⊗[R] C)
  := by
    simp [assoc,assoc_inv]

theorem assoc_inv_is_inv'  {R : Type} (A B C:Type)
  [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  :
  (assoc A B C : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C))
  ∘ₗ
  (assoc_inv A B C : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C)
  =
  (LinearMap.id : A ⊗[R] (B ⊗[R] C) →ₗ[R] A ⊗[R] (B ⊗[R] C))
  := by
    simp [assoc,assoc_inv]

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
  ( TensorProduct.map f (TensorProduct.map g h) : A ⊗[R] (B ⊗[R] C) →ₗ[R] A' ⊗[R] (B' ⊗[R] C') )
  ∘ₗ
  ( assoc A B C : (A ⊗[R] B) ⊗[R] C →ₗ[R] A ⊗[R] (B ⊗[R] C) )
  =
  ( assoc A' B' C' : (A' ⊗[R] B') ⊗[R] C' →ₗ[R] A' ⊗[R] (B' ⊗[R] C') )
  ∘ₗ
  ( TensorProduct.map (TensorProduct.map f g) h : (A ⊗[R] B) ⊗[R] C →ₗ[R] (A' ⊗[R] B') ⊗[R] C' )
  := by
    simp [assoc,TensorProduct.map_map_comp_assoc_eq]

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
  ( TensorProduct.map (TensorProduct.map f g) h : (A ⊗[R] B) ⊗[R] C →ₗ[R] (A' ⊗[R] B') ⊗[R] C' )
  ∘ₗ
  ( assoc_inv A B C : A ⊗[R] (B ⊗[R] C) →ₗ[R] (A ⊗[R] B) ⊗[R] C )
  =
  ( assoc_inv A' B' C' : A' ⊗[R] (B' ⊗[R] C') →ₗ[R] (A' ⊗[R] B') ⊗[R] C' )
  ∘ₗ
  ( TensorProduct.map f (TensorProduct.map g h) : A ⊗[R] (B ⊗[R] C) →ₗ[R] A' ⊗[R] (B' ⊗[R] C') )
  := by
    calc
      ( TensorProduct.map (TensorProduct.map f g) h ) ∘ₗ ( assoc_inv A B C )
        = (( assoc_inv A' B' C' ) ∘ₗ ( assoc A' B' C' )) ∘ₗ ( TensorProduct.map (TensorProduct.map f g) h ) ∘ₗ ( assoc_inv A B C )
            := by rw [assoc_inv_is_inv]; simp
      _ = ( assoc_inv A' B' C' ) ∘ₗ (( assoc A' B' C' ) ∘ₗ ( TensorProduct.map (TensorProduct.map f g) h )) ∘ₗ ( assoc_inv A B C )
            := by simp [LinearMap.comp_assoc]
      _ = ( assoc_inv A' B' C' ) ∘ₗ ( TensorProduct.map f (TensorProduct.map g h) ) ∘ₗ ( assoc A B C ) ∘ₗ ( assoc_inv A B C )
            := by rw [← assoc_nat]; simp [LinearMap.comp_assoc]
      _ = ( assoc_inv A' B' C' ) ∘ₗ ( TensorProduct.map f (TensorProduct.map g h) )
            := by rw [assoc_inv_is_inv']; simp

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
    ∘ₗ (TensorProduct.map unit LinearMap.id : R ⊗[R] A  →ₗ[R]  A ⊗[R] A)
    ∘ₗ (unitor_left_inv A :  A →ₗ[R] (R ⊗[R] A))
    =
    (LinearMap.id : A →ₗ[R] A)

  mul_one :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (TensorProduct.map LinearMap.id unit : A ⊗[R] R  →ₗ[R]  A ⊗[R] A)
    ∘ₗ (unitor_right_inv A :  A →ₗ[R] (A ⊗[R] R))
    =
    (LinearMap.id : A →ₗ[R] A)

  mul_assoc :
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (TensorProduct.map mul LinearMap.id
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A))
    =
    (mul : A ⊗[R] A →ₗ[R] A)
    ∘ₗ (TensorProduct.map LinearMap.id mul
        : A ⊗[R] (A ⊗[R] A) →ₗ[R] (A ⊗[R] A))
    ∘ₗ (TensorProduct.assoc R A A A
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))


namespace AlgebraTens

open LinearMap TensorProduct

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
      = mul ∘ₗ (map unit id) ∘ₗ (unitor_left_inv A) ∘ₗ (unitor_left A)
        := by rw [unitor_left_inv_is_inv]; simp
    _ = (mul ∘ₗ (map unit id) ∘ₗ (unitor_left_inv A)) ∘ₗ (unitor_left A)
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
      = mul ∘ₗ (map id unit) ∘ₗ (unitor_right_inv A) ∘ₗ (unitor_right A)
        := by rw [unitor_right_inv_is_inv]; simp
    _ = (mul ∘ₗ (map id unit) ∘ₗ (unitor_right_inv A)) ∘ₗ (unitor_right A)
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
          := by rw [assoc_inv_is_inv']; simp
    _ = (mul ∘ₗ (map id mul) ∘ₗ (assoc A A A)) ∘ₗ (assoc_inv A A A)
          := by simp [comp_assoc]
    _ = mul ∘ₗ (map mul id) ∘ₗ (assoc_inv A A A)
          := by rw [assoc,← mul_assoc]; simp [comp_assoc]

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
    ∘ₗ (TensorProduct.map counit LinearMap.id : A ⊗[R] A  →ₗ[R]  R ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (LinearMap.id : A →ₗ[R] A)

  comul_coone :
    (unitor_right A :  A ⊗[R] R →ₗ[R] A)
    ∘ₗ (TensorProduct.map LinearMap.id counit : A ⊗[R] A  →ₗ[R]  A ⊗[R] R)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (LinearMap.id : A →ₗ[R] A)

  comul_coassoc :
    (TensorProduct.assoc R A A A
        : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (TensorProduct.map comul LinearMap.id
        : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] A)
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)
    =
    (TensorProduct.map LinearMap.id comul
        : A ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A))
    ∘ₗ (comul : A →ₗ[R] A ⊗[R] A)

namespace CoalgebraTens

open LinearMap TensorProduct

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
        := by rw [unitor_left_inv_is_inv]; simp
    _ = (unitor_left_inv A) ∘ₗ (unitor_left A) ∘ₗ (map counit id) ∘ₗ comul
        := by simp [comp_assoc]
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
        := by rw [unitor_right_inv_is_inv]; simp
    _ = (unitor_right_inv A) ∘ₗ (unitor_right A) ∘ₗ (map id counit) ∘ₗ comul
        := by simp [comp_assoc]
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
          := by rw [assoc_inv_is_inv]; simp
    _ = (assoc_inv A A A) ∘ₗ (assoc A A A) ∘ₗ (map comul id) ∘ₗ comul
          := by simp [comp_assoc]
    _ = (assoc_inv A A A) ∘ₗ (map id comul) ∘ₗ comul
          := by rw [← comul_coassoc, ←assoc]

end CoalgebraTens

end CoalgebraDef

/- --- Bialgebra definition --- -/
section BialgebraDef
/-
  Just "def mulAA" Produced a compiler error
  "compiler IR check failed at 'Hopf.mulAA._rarg',
   error: unknown declaration 'TensorProduct.addCommMonoid'"
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

  -- all the individual maps entering the product on A ⊗ A
  let ass1equiv := TensorProduct.assoc R (A ⊗[R] A) A A
  let ass1 := (ass1equiv :
    ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A)
    )
  let ass1inv := (LinearEquiv.symm ass1equiv :
    (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A
    )
  let ass2equiv := TensorProduct.assoc R A A A
  let ass2_id := (TensorProduct.map ass2equiv LinearMap.id:
    ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A
    );
  let ass2inv_id := (TensorProduct.map (LinearEquiv.symm ass2equiv) LinearMap.id :
    (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A
    );
  let swap := (TensorProduct.comm R A A :
    A ⊗[R] A →ₗ[R] A ⊗[R] A
    );
  let id_swap_id := (TensorProduct.map (TensorProduct.map LinearMap.id swap) LinearMap.id :
    (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A
    );
  let mulmul := (TensorProduct.map AlgebraTens.mul AlgebraTens.mul:
    (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A
    )

  -- the product on A ⊗ A
  (mulmul : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A)
  ∘ₗ
  (ass1 : ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A))
  ∘ₗ
  (ass2inv_id : (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A)
  ∘ₗ
  (id_swap_id : (A ⊗[R] (A ⊗[R] A)) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A)
  ∘ₗ
  (ass2_id : ((A ⊗[R] A) ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] (A ⊗[R] A)) ⊗[R] A)
  ∘ₗ
  (ass1inv : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₗ[R] ((A ⊗[R] A) ⊗[R] A) ⊗[R] A)

  )

-- mulAA on pure tensors : (a ⊗ b) * (c ⊗ d) = (a*c) ⊗ (b*d)
theorem mulAA_tmul {R:Type} {A:Type}
  [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AlgebraTens R A] (a b c d : A) :
  mulAA ( (a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d) )
  =
  ( AlgebraTens.mul (a ⊗ₜ[R] c) ) ⊗ₜ[R] (AlgebraTens.mul (b ⊗ₜ[R] d) )
  := by simp [mulAA]

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
  ( TensorProduct.map comul comul : A ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] (A ⊗[R] A) )
  =
  ( comul : A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( mul : A ⊗[R] A →ₗ[R] A)

  comul_unit :
  ( comul : A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( unit : R →ₗ[R] A )
  =
  ( (TensorProduct.map unit unit) : R ⊗[R] R →ₗ[R] A ⊗[R] A )
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
  ( (TensorProduct.map counit counit) : A ⊗[R] A →ₗ[R] R ⊗[R] R )

  counit_unit :
  ( counit : A →ₗ[R] R )
  ∘ₗ
  ( unit : R →ₗ[R] A )
  =
  ( LinearMap.id : R →ₗ[R] R )

end BialgebraDef

/- --- Hopf algebra definition --- -/
section HopfalgebraDef

open AlgebraTens CoalgebraTens BialgebraTens

structure AntipodeProp {R:Type} {A:Type}
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
  [BialgebraTens R A]
  (anti : A →ₗ[R] A) where

  left : -- Δ ∘ (id ⊗ S) ∘ μ
  ( mul : A ⊗[R] A →ₗ[R] A )
  ∘ₗ
  ( TensorProduct.map LinearMap.id anti : A ⊗[R] A →ₗ[R] A ⊗[R] A )
  ∘ₗ
  ( comul : A →ₗ[R] A ⊗[R] A )
  =
  ( unit : R →ₗ[R] A )
  ∘ₗ
  ( counit : A →ₗ[R] R )

  right : -- Δ ∘ (S ⊗ id) ∘ μ
  ( mul : A ⊗[R] A →ₗ[R] A )
  ∘ₗ
  ( TensorProduct.map anti LinearMap.id : A ⊗[R] A →ₗ[R] A ⊗[R] A )
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
