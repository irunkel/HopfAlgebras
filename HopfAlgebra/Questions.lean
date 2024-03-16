import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

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

/- When one defines a new type, the instances get deleted,
   it seems.
-/
def sha := bas → ℚ

def sha_smul (q:ℚ) (a:sha) : sha := fun i:bas ↦ q*(a i)

theorem test (a:sha) : sha_smul (1:ℚ) a = a := by
  apply funext
  intro x
  rw [sha_smul]
  simp
