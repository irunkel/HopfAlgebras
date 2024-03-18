import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace Questions

--- QUESTION 1 ---

/- I wanted to make a vector space with basis vectors that
   have specific names I wanted to assign. E.g. -/
inductive bas where
| e : bas
| x : bas
deriving DecidableEq

/- The vector space is then the space of functions from bas
   to the base field, e.g. ℚ. I will do two versions, one
   with abbrev and one with def -/

abbrev Va := bas → ℚ
def Vd := bas → ℚ

/- Question 1.1: This is a hack to test if the given type is
   already known to be an instance of AddcommMonoid. Surely
   there is a better way to do this. How does one do this
   properly? -/
def testinstance (A : Type) [AddCommMonoid A] : Nat := 0

example : testinstance Va = 0 := rfl
--example : testinstance Vd = 0 := rfl -- this fails

/- The answer to Q 1.1 is "inferInstanceAs" -/

instance : AddCommMonoid Vd :=
   inferInstanceAs (AddCommMonoid (bas→ℚ))

example : testinstance Vd = 0 := rfl -- this now works

/- Question 1.2: How can I use "def" and still make Vb not
   forget that it is an AddCommMonoid? I would like Vb to
   remember some of the structure predefined on "bas → ℚ"
   but not all of it. E.g. Vb should not include the fact
   that "bas → ℚ" is already registered as an instance of an
   algebra via point-wise multiplication (I want to define my
   own algebra structure on it). -/

def smul_Vd (q:ℚ) (v:Vd) : Vd := fun (i:bas) ↦ q * (v i)

instance : SMul ℚ Vd where
   smul := smul_Vd

def zero_Vd : Vd := fun _ ↦ 0

example (v:Vd) : smul_Vd (0:ℚ) v = zero_Vd  := by
   apply funext
   intro x
   rw [smul_Vd,zero_Vd]
   simp -- this works fine

example (v:Vd) : (0:ℚ) • v = zero_Vd  := by
   apply funext
   intro x
   rw [zero_Vd]
   sorry -- simp fails at this point

/- Question 1.3: How can I prove this equality? I cannot get it
   to substitute the definition of • as above in the example
   explicitly referencing "smul_Vd".
   (This arose when I wanted to register Vd as an instance of
   AddCommMonoid by hand, when trying to prove the properties
   of nsmul.)
-/
