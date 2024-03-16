import Mathlib.LinearAlgebra.StdBasis

/- Take any commutative ring
   This does not work with a semiring, btw,
   because the examples below use substraction.

    variable {R : Type} [CommSemiring R] -- fails
-/
#eval Lean.versionString

variable {R : Type} [CommRing R]

/- alternatively: take a concret ring (and clearly
   "def R := ℤ" does not work - ha, ha, I have no idea
   what is going on)

  abbrev R := ℤ
-/

/- my beautiful type with two elements -/
inductive two where
| a : two
| b : two
deriving DecidableEq

/- apparently I have to prove that two is finite
   but I did not have the energy yet to show that the
   type Fin 2 has exactly the two elements 0 and 1.
   Should not be too hard, as Fin 2 is a natural number
   and the proof that it is less than 2.
-/
def isEquivTwo : Equiv two (Fin 2) :=
  {
    toFun := fun x ↦ match x with
      | two.a => 0
      | two.b => 1
    invFun := fun x ↦ match x with
      | 0 => two.a
      | 1 => two.b
    left_inv := by
      intro x
      cases x <;> rfl
    right_inv := by
      intro x
      match x with
        | 0 => rfl
        | 1 => rfl
        /- Ingo: Gute Idee mit "match", dann ist es noch
           kürzer es gleich damit zu machen -/
/-
      have : x=0 ∨ x=1 := match x with
        | 0 => by exact Or.inl rfl
        | 1 => by exact Or.inr rfl
      /- David: added this proof of have x=0 or x=1-/
      cases this
      case inl h =>
        simp [h]
      case inr h =>
        simp [h]
-/
  }

/- It wants that at some point but I have no idea how
   one goes about proving that
-/


/- Ingo: apparently one can also write "deriving DecidableEq"
   in the definition above. Again: no idea what is going on.
   Found that in the Lean manual.

noncomputable instance inst_dec_eq : DecidableEq two := by
  intro x y
  exact Classical.dec (x = y)
-/

/- My beautiful type with two elements is indeed finite.
   This is established by handing it an equivalence of the
   given type to "Fin n".
-/
instance inst_finite_two : Finite two := Finite.intro isEquivTwo

/- David: I needed the following for the next definition bas to compile-/
noncomputable instance inst_finite_two2 : Fintype two:= by exact Fintype.ofFinite two

/- the library function that creates a basis bas of the
   R-module (two -> R), ie on functions two->R by
   taking the delta-function basis. Leaving our the
   "noncomputable" does raise an error
-/

/- David: For the below, I needed inst_finite_two2 : Fintype two for `bas' to compile-/
noncomputable def bas : Basis two R (two → R) := Pi.basisFun R two
--

/- "bas two.a" is the function two -> R corresponding to
   two.a, and it is indeed 1 on two.a and 0 on two.b -/
example : (bas two.a) two.a = (1:R) := by rw [bas]; simp
example : (bas two.a) two.b = (0:R) := by rw [bas]; simp

/- bas.repr (basis el) also gives back the function
   it represents
-/
example : bas.repr (bas two.a) two.a = (1:R) := by
  rw [bas]; rw [Pi.basisFun_repr]; simp
example : bas.repr (bas two.a) two.b = (0:R) := by
  rw [bas]; rw [Pi.basisFun_repr]; simp

/-
  Two ways to create a linear map defined in terms of
  a basis:
    g1 - describe explicitly the function two->R assigned
         to each element of two
    g2 - give a linear combination of basis vectors
         for each basis element
-/
def g1 : two → (two → R)
| _ , _ => (1:R)

noncomputable def g2 : two → (two → R)
| two.a => (bas two.a) + (bas two.b)
| two.b => (bas two.a) - 2*(bas two.b)

/- The corresponding linear maps are created by
   Basis.constr. The notation
-/
noncomputable def g1lin : (two → R) →ₗ[R] (two → R)
  := Basis.constr bas R g1
noncomputable def g2lin : (two → R) →ₗ[R] (two → R)
  := Basis.constr bas R g2

/- The linear map can be applied to basis vectors and
   there are pre-defined theorems to reduce this back
   to the underlying functions g1, g2.
   The ... : (two → R) is there to help lean find the
   correct type. Else this fails.
-/
example : (g1lin (bas two.a) : (two → R) )
  = (bas two.a) + (bas two.b) := by
  rw [g1lin]
  rw [Basis.constr_basis]
  apply funext -- surely there is a better way to do this?
  intro x
  cases x
  repeat simp; rw[g1,bas]; simp

example : (g1lin (bas two.b) : (two → R))
  = (bas two.a) + (bas two.b) := by
  rw [g1lin]
  rw [Basis.constr_basis]
  apply funext
  intro x
  cases x
  repeat simp; rw[g1,bas]; simp

/-
  The g2lin example is nicer as it produces the correct
  vector directly without comparing functions on each value.
-/
theorem g2bas1 : (g2lin (bas two.a) : (two → R))
  = (bas two.a) + (bas two.b) := by
  rw [g2lin]
  rw [Basis.constr_basis]
  rw [g2]

theorem g2bas2 : (g2lin (bas two.b) : (two → R))
  = (bas two.a) - 2*(bas two.b) := by
  rw [g2lin]
  rw [Basis.constr_basis]
  rw [g2]

-- hurray, a linear compbination
example : (g2lin ((bas two.a) - (bas two.b)) : (two → R))
  = 3*(bas two.b) := by
  calc
    g2lin ((bas two.a) - (bas two.b))
      = g2lin (bas two.a) - g2lin (bas two.b) := by simp
    _ = ((bas two.a) + (bas two.b)) - ((bas two.a) - 2*(bas two.b : two → R))
        := by rw [g2bas1,g2bas2]
    _ = 3*(bas two.b) := by ring
