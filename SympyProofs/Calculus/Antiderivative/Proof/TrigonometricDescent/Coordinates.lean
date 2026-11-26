module

public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Coordinates
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Compiler
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Ground

/-! Separating the two scalar components is an exact field isomorphism at every height. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))]
local notation "E" => WithI (K R 0)

/-- The original field includes into the one over quadratic constants. -/
noncomputable def extendGroundHom : (n : ℕ) → K R n →+* K E n
  | 0 => quadraticConstantHom
  | n+1 => substituteHom (extendGroundHom n) K.gen gen_coordinate_transcendental

@[simp] theorem extendGroundHom_apply (n : ℕ) (z : K R n) :
    extendGroundHom n z = extendGround n z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [extendGroundHom, substituteHom_apply, extendGround, ← funext ih]

@[simp] theorem extendGround_lift {n : ℕ} (z : K R n) :
    extendGround (n+1) (K.lift z) = K.lift (extendGround n z) := by
  simp only [← extendGroundHom_apply, extendGroundHom, substituteHom_lift]

@[simp] theorem extendGround_gen {n : ℕ} :
    extendGround (n+1) (K.gen : K R (n+1)) = K.gen := by
  rw [← extendGroundHom_apply, extendGroundHom, substituteHom_gen]

private theorem lift_C {F : Type} [Field F] [DecidableEq F] (n : ℕ) (c : F) :
    K.lift (K.C c : K F n) = K.C c := by
  apply K.equiv.injective
  simp [K.equiv_lift, K.equiv_C]

/-- The reverse coordinate map is additive and multiplicative. -/
noncomputable def assembleHom (n : ℕ) : WithI (K R n) →+* K E n where
  toFun := assemble n
  map_zero' := by simp [assemble, ← extendGroundHom_apply]
  map_one' := by
    change extendGround n 1 + _ * extendGround n 0 = 1
    simp [← extendGroundHom_apply]
  map_add' x y := by simp [assemble, ← extendGroundHom_apply, mul_add]; ring
  map_mul' x y := by
    let i := (K.C (WithI.imaginary (K R 0)) : K E n)
    have hi : i ^ 2 = -1 := by
      change (K.CRingHom n (WithI.imaginary (K R 0))) ^ 2 = -1
      rw [← map_pow, WithI.imaginary_sq, map_neg, map_one]
    change extendGround n (x*y).re + i * extendGround n (x*y).im =
      (extendGround n x.re + i * extendGround n x.im) *
        (extendGround n y.re + i * extendGround n y.im)
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, neg_one_mul,
      add_zero, ← extendGroundHom_apply, map_add, map_mul, map_neg]
    linear_combination -(extendGroundHom n x.im * extendGroundHom n y.im) * hi

theorem assemble_lift (n : ℕ) (z : WithI (K R n)) :
    assemble (n+1) (WithI.map K.lift z) = K.lift (assemble n z) := by
  simp [assemble, WithI.map, map_add, map_mul, lift_C]

private theorem map_eval {A B C : Type} [Zero A] [DecidableEq A]
    [CommRing B] [DecidableEq B] [CommRing C] [DecidableEq C]
    (h : B →+* C) (f : A → B) (g : A → C) (he : ∀ a, h (f a) = g a)
    (p : Poly A) (z : B) : h ((p.map f).eval z) = (p.map g).eval (h z) := by
  simp only [Poly.eval_eq_eval_coeffs, Poly.coeffs_map]
  rw [Poly.Raw.eval_congr _ (Poly.Raw.rel_trim _), Poly.Raw.eval_congr _ (Poly.Raw.rel_trim _)]
  induction p.coeffs with
  | nil => exact h.map_zero
  | cons a l ih => simp only [List.map_cons, Poly.Raw.eval, map_add, map_mul, he, ih]

private theorem C_constants {F : Type} [Field F] [DecidableEq F] (x : K F 0) :
    K.C (K.toConstants F x) = x := by
  apply (K.constantsEquiv F).injective
  change K.Raw.constantValue F (K.Raw.C (K.toConstants F x)) = K.toConstants F x
  generalize K.toConstants F x = c
  by_cases h : c = 0 <;>
    simp [K.Raw.constantValue, K.Raw.C, K.Raw.ofPoly, MPoly.Raw.C, MPoly.Raw.constantTerm,
      Mono.trim, Poly.Raw.trim, h]

/-- Recombining the computed coordinates recovers the original fraction exactly. -/
theorem assemble_project (n : ℕ) (z : K E n) : assemble n (project n z) = z := by
  induction n with
  | zero =>
    let v := K.toConstants E z
    change K.C (QuadraticAlgebra.C v.re : E) +
      (K.C (WithI.imaginary (K R 0))) * K.C (QuadraticAlgebra.C v.im : E) = z
    change K.CRingHom 0 (QuadraticAlgebra.C v.re : E) +
      K.CRingHom 0 (WithI.imaginary (K R 0)) * K.CRingHom 0 (QuadraticAlgebra.C v.im : E) = z
    rw [← map_mul, ← map_add]
    have hv : (QuadraticAlgebra.C v.re : E) + WithI.imaginary _ * QuadraticAlgebra.C v.im = v :=
      by ext <;> simp [WithI.imaginary]
    rw [hv]
    exact C_constants z
  | succ n ih =>
    let H := assembleHom (R := R) (n+1)
    let phi := fun a => WithI.map (K.lift (R := R)) (project n a)
    let x := (QuadraticAlgebra.C K.gen : WithI (K R (n+1)))
    have hg : H x = K.gen := by simp [H, x, assembleHom, assemble, ← extendGroundHom_apply,
      extendGroundHom, substituteHom_gen]
    have hphi (a : K E n) : H (phi a) = K.lift a := by
      change assemble (n+1) (WithI.map _ (project n a)) = _
      rw [assemble_lift, ih]
    have hp (p : Poly (K E n)) : H ((p.map phi).eval x) = K.joinPoly p := by
      rw [map_eval H phi K.lift hphi, hg, K.joinPoly]
    change H ((z.split.1.map phi).eval x / (z.split.2.map phi).eval x) = z
    rw [map_div₀, hp, hp, ← K.join, K.join_split]

/-- Extracting real and imaginary parts recovers any supplied pair. -/
theorem project_assemble (n : ℕ) (z : WithI (K R n)) : project n (assemble n z) = z :=
  (assembleHom n).injective (assemble_project n _)

/-- Rational functions over quadratic constants are pairs of original rational functions. -/
noncomputable def coordinatesEquiv (n : ℕ) : K E n ≃+* WithI (K R n) :=
  let e : WithI (K R n) ≃+* K E n :=
    { assembleHom (R := R) n with
      invFun := project n
      left_inv := project_assemble n
      right_inv := assemble_project n }
  e.symm

@[simp] theorem coordinatesEquiv_apply (n : ℕ) (z : K E n) :
    coordinatesEquiv n z = project n z := rfl

@[simp] theorem coordinatesEquiv_symm_apply (n : ℕ) (z : WithI (K R n)) :
    (coordinatesEquiv n).symm z = assemble n z := rfl

theorem project_extendGround (n : ℕ) (z : K R n) :
    project n (extendGround n z) = QuadraticAlgebra.C z := by
  have h := project_assemble n (QuadraticAlgebra.C z)
  simpa [assemble, ← extendGroundHom_apply] using h

/-- Conjugation of the coefficients is a field automorphism. -/
noncomputable def conjugateHom (n : ℕ) : K E n ≃+* K E n :=
  (coordinatesEquiv n).trans
    (QuadraticAlgebra.starAlgEquiv.toRingEquiv.trans (coordinatesEquiv n).symm)

@[simp] theorem conjugateHom_apply (n : ℕ) (z : K E n) : conjugateHom n z = conjugate n z := by
  change (coordinatesEquiv n).symm (star (coordinatesEquiv n z)) = _
  rw [coordinatesEquiv_apply]
  rfl

theorem project_conjugate (n : ℕ) (z : K E n) : project n (conjugate n z) = star (project n z) :=
  project_assemble _ _

end SympyProofs.Calculus.Antiderivative.Trigonometric
