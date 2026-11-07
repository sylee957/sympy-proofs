module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.PrincipalEndomorphism
public import SympyProofs.LinearAlgebra.MatrixLogarithm.Logarithm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# The principal matrix logarithm

Every finite complex square matrix whose spectrum avoids the closed negative
real axis has exactly one logarithm with spectrum in `-π < im z < π`.
This includes matrices with nontrivial Jordan blocks. Uniqueness makes this
logarithm compatible with transpose, adjoint, and entrywise conjugation.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectrum avoids `(-∞, 0]`, including zero. -/
def HasSlitSpectrum (A : Matrix n n ℂ) : Prop := spectrum ℂ A ⊆ Complex.slitPlane

/-- The equation and open-strip condition characterizing the principal logarithm. -/
def IsPrincipalLogarithm (A L : Matrix n n ℂ) : Prop :=
  exp L = A ∧ spectrum ℂ L ⊆ principalStrip

/-- The general principal logarithm theorem. No diagonalizability is required. -/
theorem existsUnique_principalLogarithm (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    ∃! L : Matrix n n ℂ, IsPrincipalLogarithm A L := by
  let e := (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] End ℂ (n → ℂ))
  obtain ⟨l, hl, hu⟩ := existsUnique_endLogarithm (e A)
    (by simpa only [HasSlitSpectrum, AlgEquiv.spectrum_eq] using hA)
  refine ⟨e.symm l, ⟨?_, ?_⟩, ?_⟩
  · apply e.injective
    change Matrix.toLinAlgEquiv' (exp (e.symm l)) = e A
    rw [toLin_exp]
    simpa only [← show e = Matrix.toLinAlgEquiv' from rfl, AlgEquiv.apply_symm_apply] using hl.1
  · simpa only [AlgEquiv.spectrum_eq] using hl.2
  · intro L hL
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    apply hu
    constructor
    · rw [← toLin_exp, hL.1]
    · simpa only [AlgEquiv.spectrum_eq] using hL.2

/-- The principal logarithm on the slit-spectrum domain, with value `0` elsewhere.
The domain hypothesis is required by its correctness theorems, not by this function. -/
noncomputable def principalLog (A : Matrix n n ℂ) : Matrix n n ℂ := by
  classical
  exact if hA : HasSlitSpectrum A then (existsUnique_principalLogarithm A hA).choose else 0

theorem principalLog_of_not_hasSlitSpectrum (A : Matrix n n ℂ) (hA : ¬HasSlitSpectrum A) :
    principalLog A = 0 := by
  simp only [principalLog, dite_eq_right hA]

theorem principalLog_spec (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    IsPrincipalLogarithm A (principalLog A) := by
  simpa only [principalLog, dite_eq_left hA] using
    (existsUnique_principalLogarithm A hA).choose_spec.1

@[simp] theorem exp_principalLog (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    exp (principalLog A) = A := (principalLog_spec A hA).1

theorem spectrum_principalLog (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    spectrum ℂ (principalLog A) ⊆ principalStrip := (principalLog_spec A hA).2

theorem principalLog_unique (A L : Matrix n n ℂ) (hA : HasSlitSpectrum A)
    (hL : IsPrincipalLogarithm A L) : L = principalLog A := by
  simpa only [principalLog, dite_eq_left hA] using
    (existsUnique_principalLogarithm A hA).choose_spec.2 L hL

/-- Connect the principal logarithm to the chosen-logarithm API. -/
noncomputable def principalLogarithm (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) : Logarithm A :=
  ⟨principalLog A, exp_principalLog A hA⟩

theorem HasSlitSpectrum.transpose {A : Matrix n n ℂ} (hA : HasSlitSpectrum A) :
    HasSlitSpectrum Aᵀ := by
  simpa only [HasSlitSpectrum, Matrix.spectrum_transpose] using hA

theorem HasSlitSpectrum.conjTranspose {A : Matrix n n ℂ} (hA : HasSlitSpectrum A) :
    HasSlitSpectrum Aᴴ := by
  change spectrum ℂ (star A) ⊆ Complex.slitPlane
  rw [spectrum.map_star]
  intro z hz
  have h := hA (show star z ∈ spectrum ℂ A from hz)
  simpa only [Complex.mem_slitPlane_iff, Complex.star_def, Complex.conj_re,
    Complex.conj_im, neg_ne_zero] using h

theorem HasSlitSpectrum.conjugate {A : Matrix n n ℂ} (hA : HasSlitSpectrum A) :
    HasSlitSpectrum (A.map star) := hA.conjTranspose.transpose

theorem principalLog_transpose (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    principalLog Aᵀ = (principalLog A)ᵀ := by
  symm
  apply principalLog_unique _ _ hA.transpose
  constructor
  · rw [exp_transpose, exp_principalLog A hA]
  · simpa only [Matrix.spectrum_transpose] using spectrum_principalLog A hA

theorem principalLog_conjTranspose (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    principalLog Aᴴ = (principalLog A)ᴴ := by
  symm
  apply principalLog_unique _ _ hA.conjTranspose
  constructor
  · rw [exp_conjTranspose, exp_principalLog A hA]
  · change spectrum ℂ (star (principalLog A)) ⊆ principalStrip
    rw [spectrum.map_star]
    intro z hz
    have h := spectrum_principalLog A hA (show star z ∈ spectrum ℂ (principalLog A) from hz)
    change -Real.pi < z.im ∧ z.im < Real.pi
    change -Real.pi < -z.im ∧ -z.im < Real.pi at h
    constructor <;> linarith [h.1, h.2]

theorem principalLog_map_star (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    principalLog (A.map star) = (principalLog A).map star := by
  change principalLog Aᴴᵀ = (principalLog A)ᴴᵀ
  rw [principalLog_transpose Aᴴ hA.conjTranspose, principalLog_conjTranspose A hA]

end SympyProofs.MatrixExponential
