import SympyProofs.LambertW.Complex.PrincipalRange

/-!
# Conjugation symmetry and reduction to the upper half-plane

Both the principal slit domain and its proposed inverse range are invariant
under conjugation. Unique solvability transfers between conjugate inputs.
Together with the real-input theorem, this reduces global unique solvability
to the upper half-plane; that remaining hypothesis is not assumed as an axiom.
-/

namespace LambertW.Complex

open Set ComplexConjugate

@[simp] theorem mulExp_conj (w : ℂ) : mulExp (conj w) = conj (mulExp w) := by
  simp [mulExp, Complex.exp_conj]

@[simp] theorem conj_mem_principalDomain (z : ℂ) :
    conj z ∈ principalDomain ↔ z ∈ principalDomain := by
  simp [principalDomain]

@[simp] theorem conj_mem_principalRange (w : ℂ) :
    conj w ∈ principalRange ↔ w ∈ principalRange := by
  simp only [principalRange, mem_ofPred_eq, Complex.conj_im, Complex.conj_re,
    mem_Ioo, Real.cos_neg, Real.sin_neg, neg_eq_zero, neg_ne_zero, neg_neg,
    div_neg, neg_div, neg_mul]
  constructor <;> rintro ⟨⟨hlo, hhi⟩, hr, hb⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, hr, hb⟩

/-- Conjugation transports a principal-region solution to the conjugate input. -/
theorem principal_solution_conj_iff (w z : ℂ) :
    (conj w ∈ principalRange ∧ mulExp (conj w) = conj z) ↔
      (w ∈ principalRange ∧ mulExp w = z) := by
  rw [conj_mem_principalRange, mulExp_conj]
  constructor
  · rintro ⟨hw, he⟩
    exact ⟨hw, by simpa using congrArg conj he⟩
  · rintro ⟨hw, he⟩
    exact ⟨hw, congrArg conj he⟩

/-- Unique solvability is invariant under conjugating the input. -/
theorem existsUnique_principalRange_mulExp_conj_iff (z : ℂ) :
    (∃! w : ℂ, w ∈ principalRange ∧ mulExp w = conj z) ↔
      (∃! w : ℂ, w ∈ principalRange ∧ mulExp w = z) := by
  have transfer : ∀ z : ℂ,
      (∃! w : ℂ, w ∈ principalRange ∧ mulExp w = z) →
      (∃! w : ℂ, w ∈ principalRange ∧ mulExp w = conj z) := by
    intro z ⟨w, hw, hu⟩
    refine ⟨conj w, (principal_solution_conj_iff w z).mpr hw, ?_⟩
    intro v hv
    have hv' : conj v ∈ principalRange ∧ mulExp (conj v) = z := by
      simpa using (principal_solution_conj_iff v (conj z)).mpr hv
    have h := congrArg conj (hu (conj v) hv')
    simpa using h
  constructor
  · intro h
    simpa using transfer (conj z) h
  · exact transfer z

/-- It suffices to prove unique solvability for inputs with positive imaginary part. -/
theorem existsUnique_principalRange_mulExp_of_upper
    (hupper : ∀ z : ℂ, 0 < z.im →
      ∃! w : ℂ, w ∈ principalRange ∧ mulExp w = z)
    {z : ℂ} (hz : z ∈ principalDomain) :
    ∃! w : ℂ, w ∈ principalRange ∧ mulExp w = z := by
  rcases lt_trichotomy z.im 0 with hi | hi | hi
  · apply (existsUnique_principalRange_mulExp_conj_iff z).mp
    apply hupper
    simpa using hi
  · have hr : -Real.exp (-1) < z.re := by
      simpa [principalDomain, hi] using hz
    have heq : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    rw [heq]
    exact existsUnique_principalRange_mulExp_ofReal hr
  · exact hupper z hi

/-- Any principal-region preimage of an upper-half-plane input also lies above the real axis. -/
theorem im_pos_of_principal_solution {w z : ℂ}
    (hw : w ∈ principalRange) (he : mulExp w = z) (hz : 0 < z.im) : 0 < w.im := by
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · have h := mulExp_im_neg_of_mem_principalRange hw hi
    rw [he] at h
    linarith
  · have h := (mulExp_im_eq_zero_iff_of_mem_principalRange hw).mpr hi
    rw [he] at h
    linarith
  · exact hi

end LambertW.Complex
