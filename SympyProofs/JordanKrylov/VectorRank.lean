import SympyProofs.JordanKrylov.KernelChain
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Definition 2: the rank of a vector with respect to f

This is the least exponent ℓ for which f(A)^ℓ u = 0, not matrix rank.
The definition takes only A, f, and u. Kernel-membership assumptions belong
to the theorems, not to the value of the rank. On the union of the power
kernels it is the least annihilating exponent. Outside that union it is
defined to be zero; this default does not assert annihilation. The zero
vector also has rank zero. Internally, rank uses mathlib's `Submodule.pOrder`
on the f-primary torsion submodule of `Module.AEval' A.mulVecLin`.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

/-- The f-primary part of the polynomial-action module, using mathlib's torsion submodule.
Its elements are precisely the vectors annihilated by some power of f(A). -/
noncomputable def fPrimaryModule (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :=
  Submodule.torsion' K[X] (Module.AEval' A.mulVecLin) (Submonoid.powers f)

private theorem pow_smul_aeval_eq_zero_iff (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) (k : ℕ) :
    f ^ k • Module.AEval'.of A.mulVecLin u = 0 ↔ u ∈ powerKernel K A f k := by
  change (aeval A.mulVecLin (f ^ k)) u = 0 ↔ _
  have heval := Polynomial.aeval_algHom_apply Matrix.toLinAlgEquiv' A (f ^ k)
  change aeval A.mulVecLin (f ^ k) = Matrix.toLinAlgEquiv' (aeval A (f ^ k)) at heval
  rw [heval]
  change (aeval A (f ^ k)) *ᵥ u = 0 ↔ _
  rw [map_pow]
  rfl

/-- Membership in the torsion submodule is membership in some power kernel. -/
theorem mem_fPrimaryModule_iff (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) :
    Module.AEval'.of A.mulVecLin u ∈ fPrimaryModule K A f ↔
      ∃ k, u ∈ powerKernel K A f k := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨k, hk⟩ := a.property
    refine ⟨k, (pow_smul_aeval_eq_zero_iff K A f u k).mp ?_⟩
    change (a : K[X]) • Module.AEval'.of A.mulVecLin u = 0 at ha
    rwa [← hk] at ha
  · rintro ⟨k, hk⟩
    exact ⟨⟨f ^ k, ⟨k, rfl⟩⟩, (pow_smul_aeval_eq_zero_iff K A f u k).mpr hk⟩

/-- Rank is mathlib's p-order with p = f on the f-primary module.
Decidability is supplied classically inside the definition. If no power
annihilates u, return zero by convention. -/
noncomputable def vectorRank (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) : ℕ := by
  classical
  exact if h : Module.AEval'.of A.mulVecLin u ∈ fPrimaryModule K A f then
    Submodule.pOrder (p := f)
      (Submodule.torsion'_isTorsion' (R := K[X]) (M := Module.AEval' A.mulVecLin)
        (Submonoid.powers f)) ⟨Module.AEval'.of A.mulVecLin u, h⟩
    else 0

/-- The previous definition is retained as a proved characterization:
rank is the least annihilating exponent when one exists, and zero otherwise. -/
theorem vectorRank_eq_find_or_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) :
    vectorRank K A f u = (by
      classical
      exact if h : ∃ ℓ, u ∈ powerKernel K A f ℓ then Nat.find h else 0) := by
  classical
  unfold vectorRank
  by_cases h : Module.AEval'.of A.mulVecLin u ∈ fPrimaryModule K A f
  · rw [dite_eq_left h, dite_eq_left ((mem_fPrimaryModule_iff K A f u).mp h)]
    unfold Submodule.pOrder
    apply Nat.find_congr'
    intro k
    constructor
    · intro hz
      exact (pow_smul_aeval_eq_zero_iff K A f u k).mp (congrArg Subtype.val hz)
    · intro hz
      exact Subtype.ext ((pow_smul_aeval_eq_zero_iff K A f u k).mpr hz)
  · rw [dite_eq_right h, dite_eq_right (fun hex => h ((mem_fPrimaryModule_iff K A f u).mpr hex))]

/-- On an f-primary vector, rank is the least annihilating exponent. -/
theorem vectorRank_eq_find (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (h : ∃ ℓ, u ∈ powerKernel K A f ℓ) :
    vectorRank K A f u = (by classical exact Nat.find h) := by
  classical
  rw [vectorRank_eq_find_or_zero]
  simp only [dite_eq_left h]

/-- Outside the union of the power kernels, rank is zero by convention. -/
theorem vectorRank_eq_zero_of_not_exists (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (h : ¬ ∃ ℓ, u ∈ powerKernel K A f ℓ) : vectorRank K A f u = 0 := by
  classical
  rw [vectorRank_eq_find_or_zero]
  simp only [dite_eq_right h]

@[simp] theorem vectorRank_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    vectorRank K A f (0 : Fin n → K) = 0 := by
  classical
  have h : ∃ ℓ, (0 : Fin n → K) ∈ powerKernel K A f ℓ := ⟨0, by simp⟩
  rw [vectorRank_eq_find K A f 0 h]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h (by simp : (0 : Fin n → K) ∈ powerKernel K A f 0))

/-- The rank is an exponent that annihilates u. -/
theorem mem_powerKernel_vectorRank (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    {ℓbar : ℕ} (hu : u ∈ powerKernel K A f ℓbar) :
    u ∈ powerKernel K A f (vectorRank K A f u) := by
  classical
  rw [vectorRank_eq_find K A f u ⟨ℓbar, hu⟩]
  exact Nat.find_spec (show ∃ ℓ, u ∈ powerKernel K A f ℓ from ⟨ℓbar, hu⟩)

/-- For the paper's nonzero vector, 1 ≤ rank_f(u) ≤ ℓbar. -/
theorem vectorRank_bounds (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu0 : u ≠ 0) {ℓbar : ℕ} (hu : u ∈ powerKernel K A f ℓbar) :
    1 ≤ vectorRank K A f u ∧ vectorRank K A f u ≤ ℓbar := by
  classical
  constructor
  · have h := mem_powerKernel_vectorRank K A f u hu
    by_contra hpos
    have hz : vectorRank K A f u = 0 := by omega
    rw [hz, powerKernel_zero, Submodule.mem_bot] at h
    exact hu0 h
  · rw [vectorRank_eq_find K A f u ⟨ℓbar, hu⟩]
    exact Nat.find_min' ⟨ℓbar, hu⟩ hu

/-- Definition 2: rank_f(u) = ℓ exactly when u belongs to the ℓ-th kernel
but not the preceding kernel. -/
theorem vectorRank_eq_iff (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    {ℓbar : ℕ} (hu : u ∈ powerKernel K A f ℓbar) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    vectorRank K A f u = ℓ ↔
      u ∈ (powerKernel K A f ℓ : Set (Fin n → K)) \
        (powerKernel K A f (ℓ - 1) : Set (Fin n → K)) := by
  classical
  rw [vectorRank_eq_find K A f u ⟨ℓbar, hu⟩]
  rw [Nat.find_eq_iff]
  change (_ ∧ ∀ k < ℓ, u ∉ powerKernel K A f k) ↔
    (u ∈ powerKernel K A f ℓ ∧ u ∉ powerKernel K A f (ℓ - 1))
  constructor
  · rintro ⟨hmem, hmin⟩
    exact ⟨hmem, hmin (ℓ - 1) (by omega)⟩
  · rintro ⟨hmem, hprev⟩
    refine ⟨hmem, fun k hk hku => hprev ?_⟩
    exact powerKernel_le K A f (by omega : k ≤ ℓ - 1) hku

/-- Among vectors annihilated by a power, rank zero characterizes the zero vector. -/
theorem vectorRank_eq_zero_iff (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu : u ∈ powerKernel K A f ℓbar) : vectorRank K A f u = 0 ↔ u = 0 := by
  constructor
  · intro hr
    have h := mem_powerKernel_vectorRank K A f u hu
    simpa [hr] using h
  · rintro rfl
    exact vectorRank_zero K A f

end SympyProofs.JordanKrylov
