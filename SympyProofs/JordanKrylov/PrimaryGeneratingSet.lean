import SympyProofs.JordanKrylov.BasisMinimalPolynomial
import SympyProofs.JordanKrylov.KrylovGeneratingSet
import SympyProofs.JordanKrylov.KrylovDecomposition
import SympyProofs.JordanKrylov.JordanKrylovBasis
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Primary generators obtained from a spanning family

Section 4.1, generalized to finite spanning families: factor each vector's minimal annihilating polynomial as
`f ^ m i * g i`, and retain `g i (A) (e i)` when `m i > 0`.
-/

namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped BigOperators

/-- Equation (10), factorization: extract the full multiplicity of f. -/
theorem minimalAnnihilatingPolynomial_exists_primary_factor (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) :
    ∃ g : K[X], minimalAnnihilatingPolynomial K A u =
      f ^ multiplicity f (minimalAnnihilatingPolynomial K A u) * g :=
  pow_multiplicity_dvd f (minimalAnnihilatingPolynomial K A u)

/-- Equation (10), coprimality: any cofactor after extracting the full
multiplicity of the monic irreducible f is coprime to f. -/
theorem minimalAnnihilatingPolynomial_primary_factor_isCoprime
    (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (g : K[X])
    (hfactor : minimalAnnihilatingPolynomial K A u =
      f ^ multiplicity f (minimalAnnihilatingPolynomial K A u) * g) :
    IsCoprime f g := by
  have hfin := Polynomial.finiteMultiplicity_of_degree_pos_of_monic
    (Polynomial.degree_pos_of_irreducible hf) hm
    (minimalAnnihilatingPolynomial_monic K A u).ne_zero
  obtain ⟨g', hfactor', hnot⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have heq : g = g' := mul_left_cancel₀ (pow_ne_zero _ hf.ne_zero)
    (hfactor.symm.trans hfactor')
  subst g'
  exact (hf.isCoprime_or_dvd g).resolve_right hnot

/-- The multiplicity of f in the matrix minimal polynomial is the maximum
of its multiplicities in the minimal annihilating polynomials of a spanning family. -/
theorem multiplicity_minpoly_eq_max_spanning (K : Subfield ℂ) {n : ℕ}
    {ι : Type*} [Fintype ι] (A : Matrix (Fin n) (Fin n) K)
    (e : ι → (Fin n → K)) (he : Submodule.span K (Set.range e) = ⊤) (f : K[X]) (hf : Irreducible f) (hm : f.Monic) :
    multiplicity f (minpoly K A) = Finset.univ.sup
      (fun i => multiplicity f (minimalAnnihilatingPolynomial K A (e i))) := by
  classical
  let m := fun i => multiplicity f (minimalAnnihilatingPolynomial K A (e i))
  let M := Finset.univ.sup m
  have hfin := Polynomial.finiteMultiplicity_of_degree_pos_of_monic
    (Polynomial.degree_pos_of_irreducible hf) hm (minpoly.monic (Matrix.isIntegral A)).ne_zero
  apply le_antisymm
  · have hfac (i : ι) := minimalAnnihilatingPolynomial_exists_primary_factor K A f (e i)
    choose g hg using hfac
    have hcop (i : ι) : IsCoprime f (g i) :=
      minimalAnnihilatingPolynomial_primary_factor_isCoprime K A f hf hm (e i) (g i) (hg i)
    let G := ∏ i, g i
    have hc : IsCoprime f G := IsCoprime.prod_right (fun i _ => hcop i)
    have hd : minpoly K A ∣ f ^ M * G := by
      apply (minpoly_dvd_iff_spanning_annihilators_dvd K A e he _).mpr
      intro i
      rw [hg i]
      exact mul_dvd_mul (pow_dvd_pow f (Finset.le_sup (f := m) (Finset.mem_univ i)))
        (Finset.dvd_prod_of_mem g (Finset.mem_univ i))
    by_contra hle
    change ¬ multiplicity f (minpoly K A) ≤ M at hle
    have hpow : f ^ (M + 1) ∣ f ^ M * G :=
      (pow_dvd_of_le_multiplicity (by omega)).trans hd
    rw [pow_succ] at hpow
    have hdiv : f ∣ G := (mul_dvd_mul_iff_left (pow_ne_zero M hf.ne_zero)).mp hpow
    exact (hf.dvd_iff_not_isCoprime.mp hdiv) hc
  · apply Finset.sup_le
    intro i _
    exact hfin.le_multiplicity_of_pow_dvd
      ((pow_multiplicity_dvd f (minimalAnnihilatingPolynomial K A (e i))).trans
        (minimalAnnihilatingPolynomial_dvd_minpoly K A (e i)))

/-- The multiplicity of f in the matrix minimal polynomial is the maximum
of its multiplicities in the minimal annihilating polynomials of a basis. -/
theorem multiplicity_minpoly_eq_max_basis (K : Subfield ℂ) {n : ℕ}
    {ι : Type*} [Fintype ι] (A : Matrix (Fin n) (Fin n) K)
    (e : Module.Basis ι K (Fin n → K)) (f : K[X]) (hf : Irreducible f) (hm : f.Monic) :
    multiplicity f (minpoly K A) = Finset.univ.sup
      (fun i => multiplicity f (minimalAnnihilatingPolynomial K A (e i))) :=
  multiplicity_minpoly_eq_max_spanning K A e e.span_eq f hf hm

/-- The indices in `𝓔_f`, whose annihilators contain a positive power of f. -/
def primaryBasisIndices {ι : Type*} (m : ι → ℕ) : Set ι := {i | 0 < m i}

/-- The paper's generating set `𝓥 = {g_e(A)e | e ∈ 𝓔_f}`. -/
noncomputable def primaryGeneratingSet (K : Subfield ℂ) {n : ℕ} {ι : Type*}
    (A : Matrix (Fin n) (Fin n) K) (e : ι → (Fin n → K))
    (m : ι → ℕ) (g : ι → K[X]) : Set (Fin n → K) :=
  (fun i => aeval A (g i) *ᵥ e i) '' primaryBasisIndices m

theorem primaryGeneratingSet_finite (K : Subfield ℂ) {n : ℕ} {ι : Type*} [Finite ι]
    (A : Matrix (Fin n) (Fin n) K) (e : ι → (Fin n → K))
    (m : ι → ℕ) (g : ι → K[X]) : (primaryGeneratingSet K A e m g).Finite :=
  (Set.toFinite _).image _

/-- Each cofactor vector lies in the primary kernel at its own exponent. -/
theorem cofactorVector_mem_powerKernel (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (m : ℕ) (g : K[X])
    (hfactor : minimalAnnihilatingPolynomial K A u = f ^ m * g) :
    aeval A g *ᵥ u ∈ powerKernel K A f m := by
  have h := minimalAnnihilatingPolynomial_annihilates K A u
  rw [hfactor, map_mul, map_pow, ← Matrix.mulVec_mulVec] at h
  exact h

/-- The cofactor of a basis vector belongs to the primary kernel at the
multiplicity of f in the matrix minimal polynomial, as in Section 4.1. -/
theorem basisCofactorVector_mem_powerKernel_minpoly (K : Subfield ℂ) {n : ℕ}
    {ι : Type*} [Fintype ι] (A : Matrix (Fin n) (Fin n) K)
    (e : Module.Basis ι K (Fin n → K)) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (i : ι) (g : K[X])
    (hfactor : minimalAnnihilatingPolynomial K A (e i) =
      f ^ multiplicity f (minimalAnnihilatingPolynomial K A (e i)) * g) :
    aeval A g *ᵥ e i ∈ powerKernel K A f (multiplicity f (minpoly K A)) := by
  have hbound : multiplicity f (minimalAnnihilatingPolynomial K A (e i)) ≤
      multiplicity f (minpoly K A) := by
    rw [multiplicity_minpoly_eq_max_basis K A e f hf hm]
    exact Finset.le_sup (f := fun j =>
      multiplicity f (minimalAnnihilatingPolynomial K A (e j))) (Finset.mem_univ i)
  exact powerKernel_monotone K A f hbound
    (cofactorVector_mem_powerKernel K A f (e i) _ g hfactor)

/-- Proposition 16 for a finite spanning family: the cofactor vectors form a Krylov generating set.
Any common upper bound on the exponents works, including their maximum.
The coprime factorizations suffice without a matrix minimal-polynomial hypothesis. -/
theorem primaryGeneratingSet_isKrylovGeneratingSet (K : Subfield ℂ) {n ℓbar : ℕ}
    {ι : Type*} [Fintype ι] (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (e : ι → (Fin n → K)) (he : Submodule.span K (Set.range e) = ⊤) (m : ι → ℕ) (g : ι → K[X])
    (hfactor : ∀ i, minimalAnnihilatingPolynomial K A (e i) = f ^ m i * g i)
    (hcoprime : ∀ i, IsCoprime f (g i)) (hbound : ∀ i, m i ≤ ℓbar) :
    IsKrylovGeneratingSet K A (powerKernel K A f ℓbar)
      (primaryGeneratingSet K A e m g) := by
  classical
  let W := ⨆ w ∈ primaryGeneratingSet K A e m g, krylovSpace K A w
  have hgen (i : ι) : krylovSpace K A (aeval A (g i) *ᵥ e i) ≤ W := by
    by_cases hi : 0 < m i
    · exact le_iSup_of_le (aeval A (g i) *ᵥ e i)
        (le_iSup (fun _ : aeval A (g i) *ᵥ e i ∈ primaryGeneratingSet K A e m g =>
          krylovSpace K A (aeval A (g i) *ᵥ e i)) ⟨i, hi, rfl⟩)
    · have hm : m i = 0 := by omega
      have hz := cofactorVector_mem_powerKernel K A f (e i) (m i) (g i) (hfactor i)
      simp only [hm, powerKernel_zero, Submodule.mem_bot] at hz
      simp [hz, krylovSpace_zero]
  have hle : W ≤ powerKernel K A f ℓbar := by
    apply iSup_le
    intro w
    apply iSup_le
    rintro ⟨i, hi, rfl⟩
    exact krylovSpace_le_powerKernel K A f _ ℓbar
      (powerKernel_monotone K A f (hbound i)
        (cofactorVector_mem_powerKernel K A f (e i) (m i) (g i) (hfactor i)))
  change powerKernel K A f ℓbar = W
  apply le_antisymm _ hle
  intro v hv
  let G : K[X] := ∏ i, g i
  have hc : IsCoprime (f ^ ℓbar) G :=
    (IsCoprime.prod_right (fun i _ => hcoprime i)).pow_left
  obtain ⟨a, b, hab⟩ := hc
  have hbv : aeval A (G * b) *ᵥ v = v := by
    have hh := congrArg (fun p : K[X] => aeval A p *ᵥ v) hab
    simp only [map_add, map_mul, map_pow, map_one, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at hh
    rw [(mem_powerKernel K A f ℓbar v).mp hv, Matrix.mulVec_zero, zero_add] at hh
    simpa [mul_comm G b, map_mul, ← Matrix.mulVec_mulVec] using hh
  rw [← hbv, map_mul, ← Matrix.mulVec_mulVec]
  let x := aeval A b *ᵥ v
  change aeval A G *ᵥ x ∈ W
  have hall : Submodule.span K (Set.range e) ≤ W.comap (aeval A G).mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change aeval A G *ᵥ e i ∈ W
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem g (Finset.mem_univ i)
    apply hgen i
    apply (mem_krylovSpace_iff K A _ _).mpr
    refine ⟨q, ?_⟩
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm q, ← hq]
  rw [he] at hall
  exact hall (Submodule.mem_top : x ∈ (⊤ : Submodule K (Fin n → K)))

/-- Proposition 16 with the paper's exponent `ℓbar = max i, m i`.
The empty maximum is zero, so this also covers the zero-dimensional space. -/
theorem primaryGeneratingSet_isKrylovGeneratingSet_max (K : Subfield ℂ) {n : ℕ}
    {ι : Type*} [Fintype ι] (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (e : ι → (Fin n → K)) (he : Submodule.span K (Set.range e) = ⊤) (m : ι → ℕ) (g : ι → K[X])
    (hfactor : ∀ i, minimalAnnihilatingPolynomial K A (e i) = f ^ m i * g i)
    (hcoprime : ∀ i, IsCoprime f (g i)) :
    IsKrylovGeneratingSet K A (powerKernel K A f (Finset.univ.sup m))
      (primaryGeneratingSet K A e m g) :=
  primaryGeneratingSet_isKrylovGeneratingSet K A f e he m g hfactor hcoprime
    (fun i => Finset.le_sup (f := m) (Finset.mem_univ i))

/-- Proposition 16 using the multiplicity in the matrix minimal polynomial
as the exponent of the primary kernel. -/
theorem primaryGeneratingSet_isKrylovGeneratingSet_minpoly (K : Subfield ℂ) {n : ℕ}
    {ι : Type*} [Fintype ι] (A : Matrix (Fin n) (Fin n) K)
    (e : ι → (Fin n → K)) (he : Submodule.span K (Set.range e) = ⊤) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (g : ι → K[X])
    (hfactor : ∀ i, minimalAnnihilatingPolynomial K A (e i) =
      f ^ multiplicity f (minimalAnnihilatingPolynomial K A (e i)) * g i) :
    IsKrylovGeneratingSet K A (powerKernel K A f (multiplicity f (minpoly K A)))
      (primaryGeneratingSet K A e
        (fun i => multiplicity f (minimalAnnihilatingPolynomial K A (e i))) g) := by
  rw [multiplicity_minpoly_eq_max_spanning K A e he f hf hm]
  exact primaryGeneratingSet_isKrylovGeneratingSet_max K A f e he _ g hfactor
    (fun i => minimalAnnihilatingPolynomial_primary_factor_isCoprime
      K A f hf hm (e i) (g i) (hfactor i))

end SympyProofs.JordanKrylov
