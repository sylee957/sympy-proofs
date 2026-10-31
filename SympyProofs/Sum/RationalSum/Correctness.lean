module

public import SympyProofs.Sum.RationalSum.ModelCorrectness
public import SympyProofs.Sum.RationalSum.Refinement
public import SympyProofs.Sum.ShiftlessDecomposition.Correctness

/-! End-to-end correctness of `reduce ops P D`, including decomposition of `D`. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial

variable (ops : ShiftlessDecomposition.Primitives ℚ) (hops : ops.Valid)
    {D : Polynomial ℚ} (hD : D ≠ 0)

include hops hD

/-- The complete computation commutes with every ℚ-algebra homomorphism.
No injectivity or preservation of numerator degree is required. -/
theorem reduce_map {R S : Type*} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (P : Polynomial R) :
    reduce ops (P.map f.toRingHom) D = (reduce ops P D).map f := by
  simpa only [reduce_eq_model] using
    model_prepare_map f (ShiftlessDecomposition.decompose_sound ops hops D hD) P

/-- Numerator coefficients may be arbitrary functions on any parameter space. -/
theorem reduce_apply {Θ R : Type*} [CommRing R] [Algebra ℚ R]
    (P : Polynomial (Θ → R)) (θ : Θ) :
    reduce ops (P.map (Pi.evalRingHom (fun _ : Θ => R) θ)) D =
      (reduce ops P D).map (Pi.evalAlgHom ℚ (fun _ : Θ => R) θ) :=
  reduce_map ops hops hD (Pi.evalAlgHom ℚ (fun _ : Θ => R) θ) P

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The full output satisfies `P/D = ΔG + residual`. -/
theorem reduce_sound (P : Polynomial K) : (reduce ops P D).Sound P D := by
  classical
  rw [reduce_eq_model]
  exact model_sound (ShiftlessDecomposition.decompose_sound ops hops D hD) P

theorem reduce_specialize_sound {R : Type*} [CommRing R] [Algebra ℚ R]
    (f : R →ₐ[ℚ] K) (P : Polynomial R) :
    ((reduce ops P D).map f).Sound (P.map f.toRingHom) D := by
  rw [← reduce_map ops hops hD f]
  exact reduce_sound ops hops hD _

theorem reduce_apply_sound {Θ : Type*}
    (P : Polynomial (Θ → K)) (θ : Θ) :
    ((reduce ops P D).map (Pi.evalAlgHom ℚ (fun _ : Θ => K) θ)).Sound
      (P.map (Pi.evalRingHom (fun _ : Θ => K) θ)) D :=
  reduce_specialize_sound ops hops hD (Pi.evalAlgHom ℚ (fun _ : Θ => K) θ) P

/-- Vanishing residual numerators certify a rational antidifference. -/
theorem reduce_summable_of_residualVanishes (P : Polynomial K)
    (hz : (reduce ops P D).residualVanishes) :
    ∃ G : RatFunc K,
      Gosper.rationalShift 1 G - G = (P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K) := by
  classical
  rw [reduce_eq_model] at hz
  exact model_summable_of_residualVanishes
    (ShiftlessDecomposition.decompose_sound ops hops D hD) P hz

/-- Any rational antidifference forces all computed residual numerators to vanish. -/
theorem reduce_residualVanishes_of_summable (P : Polynomial K)
    (h : ∃ G : RatFunc K,
      Gosper.rationalShift 1 G - G = (P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K)) :
    (reduce ops P D).residualVanishes := by
  classical
  rw [reduce_eq_model]
  exact model_residualVanishes_of_summable
    (ShiftlessDecomposition.decompose_sound ops hops D hD) P h

/-- Necessary and sufficient criterion for rational summability of `P/D`. -/
theorem reduce_summable_iff (P : Polynomial K) :
    (∃ G : RatFunc K,
      Gosper.rationalShift 1 G - G = (P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K)) ↔
      (reduce ops P D).residualVanishes :=
  ⟨reduce_residualVanishes_of_summable ops hops hD P,
    reduce_summable_of_residualVanishes ops hops hD P⟩

/-- The specialized residual equations characterize summability at every parameter value. -/
theorem reduce_specialize_summable_iff
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (f : R →ₐ[ℚ] K) (P : Polynomial R) :
    (∃ G : RatFunc K, Gosper.rationalShift 1 G - G =
      (P.map f.toRingHom : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K)) ↔
      ((reduce ops P D).map f).residualVanishes := by
  rw [← reduce_map ops hops hD f]
  exact reduce_summable_iff ops hops hD _

theorem reduce_apply_summable_iff {Θ : Type*}
    (P : Polynomial (Θ → K)) (θ : Θ) :
    (∃ G : RatFunc K, Gosper.rationalShift 1 G - G =
      (P.map (Pi.evalRingHom (fun _ : Θ => K) θ) : RatFunc K) /
        (D.map (algebraMap ℚ K) : RatFunc K)) ↔
      ((reduce ops P D).map (Pi.evalAlgHom ℚ (fun _ : Θ => K) θ)).residualVanishes :=
  reduce_specialize_summable_iff ops hops hD (Pi.evalAlgHom ℚ (fun _ : Θ => K) θ) P

/-- Exact finite sums in the rational-function field, with symbolic starting point `X`. -/
theorem reduce_sum_range (P : Polynomial K) (n : ℕ) :
    let r := reduce ops P D
    ∑ k ∈ Finset.range n,
        Gosper.rationalShift (k : K) ((P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K)) =
      r.primitiveAt (n : K) - r.primitiveAt 0 +
        ∑ k ∈ Finset.range n, Gosper.rationalShift (k : K) r.residualPart := by
  classical
  simpa only [reduce_eq_model] using
    model_sum_range (ShiftlessDecomposition.decompose_sound ops hops D hD) P n

/-- Summation after arbitrary algebraic specialization of the numerator. -/
theorem reduce_specialize_sum_range {R : Type*} [CommRing R] [Algebra ℚ R]
    (f : R →ₐ[ℚ] K) (P : Polynomial R) (n : ℕ) :
    let r := (reduce ops P D).map f
    ∑ k ∈ Finset.range n,
        Gosper.rationalShift (k : K)
          ((P.map f.toRingHom : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K)) =
      r.primitiveAt (n : K) - r.primitiveAt 0 +
        ∑ k ∈ Finset.range n, Gosper.rationalShift (k : K) r.residualPart := by
  dsimp only
  rw [← reduce_map ops hops hD f]
  exact reduce_sum_range ops hops hD _ n

/-- Residuals need vanish only at the chosen specialization to evaluate the sum. -/
theorem reduce_specialize_sum_range_of_residualVanishes
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (f : R →ₐ[ℚ] K) (P : Polynomial R) (n : ℕ)
    (hz : ((reduce ops P D).map f).residualVanishes) :
    let r := (reduce ops P D).map f
    ∑ k ∈ Finset.range n,
        Gosper.rationalShift (k : K)
          ((P.map f.toRingHom : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K)) =
      r.primitiveAt (n : K) - r.primitiveAt 0 := by
  simpa only [Result.residualPart_eq_zero hz, map_zero, Finset.sum_const_zero, add_zero]
    using reduce_specialize_sum_range ops hops hD f P n

/-- Evaluation at any parameter value commutes with the finite-sum identity. -/
theorem reduce_apply_sum_range {Θ : Type*}
    (P : Polynomial (Θ → K)) (θ : Θ) (n : ℕ) :
    let r := (reduce ops P D).map (Pi.evalAlgHom ℚ (fun _ : Θ => K) θ)
    ∑ k ∈ Finset.range n,
        Gosper.rationalShift (k : K)
          ((P.map (Pi.evalRingHom (fun _ : Θ => K) θ) : RatFunc K) /
            (D.map (algebraMap ℚ K) : RatFunc K)) =
      r.primitiveAt (n : K) - r.primitiveAt 0 +
        ∑ k ∈ Finset.range n, Gosper.rationalShift (k : K) r.residualPart :=
  reduce_specialize_sum_range ops hops hD (Pi.evalAlgHom ℚ (fun _ : Θ => K) θ) P n

end Gosper.RationalSum
