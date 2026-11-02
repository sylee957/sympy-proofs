module

public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness

/-! Specialization of a normal form whose two shift-coprime factors are fixed. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

/-- Scaling the normalization polynomial by a nonzero coefficient preserves its ratio. -/
theorem normalFormValid_scale_C {F : Type} [Field F]
    (P Q A B C : F[X]) (d : F) (hd : d ≠ 0)
    (hvalid : normalFormValid P Q (A, B, C)) :
    normalFormValid P Q (A, B, Polynomial.C d * C) := by
  refine ⟨⟨hvalid.1.1, hvalid.1.2.1,
    mul_ne_zero (Polynomial.C_ne_zero.mpr hd) hvalid.1.2.2⟩, hvalid.2.1, ?_⟩
  change P * (B * (Polynomial.C d * C)) =
    Q * (A * taylor 1 (Polynomial.C d * C))
  rw [taylor_mul, taylor_C]
  calc
    _ = Polynomial.C d * (P * (B * C)) := by ring
    _ = Polynomial.C d * (Q * (A * taylor 1 C)) := congrArg (Polynomial.C d * ·) hvalid.2.2
    _ = _ := by ring

private theorem isCoprime_map_of_injective_maps {K F E : Type} [CommRing K] [Field F] [Field E]
    (i : K →+* F) (hi : Function.Injective i) (f : K →+* E) (hf : Function.Injective f)
    (A B : K[X]) (hA : A ≠ 0) (hcop : IsCoprime (A.map i) (B.map i)) :
    IsCoprime (A.map f) (B.map f) := by
  have hr : Polynomial.resultant A B ≠ 0 := by
    intro hz
    have hz' : Polynomial.resultant (A.map i) (B.map i) = 0 := by
      simp only [natDegree_map_eq_of_injective hi, resultant_map_map, hz, map_zero]
    exact ((resultant_eq_zero_iff.mp hz').2) hcop
  by_contra hn
  have hz := resultant_eq_zero_iff.mpr
    ⟨Or.inl ((Polynomial.map_eq_zero_iff hf).not.mpr hA), hn⟩
  rw [natDegree_map_eq_of_injective hf, natDegree_map_eq_of_injective hf,
    resultant_map_map] at hz
  exact hr (hf (by simpa using hz))

variable {K R L E : Type} [CommRing K] [CommRing R] [Field L] [Field E]
  [Algebra K R] [Algebra K L] [Algebra K E]

/-- A fixed pair of normalized factors remains valid under coefficient specialization,
provided the specialized normalization polynomial is nonzero. -/
theorem normalFormValid_specialize (i : R →ₐ[K] L) (hi : Function.Injective i)
    (f : R →ₐ[K] E)
    (hKi : Function.Injective (algebraMap K L))
    (hKf : Function.Injective (algebraMap K E)) (A B : K[X]) (C P Q : R[X])
    (hvalid : normalFormValid (P.map i.toRingHom) (Q.map i.toRingHom)
      (A.map (algebraMap K L), B.map (algebraMap K L), C.map i.toRingHom))
    (hC : C.map f.toRingHom ≠ 0) :
    normalFormValid (P.map f.toRingHom) (Q.map f.toRingHom)
      (A.map (algebraMap K E), B.map (algebraMap K E), C.map f.toRingHom) := by
  have hA : A ≠ 0 := by
    intro h
    simpa [h] using hvalid.1.1
  have hB : B ≠ 0 := by
    intro h
    simpa [h] using hvalid.1.2.1
  refine ⟨⟨(Polynomial.map_eq_zero_iff hKf).not.mpr hA,
    (Polynomial.map_eq_zero_iff hKf).not.mpr hB, hC⟩, ?_, ?_⟩
  · intro j
    have hcop : IsCoprime (A.map (algebraMap K E))
        ((taylor (j : K) B).map (algebraMap K E)) :=
      isCoprime_map_of_injective_maps (algebraMap K L) hKi
        (algebraMap K E) hKf A (taylor (j : K) B) hA (by simpa using hvalid.2.1 j)
    simpa using hcop
  · have hratio : P * (B.map (algebraMap K R) * C) =
        Q * (A.map (algebraMap K R) * taylor 1 C) := by
      apply Polynomial.map_injective i.toRingHom hi
      simpa [Polynomial.map_map] using hvalid.2.2
    simpa [Polynomial.map_map] using congrArg (Polynomial.map f.toRingHom) hratio

/-- Cleared coefficients can be specialized even when the clearing scalar vanishes;
only the resulting normalization polynomial must remain nonzero. -/
theorem normalFormValid_specialize_of_clearDenominators
    (i : R →ₐ[K] L) (hi : Function.Injective i) (f : R →ₐ[K] E)
    (hKi : Function.Injective (algebraMap K L))
    (hKf : Function.Injective (algebraMap K E)) (A B : K[X]) (C₀ : L[X]) (C P Q : R[X]) (d : R) (hd : d ≠ 0)
    (hvalid : normalFormValid (P.map i.toRingHom) (Q.map i.toRingHom)
      (A.map (algebraMap K L), B.map (algebraMap K L), C₀))
    (hclear : C.map i.toRingHom = Polynomial.C (i d) * C₀)
    (hC : C.map f.toRingHom ≠ 0) :
    normalFormValid (P.map f.toRingHom) (Q.map f.toRingHom)
      (A.map (algebraMap K E), B.map (algebraMap K E), C.map f.toRingHom) := by
  have hid : i d ≠ 0 := fun h => hd (hi (by simpa using h))
  apply normalFormValid_specialize i hi f hKi hKf A B C P Q _ hC
  rw [hclear]
  exact normalFormValid_scale_C _ _ _ _ _ (i d) hid hvalid

end Gosper.Algorithm
