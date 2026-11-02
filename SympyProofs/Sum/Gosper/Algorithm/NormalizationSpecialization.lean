module

public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness

/-! Specialization of a normal form whose two shift-coprime factors are fixed. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K R L E : Type} [Field K] [CommRing R] [Field L] [Field E]
  [Algebra K R] [Algebra K L] [Algebra K E]

/-- A fixed pair of normalized factors remains valid under coefficient specialization,
provided the specialized normalization polynomial is nonzero. -/
theorem normalFormValid_specialize (i : R →ₐ[K] L) (hi : Function.Injective i)
    (f : R →ₐ[K] E) (A B : K[X]) (C P Q : R[X])
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
  refine ⟨⟨by simpa using hA, by simpa using hB, hC⟩, ?_, ?_⟩
  · intro j
    have hcop : IsCoprime A (taylor (j : K) B) := by
      apply (Polynomial.isCoprime_map (algebraMap K L)).mp
      simpa using hvalid.2.1 j
    simpa using hcop.map (Polynomial.mapRingHom (algebraMap K E))
  · have hratio : P * (B.map (algebraMap K R) * C) =
        Q * (A.map (algebraMap K R) * taylor 1 C) := by
      apply Polynomial.map_injective i.toRingHom hi
      simpa [Polynomial.map_map] using hvalid.2.2
    simpa [Polynomial.map_map] using congrArg (Polynomial.map f.toRingHom) hratio

end Gosper.Algorithm
