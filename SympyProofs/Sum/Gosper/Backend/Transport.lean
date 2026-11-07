module

public import SympyProofs.Sum.Gosper.Backend.Descent
public import SympyProofs.Sum.Gosper.Backend.FieldExtension

/-! Transport input-ring operations through an algebra isomorphism. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial

variable {K R S : Type*} [CommRing K] [IsDomain K]
variable [Field R] [Field S] [Algebra K R] [Algebra K S]

/-- Change the input-field representation, preserving the constant-domain solver. -/
noncomputable def TermBackend.transport (backend : TermBackend K R) (e : R ≃ₐ[K] S) :
    TermBackend K S where
  gcd p q := (backend.gcd (p.map e.symm.toRingHom) (q.map e.symm.toRingHom)).map e.toRingHom
  exactDiv p q := (backend.exactDiv (p.map e.symm.toRingHom)
    (q.map e.symm.toRingHom)).map e.toRingHom
  resultant p q :=
    (backend.resultant (p.map (Polynomial.mapRingHom e.symm.toRingHom))
      (q.map (Polynomial.mapRingHom e.symm.toRingHom))).map e.toRingHom
  naturalRoots p := backend.naturalRoots (p.map e.symm.toRingHom)
  integerRatio := backend.integerRatio
  descend c := backend.descend (e.symm c)

omit [IsDomain K] in
private theorem alg_polynomial_map_inverse (e : R ≃ₐ[K] S) (p : S[X]) :
    (p.map e.symm.toRingHom).map e.toRingHom = p := by
  ext n
  simp

omit [IsDomain K] in
private theorem alg_polynomial_map_inverse₂ (e : R ≃ₐ[K] S) (p : S[X][X]) :
    (p.map (Polynomial.mapRingHom e.symm.toRingHom)).map
      (Polynomial.mapRingHom e.toRingHom) = p := by
  ext n j
  simp

private theorem resultant_map_equiv (e : R ≃+* S) (p q : R[X][X]) :
    (Polynomial.resultant p q).map e.toRingHom =
      Polynomial.resultant (p.map (Polynomial.mapRingHom e.toRingHom))
        (q.map (Polynomial.mapRingHom e.toRingHom)) := by
  symm
  have hi : Function.Injective (Polynomial.mapRingHom e.toRingHom) :=
    Polynomial.map_injective e.toRingHom e.injective
  simpa only [Polynomial.natDegree_map_eq_of_injective hi, Polynomial.coe_mapRingHom] using
    Polynomial.resultant_map_map p q p.natDegree q.natDegree
      (Polynomial.mapRingHom e.toRingHom)

private theorem transport_gcd_greatest (backend : TermBackend K R)
    (hbackend : backend.Valid) (e : R ≃ₐ[K] S) (p q d : S[X])
    (hp : d ∣ p) (hq : d ∣ q) : d ∣ (backend.transport e).gcd p q := by
  have hd := hbackend.gcd_greatest _ _ _
    ((Polynomial.mapRingHom e.symm.toRingHom).map_dvd hp)
    ((Polynomial.mapRingHom e.symm.toRingHom).map_dvd hq)
  have hm := (Polynomial.mapRingHom e.toRingHom).map_dvd hd
  change (d.map e.symm.toRingHom).map e.toRingHom ∣ _ at hm
  rw [alg_polynomial_map_inverse e] at hm
  exact hm

/-- Transporting the input field preserves every backend contract. -/
theorem TermBackend.transport_valid (backend : TermBackend K R) (hbackend : backend.Valid)
    (e : R ≃ₐ[K] S) : (backend.transport e).Valid where
  gcd_dvd_left p q := by
    have hm := (Polynomial.mapRingHom e.toRingHom).map_dvd
      (hbackend.gcd_dvd_left (p.map e.symm.toRingHom) (q.map e.symm.toRingHom))
    change _ ∣ (p.map e.symm.toRingHom).map e.toRingHom at hm
    rw [alg_polynomial_map_inverse e] at hm
    exact hm
  gcd_dvd_right p q := by
    have hm := (Polynomial.mapRingHom e.toRingHom).map_dvd
      (hbackend.gcd_dvd_right (p.map e.symm.toRingHom) (q.map e.symm.toRingHom))
    change _ ∣ (q.map e.symm.toRingHom).map e.toRingHom at hm
    rw [alg_polynomial_map_inverse e] at hm
    exact hm
  gcd_greatest p q d hp hq := transport_gcd_greatest backend hbackend e p q d hp hq
  exactDiv_mul p d hd hdp := by
    have hd' : d.map e.symm.toRingHom ≠ 0 :=
      (Polynomial.map_ne_zero_iff e.symm.injective).mpr hd
    have he := hbackend.exactDiv_mul (p.map e.symm.toRingHom) (d.map e.symm.toRingHom)
      hd' ((Polynomial.mapRingHom e.symm.toRingHom).map_dvd hdp)
    have hm := congrArg (Polynomial.map e.toRingHom) he
    rw [Polynomial.map_mul, alg_polynomial_map_inverse e, alg_polynomial_map_inverse e] at hm
    exact hm
  resultant_eq p q hp hq := by
    have hp' : p.map (Polynomial.mapRingHom e.symm.toRingHom) ≠ 0 :=
      (Polynomial.map_eq_zero_iff (Polynomial.map_injective _ e.symm.injective)).not.mpr hp
    have hq' : q.map (Polynomial.mapRingHom e.symm.toRingHom) ≠ 0 :=
      (Polynomial.map_eq_zero_iff (Polynomial.map_injective _ e.symm.injective)).not.mpr hq
    obtain ⟨c, hc, he⟩ := hbackend.resultant_eq _ _ hp' hq'
    refine ⟨e c, by simpa using hc, ?_⟩
    change (backend.resultant _ _).map e.toRingHom = _
    rw [he, Polynomial.map_mul, map_C, resultant_map_equiv e.toRingEquiv]
    rw [alg_polynomial_map_inverse₂ e, alg_polynomial_map_inverse₂ e]
    rfl
  mem_naturalRoots p hp j := by
    have hp' : p.map e.symm.toRingHom ≠ 0 :=
      (Polynomial.map_ne_zero_iff e.symm.injective).mpr hp
    rw [show j ∈ (backend.transport e).naturalRoots p ↔
      j ∈ backend.naturalRoots (p.map e.symm.toRingHom) from Iff.rfl,
      hbackend.mem_naturalRoots _ hp' j]
    have he : (p.map e.symm.toRingHom).eval (j : R) = e.symm (p.eval (j : S)) := by
      simp
    rw [he]
    exact (map_eq_zero_iff e.symm.toRingHom e.symm.injective)
  integerRatio_eq_some := hbackend.integerRatio_eq_some
  descend c a := by
    change backend.descend (e.symm c) = some a ↔ algebraMap K S a = c
    rw [hbackend.descend]
    constructor
    · intro h
      apply e.symm.injective
      simpa using h
    · intro h
      simpa using congrArg e.symm h

end Gosper.Algorithm
