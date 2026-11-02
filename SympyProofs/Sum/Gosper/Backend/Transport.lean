module

public import SympyProofs.Sum.Gosper.Backend.Basic
public import SympyProofs.Sum.Gosper.Backend.FieldExtension

/-! Transport every backend primitive through a field isomorphism. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial

variable {K L : Type*} [Field K] [Field L]

/-- Preserve the supplied operations while changing their coefficient-field representation. -/
noncomputable def Backend.transport (backend : Backend K) (e : K ≃+* L) : Backend L where
  factor p :=
    let f := backend.factor (p.map e.symm.toRingHom)
    (e f.1, f.2.map fun z => (z.1.map e.toRingHom, z.2))
  resultant p q :=
    (backend.resultant (p.map (Polynomial.mapRingHom e.symm.toRingHom))
      (q.map (Polynomial.mapRingHom e.symm.toRingHom))).map e.toRingHom
  zeros m n := (backend.zeros m n).map e
  setElement M i j value :=
    (backend.setElement (M.map e.symm) i j (e.symm value)).map e
  getCol M j i := e (backend.getCol (M.map e.symm) j i)
  rref A := (backend.rref (A.map e.symm)).map e.toRingHom

private theorem polynomial_map_inverse (e : K ≃+* L) (p : L[X]) :
    (p.map e.symm.toRingHom).map e.toRingHom = p := by
  ext n
  simp

private theorem polynomial_map_inverse₂ (e : K ≃+* L) (p : L[X][X]) :
    (p.map (Polynomial.mapRingHom e.symm.toRingHom)).map
      (Polynomial.mapRingHom e.toRingHom) = p := by
  ext n j
  simp

private theorem factorization_map (e : K ≃+* L) (p : K[X])
    (f : K × List (K[X] × ℕ)) (hf : IsFactorization p f) :
    IsFactorization (p.map e.toRingHom)
      (e f.1, f.2.map fun z => (z.1.map e.toRingHom, z.2)) where
  coefficient_ne_zero := by simpa using hf.coefficient_ne_zero
  irreducible := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact (hf.irreducible w hw).map (Polynomial.mapEquiv e).toMulEquiv
  positive := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact hf.positive w hw
  reconstruct := by
    have h := congrArg (Polynomial.map e.toRingHom) hf.reconstruct
    simpa [Polynomial.map_list_prod, List.map_map, Function.comp_def] using h

private theorem resultant_map_equiv (e : K ≃+* L) (p q : K[X][X]) :
    (Polynomial.resultant p q).map e.toRingHom =
      Polynomial.resultant (p.map (Polynomial.mapRingHom e.toRingHom))
        (q.map (Polynomial.mapRingHom e.toRingHom)) := by
  symm
  have hi : Function.Injective (Polynomial.mapRingHom e.toRingHom) :=
    Polynomial.map_injective e.toRingHom e.injective
  simpa only [Polynomial.natDegree_map_eq_of_injective hi, Polynomial.coe_mapRingHom] using
    Polynomial.resultant_map_map p q p.natDegree q.natDegree
      (Polynomial.mapRingHom e.toRingHom)

private theorem matrix_kernel_map_equiv {m n : ℕ} (e : K ≃+* L)
    (A : Matrix (Fin m) (Fin n) K) (x : Fin n → L) :
    (A.map e).mulVec x = 0 ↔ A.mulVec (e.symm ∘ x) = 0 := by
  have hi : Function.Injective (fun y : Fin m → L => e.symm ∘ y) := by
    intro y z h
    ext i
    exact e.symm.injective (congrFun h i)
  rw [← hi.eq_iff]
  have hvec : e.symm ∘ (A.map e).mulVec x = A.mulVec (e.symm ∘ x) := by
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hz : e.symm ∘ (0 : Fin m → L) = (0 : Fin m → K) := by
    ext i
    exact e.symm.map_zero
  rw [hvec, hz]

private theorem rref_map_valid_equiv {m n : ℕ} (e : K ≃+* L)
    (A : Matrix (Fin m) (Fin n) K) (r : RrefResult K m n) (hr : r.Valid A) :
    (r.map e.toRingHom).Valid (A.map e) := by
  refine { r.map_valid_self hr e.toRingHom with kernel_iff := ?_ }
  intro x
  exact (matrix_kernel_map_equiv e A x).trans
    ((hr.kernel_iff _).trans (matrix_kernel_map_equiv e r.matrix x).symm)

/-- Transport preserves factorization, resultants, matrix operations, and the full RREF contract. -/
theorem Backend.transport_valid (backend : Backend K) (hbackend : backend.Valid)
    (e : K ≃+* L) : (backend.transport e).Valid where
  factor_valid p hp := by
    have hp' : p.map e.symm.toRingHom ≠ 0 :=
      (Polynomial.map_eq_zero_iff e.symm.injective).not.mpr hp
    simpa only [transport, polynomial_map_inverse] using
      factorization_map e _ _ (hbackend.factor_valid _ hp')
  resultant_eq p q hp hq := by
    have hp' : p.map (Polynomial.mapRingHom e.symm.toRingHom) ≠ 0 :=
      (Polynomial.map_eq_zero_iff (Polynomial.map_injective _ e.symm.injective)).not.mpr hp
    have hq' : q.map (Polynomial.mapRingHom e.symm.toRingHom) ≠ 0 :=
      (Polynomial.map_eq_zero_iff (Polynomial.map_injective _ e.symm.injective)).not.mpr hq
    obtain ⟨c, hc, he⟩ := hbackend.resultant_eq _ _ hp' hq'
    refine ⟨e c, by simpa using hc, ?_⟩
    change (backend.resultant _ _).map e.toRingHom = _
    rw [he, Polynomial.map_mul, map_C, resultant_map_equiv,
      polynomial_map_inverse₂, polynomial_map_inverse₂]
    rfl
  zeros_eq m n := by
    ext i j
    simp [transport, hbackend.zeros_eq]
  setElement_apply M i j value i' j' := by
    change e (backend.setElement (M.map e.symm) i j (e.symm value) i' j') = _
    rw [hbackend.setElement_apply]
    split_ifs <;> simp_all
  getCol_apply M j i := by
    change e (backend.getCol (M.map e.symm) j i) = M i j
    simp [hbackend.getCol_apply]
  rref_valid A := by
    have h := rref_map_valid_equiv e _ _ (hbackend.rref_valid (A.map e.symm))
    have hA : (A.map e.symm).map e = A := by ext i j; simp
    simpa only [transport, hA] using h

end Gosper.Algorithm
