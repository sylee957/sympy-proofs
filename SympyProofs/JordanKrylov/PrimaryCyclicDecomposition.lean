import Mathlib.Algebra.Module.PID

namespace SympyProofs.JordanKrylov
open scoped BigOperators DirectSum

/-- A finite primary torsion module over a PID admits independent cyclic generators. -/
theorem exists_primary_cyclic_generators {R M : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : R) (hp : Irreducible p) (ht : Module.IsTorsion' M (Submonoid.powers p)) :
    ∃ (d : ℕ) (v : Fin d → M),
      iSupIndep (fun i => Submodule.span R {v i}) ∧
      (⨆ i, Submodule.span R {v i}) = ⊤ := by
  classical
  obtain ⟨d, k, ⟨e₀⟩⟩ := Module.torsion_by_prime_power_decomposition hp ht
  let Q := fun i : Fin d => R ⧸ Ideal.span {p ^ k i}
  let e : M ≃ₗ[R] ∀ i, Q i := e₀.trans (DirectSum.linearEquivFunOnFintype R (Fin d) Q)
  let v : Fin d → M := fun i => e.symm (Pi.single i 1)
  have hmem (i : Fin d) (x : M) (hx : x ∈ Submodule.span R {v i}) :
      ∃ a : R, x = a • v i := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨a, ha.symm⟩
  refine ⟨d, v, ?_, ?_⟩
  · apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
    intro s x hx hsum i hi
    have he := congrArg (fun m => e m i) hsum
    simp only [map_sum, map_zero, Finset.sum_apply, Pi.zero_apply] at he
    have hsingle : (∑ j ∈ s, e (x j) i) = e (x i) i := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        obtain ⟨a, ha⟩ := hmem j (x j) (hx j hj)
        simp [ha, v, Ne.symm hji]
      · exact fun h => False.elim (h hi)
    rw [hsingle] at he
    obtain ⟨a, ha⟩ := hmem i (x i) (hx i hi)
    apply e.injective
    ext j
    by_cases hj : j = i
    · subst j; simpa using he
    · simp [ha, v, hj]
  · apply top_unique
    intro x _
    have hterm (i : Fin d) : e.symm (Pi.single i (e x i)) ∈ Submodule.span R {v i} := by
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e x i)
      apply Submodule.mem_span_singleton.mpr
      refine ⟨a, ?_⟩
      apply e.injective
      simp only [map_smul, v, LinearEquiv.apply_symm_apply]
      ext j
      by_cases hj : j = i
      · subst j; simpa [Q, Algebra.smul_def] using ha
      · simp [hj]
    have heq : x = ∑ i, e.symm (Pi.single i (e x i)) := by
      apply e.injective
      ext j
      simp
    rw [heq]
    exact Submodule.sum_mem _ fun i _ => (le_iSup (fun j => Submodule.span R {v j}) i) (hterm i)

end SympyProofs.JordanKrylov
