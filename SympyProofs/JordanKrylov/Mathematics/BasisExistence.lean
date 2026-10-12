import SympyProofs.JordanKrylov.Mathematics.PrimaryCyclicDecomposition
import SympyProofs.JordanKrylov.Mathematics.RankMultiplicity

/-! # Existence of Jordan–Krylov bases

The power kernel is a finite primary torsion module for the polynomial action
q • u = q(A)u. The PID structure theorem supplies independent cyclic generators.
Their polynomial spans are exactly the Krylov spaces of their underlying vectors.

The positive-rank uniqueness part of Theorem 12 is proved separately in `RankMultiplicity`.
-/

namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped BigOperators DirectSum

private theorem aeval_module_smul (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (q : K[X]) (x : Module.AEval' A.mulVecLin) :
    (Module.AEval'.of A.mulVecLin).symm (q • x) =
      aeval A q *ᵥ (Module.AEval'.of A.mulVecLin).symm x := by
  change (aeval A.mulVecLin q) _ = _
  have h := Polynomial.aeval_algHom_apply Matrix.toLinAlgEquiv' A q
  change aeval A.mulVecLin q = Matrix.toLinAlgEquiv' (aeval A q) at h
  rw [h]
  rfl

/-- A primary power kernel is the independent sum of finitely many cyclic Krylov spaces. -/
theorem exists_independent_krylov_family (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (ℓbar : ℕ) :
    ∃ (d : ℕ) (w : Fin d → (Fin n → K)),
      iSupIndep (fun i => krylovSpace K A (w i)) ∧
      (⨆ i, krylovSpace K A (w i)) = powerKernel K A f ℓbar := by
  classical
  let P := Submodule.torsionBy K[X] (Module.AEval' A.mulVecLin) (f ^ ℓbar)
  let E : P →ₗ[K] (Fin n → K) :=
    (Module.AEval'.of A.mulVecLin).symm.toLinearMap.comp (P.subtype.restrictScalars K)
  have hEinj : Function.Injective E :=
    (Module.AEval'.of A.mulVecLin).symm.injective.comp Subtype.val_injective
  let : Module.Finite K P := Module.Finite.of_injective E hEinj
  let : Module.Finite K[X] P := Module.Finite.of_restrictScalars_finite K K[X] P
  have hEs (q : K[X]) (x : P) : E (q • x) = aeval A q *ᵥ E x :=
    aeval_module_smul K A q x.val
  have hErange : LinearMap.range E = powerKernel K A f ℓbar := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_powerKernel]
      have hx : f ^ ℓbar • x.val = 0 := x.property
      have he := congrArg (Module.AEval'.of A.mulVecLin).symm hx
      rw [aeval_module_smul, map_zero, map_pow] at he
      exact he
    · intro hu
      have hx : Module.AEval'.of A.mulVecLin u ∈ P := by
        change f ^ ℓbar • Module.AEval'.of A.mulVecLin u = 0
        apply (Module.AEval'.of A.mulVecLin).symm.injective
        rw [aeval_module_smul, map_zero, LinearEquiv.symm_apply_apply, map_pow]
        exact (mem_powerKernel K A f ℓbar u).mp hu
      exact ⟨⟨Module.AEval'.of A.mulVecLin u, hx⟩, rfl⟩
  have ht : Module.IsTorsion' P (Submonoid.powers f) := by
    apply (Submodule.isTorsion'_powers_iff f).mpr
    intro x
    exact ⟨ℓbar, Subtype.ext x.property⟩
  obtain ⟨d, v, hind, hspan⟩ := exists_primary_cyclic_generators (M := P) f hf ht
  have hcyc (x : P) : ((Submodule.span K[X] {x}).restrictScalars K).map E =
      krylovSpace K A (E x) := by
    ext u
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.mp hy
      exact (mem_krylovSpace_iff K A (E x) _).mpr ⟨q, (hEs q x).symm⟩
    · intro hu
      obtain ⟨q, hq⟩ := (mem_krylovSpace_iff K A (E x) u).mp hu
      exact ⟨q • x, Submodule.smul_mem _ q (Submodule.mem_span_singleton_self x),
        (hEs q x).trans hq⟩
  refine ⟨d, fun i => E (v i), ?_, ?_⟩
  · simp_rw [← hcyc]
    intro i
    dsimp only
    simp_rw [← Submodule.map_iSup, ← Submodule.restrictScalars_iSup]
    apply Submodule.disjoint_map hEinj
    exact (Submodule.disjoint_restrictScalars_iff K).mpr (hind i)
  · simp_rw [← hcyc, ← Submodule.map_iSup, ← Submodule.restrictScalars_iSup]
    rw [hspan]
    simpa using hErange

/-- The existence part of Theorem 12. -/
theorem exists_jordanKrylovBasis_powerKernel (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (ℓbar : ℕ) :
    ∃ B : Set (Fin n → K), IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B := by
  classical
  obtain ⟨d, w, hind, hspan⟩ := exists_independent_krylov_family K A f hf ℓbar
  let B := Set.range w
  have hg (b : B) : ∃ i, w i = b.val := b.property
  choose g hg using hg
  have hginj : Function.Injective g := by
    intro b c h
    apply Subtype.ext
    rw [← hg b, ← hg c, h]
  refine ⟨B, ?_, Set.finite_range w, ?_⟩
  · change powerKernel K A f ℓbar = ⨆ b ∈ Set.range w, krylovSpace K A b
    simpa only [iSup_range] using hspan.symm
  · have hi := hind.comp hginj
    simpa only [Function.comp_def, hg] using hi

end SympyProofs.JordanKrylov
