import SympyProofs.JordanKrylov.Algorithms.JordanDecomposition
import SympyProofs.JordanKrylov.Algorithms.MinimalAnnihilatingPolynomialsCorrectness
import SympyProofs.JordanKrylov.Algorithms.GeneralizedEigenspaceCorrectness

namespace SympyProofs.JordanKrylov
open Matrix Polynomial

open scoped Std.WP

/-- The assembled routine supplies the mathematically specified minimal
annihilator to every primary computation, retaining factor order. -/
theorem computeJordanDecomposition_eq
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (preprocess : Bool) :
    computeJordanDecomposition K A preprocess =
      (Operations.factorCharpoly A).map (fun fm =>
        (⟨fm.1, fm.2, computeGeneralizedEigenspace K A fm.1
            (fun i j => if i = j then 1 else 0)
            (fun i => minimalAnnihilatingPolynomial K A (fun j => if i = j then 1 else 0))
            fm.2 preprocess⟩ : SymbolicJordanComponent K n)) := by
  generalize h : computeJordanDecomposition K A preprocess = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ out => out.toList = pref.flatMap (fun fm => List.replicate fm.2 fm.1)
  · fun pref _ out => out = (pref.map (fun fm =>
      (⟨fm.1, fm.2, computeGeneralizedEigenspace K A fm.1
          (fun i j => if i = j then 1 else 0)
          (fun i => minimalAnnihilatingPolynomial K A (fun j => if i = j then 1 else 0))
          fm.2 preprocess⟩ : SymbolicJordanComponent K n))).toArray
  · by
      rename_i pref f m suff hsplit out hout
      exact fun steps _ acc => acc.toList =
        pref.flatMap (fun fm => List.replicate fm.2 fm.1) ++ List.replicate steps.length f
  case vc1 => rfl
  case vc2 => rfl
  case vc3 =>
    rename_i expanded hex out hout
    apply Array.toList_inj.mp
    simpa only [Std.Internal.ForIn.toList_array, factors, Array.toList_map, List.toList_toArray] using congrArg Array.toList hout
  case vc5 =>
    rename_i pref f m suff hsplit out hout
    simpa using hout
  case vc6 =>
    rename_i pref f m suff hsplit out hout acc hacc
    simpa only [List.length_range, List.flatMap_append, List.flatMap_singleton] using hacc
  case vc7 =>
    rename_i pref f m suff hsplit out hout steps j tail hsteps acc hacc
    simp only [expanded, Array.toList_push, hacc, List.length_append, List.length_singleton,
      List.replicate_add, List.replicate_one, List.append_assoc]
  case vc4 =>
    rename_i expanded hex _ pref f m suff hsplit out hout
    have hex' : expanded.toList = (Operations.factorCharpoly A).toList.flatMap
        (fun fm => List.replicate fm.2 fm.1) := by
      simpa only [Std.Internal.ForIn.toList_array, factors] using hex
    have hann : annihilators = Array.ofFn
        (fun i => minimalAnnihilatingPolynomial K A (e i)) := by
      dsimp only [annihilators]
      rw [hops.indeterminate_eq]
      apply computeMinimalAnnihilatingPolynomials_correct K hops A X 0 expanded e
        monic_X irreducible_X
      · intro g hg
        rw [← Array.mem_toList_iff, hex'] at hg
        obtain ⟨⟨q, r⟩, hqr, hrep⟩ := List.mem_flatMap.mp hg
        have hq : g = q := (List.mem_replicate.mp hrep).2
        subst g
        exact ⟨(hops.factorCharpoly_factors A q r (Array.mem_toList_iff.mp hqr)).1,
          (hops.factorCharpoly_factors A q r (Array.mem_toList_iff.mp hqr)).2.1⟩
      · rw [pow_zero, one_mul, hex', ← hops.factorCharpoly_product A]
        exact Matrix.aeval_self_charpoly A
    have hp : p = fun i => minimalAnnihilatingPolynomial K A (e i) := by
      funext i
      simp [p, hann]
    apply Array.toList_inj.mp
    simp only [components, chains, hp, e, hout, Array.toList_push,
      List.map_append, List.map_singleton]


private theorem coordinateVectors_span (K : Type*) [Field K] (n : ℕ) :
    Submodule.span K (Set.range (fun i : Fin n => fun j : Fin n =>
      if i = j then (1 : K) else 0)) = ⊤ := by
  have he : (fun i : Fin n => fun j : Fin n => if i = j then (1 : K) else 0) =
      (Pi.basisFun K (Fin n) : Fin n → (Fin n → K)) := by
    funext i j
    simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [he]
  exact (Pi.basisFun K (Fin n)).span_eq

/-- The output contains exactly one component per factor, in backend order. -/
theorem computeJordanDecomposition_factors
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (preprocess : Bool) :
    (computeJordanDecomposition K A preprocess).map (fun c => (c.factor, c.multiplicity)) =
      Operations.factorCharpoly A := by
  rw [computeJordanDecomposition_eq K hops]
  simp [Array.map_map, Function.comp_def]

/-- Every symbolic output chain evaluates to a genuine Jordan chain at each
root of its factor. -/
theorem computeJordanDecomposition_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (preprocess : Bool)
    (component : SymbolicJordanComponent K n)
    (hc : component ∈ computeJordanDecomposition K A preprocess)
    (α : ℂ) (hα : component.factor.eval₂ K.subtype α = 0) :
    ∀ c ∈ component.chains,
      IsJordanChain (A.map K.subtype).mulVecLin α (evaluateJordanChain K c α) := by
  rw [computeJordanDecomposition_eq K hops] at hc
  obtain ⟨⟨f, m⟩, hfm, rfl⟩ := Array.mem_map.mp hc
  have hf := hops.factorCharpoly_factors A f m hfm
  exact computeGeneralizedEigenspace_correct K A f _ _ m preprocess
    (coordinateVectors_span K n) hf.2.1 hf.1 (fun _ => rfl)
    (hops.factorCharpoly_multiplicity A f m hfm) hops α hα

/-- Each component is complete: evaluating its chains at all distinct roots
spans its entire complexified primary kernel. -/
theorem computeJordanDecomposition_component_span
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (preprocess : Bool)
    (component : SymbolicJordanComponent K n)
    (hc : component ∈ computeJordanDecomposition K A preprocess)
    (α : Fin component.factor.natDegree → ℂ) (hinj : Function.Injective α)
    (hroot : ∀ i, component.factor.eval₂ K.subtype (α i) = 0) :
    (⨆ i, ⨆ c ∈ component.chains, evaluatedChainSpace K c (α i)) =
      complexSpan K (powerKernel K A component.factor
        (multiplicity component.factor (minpoly K A))) := by
  rw [computeJordanDecomposition_eq K hops] at hc
  obtain ⟨⟨f, m⟩, hfm, rfl⟩ := Array.mem_map.mp hc
  have hf := hops.factorCharpoly_factors A f m hfm
  exact computeGeneralizedEigenspace_span K A f _ _ m preprocess
    (coordinateVectors_span K n) hf.2.1 hf.1 (fun _ => rfl)
    (hops.factorCharpoly_multiplicity A f m hfm) hops α hinj hroot

/-- Distinct chains of one component have independent spans at each root. -/
theorem computeJordanDecomposition_component_independent
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (preprocess : Bool)
    (component : SymbolicJordanComponent K n)
    (hc : component ∈ computeJordanDecomposition K A preprocess) (α : ℂ) :
    iSupIndep (fun c : ↥component.chains => evaluatedChainSpace K c.val α) := by
  rw [computeJordanDecomposition_eq K hops] at hc
  obtain ⟨⟨f, m⟩, hfm, rfl⟩ := Array.mem_map.mp hc
  have hf := hops.factorCharpoly_factors A f m hfm
  exact computeGeneralizedEigenspace_independent K A f _ _ m preprocess
    (coordinateVectors_span K n) hf.2.1 hf.1 (fun _ => rfl)
    (hops.factorCharpoly_multiplicity A f m hfm) hops α

end SympyProofs.JordanKrylov
