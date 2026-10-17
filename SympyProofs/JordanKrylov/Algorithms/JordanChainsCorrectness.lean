import SympyProofs.JordanKrylov.Algorithms.JordanChainsLemmas
import SympyProofs.JordanKrylov.Algorithms.JordanKrylovBasisInvariant
import SympyProofs.JordanKrylov.Mathematics.BasisChainDecomposition

/-! # Correctness of Algorithm 5

Evaluation at a root gives Jordan chains. Taken over all roots, the output
spans the complexification of the input primary power kernel.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- Evaluate a symbolic chain at one eigenvalue, preserving its order. -/
noncomputable def evaluateJordanChain (K : Subfield ℂ) {n : ℕ}
    (c : List (Fin n → K[X])) (α : ℂ) : Fin c.length → (Fin n → ℂ) :=
  fun j i => (c.get j i).eval₂ K.subtype α

theorem pChainAt_eq_eval_coordinates (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓ k : ℕ) (α : ℂ) (b : Fin n → K) :
    pChainAt K A f ℓ k α b = fun i => (pChainCoordinates K A f ℓ k b i).eval₂ K.subtype α := by
  funext i
  exact PolynomialModule.eval_ofCoordinates ℂ (pChainCoordinates K A f ℓ k b) α i

/-- Every returned symbolic chain is a Jordan chain at every root of f. -/
theorem computeJordanChains_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ)
    (hops : Operations.IsCorrect K)
    (hf : Irreducible f)
    (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) ({v | ∃ ℓ, v ∈ B ℓ}))
    (hranks : ∀ ℓ b, b ∈ B ℓ → 1 ≤ ℓ ∧ vectorRank K A f b = ℓ)
    (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    ∀ c ∈ computeJordanChains K A f B ℓbar,
      IsJordanChain (A.map K.subtype).mulVecLin α (evaluateJordanChain K c α) := by
  intro c hc
  obtain ⟨ℓ, hp, _, b, hb, rfl⟩ := (mem_computeJordanChains_iff K hops A f B ℓbar c).mp hc
  have hr := (hranks ℓ b hb).2
  have hk := hB.1.subset K A _ _ (show b ∈ {v | ∃ ℓ, v ∈ B ℓ} from ⟨ℓ, hb⟩)
  have hn : b ≠ 0 := by
    intro hz
    rw [hz, vectorRank_zero] at hr
    omega
  have h := pChainAt_isJordanChain K A f hf b hn hk hr α hα
  obtain ⟨hpos, hnz, hstep⟩ := h
  refine ⟨by simpa using hpos, ?_, ?_⟩
  · intro j
    unfold evaluateJordanChain
    simpa [evaluateJordanChain, pChainAt_eq_eval_coordinates] using
      hnz ⟨j.val, by simpa using j.isLt⟩
  · intro j
    unfold evaluateJordanChain
    have hj := hstep ⟨j.val, by simpa using j.isLt⟩
    simpa [evaluateJordanChain, pChainAt_eq_eval_coordinates] using hj

/-- The subspace spanned by an evaluated output chain. -/
noncomputable def evaluatedChainSpace (K : Subfield ℂ) {n : ℕ}
    (c : List (Fin n → K[X])) (α : ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (Set.range (evaluateJordanChain K c α))

theorem evaluatedChainSpace_ofFn (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (b : Fin n → K) (α : ℂ) :
    evaluatedChainSpace K
      (List.ofFn (fun j : Fin ℓ => pChainCoordinates K A f ℓ (ℓ - j.val) b)) α =
      chainSpace K A f b ℓ α := by
  unfold evaluatedChainSpace evaluateJordanChain chainSpace
  congr 1
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨⟨j.val, by simpa using j.isLt⟩, ?_⟩
    simp [pChainAt_eq_eval_coordinates]
  · rintro ⟨j, rfl⟩
    refine ⟨⟨j.val, by simp⟩, ?_⟩
    simp [pChainAt_eq_eval_coordinates]

/-- A positive rank label in a bounded primary kernel cannot exceed its exponent. -/
theorem basisLayer_rank_le
    (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (B : ℕ → List (Fin n → K))
    (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) ({v | ∃ ℓ, v ∈ B ℓ}))
    (hranks : ∀ ℓ b, b ∈ B ℓ → 1 ≤ ℓ ∧ vectorRank K A f b = ℓ) (b : Fin n → K) (hb : b ∈ B ℓ) :
    ℓ ≤ ℓbar := by
  have hr := hranks ℓ b hb
  have hk := hB.1.subset K A _ _ (show b ∈ {v | ∃ ℓ, v ∈ B ℓ} from ⟨ℓ, hb⟩)
  have hn : b ≠ 0 := by
    intro hz
    rw [hz, vectorRank_zero] at hr
    omega
  have h := (vectorRank_bounds K A f b hn hk).2
  omega

/-- The output spans exactly the same chain spaces as the input generators. -/
theorem computeJordanChains_chainSpan
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ)
    (hops : Operations.IsCorrect K)
    (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) ({v | ∃ ℓ, v ∈ B ℓ}))
    (hranks : ∀ ℓ b, b ∈ B ℓ → 1 ≤ ℓ ∧ vectorRank K A f b = ℓ) (α : ℂ) :
    (⨆ c ∈ computeJordanChains K A f B ℓbar, evaluatedChainSpace K c α) =
      ⨆ b : {v | ∃ ℓ, v ∈ B ℓ}, chainSpace K A f b.val (vectorRank K A f b.val) α := by
  apply le_antisymm
  · refine iSup_le fun c => iSup_le fun hc => ?_
    obtain ⟨ℓ, _, _, b, hb, rfl⟩ := (mem_computeJordanChains_iff K hops A f B ℓbar c).mp hc
    rw [evaluatedChainSpace_ofFn, ← (hranks ℓ b hb).2]
    exact le_iSup (fun b : {v | ∃ ℓ, v ∈ B ℓ} => chainSpace K A f b.val (vectorRank K A f b.val) α)
      ⟨b, ℓ, hb⟩
  · refine iSup_le fun b => ?_
    obtain ⟨ℓ, hb⟩ := b.property
    have hr := hranks ℓ b.val hb
    let c := List.ofFn (fun j : Fin ℓ => pChainCoordinates K A f ℓ (ℓ-j.val) b.val)
    have hc : c ∈ computeJordanChains K A f B ℓbar :=
      (mem_computeJordanChains_iff K hops A f B ℓbar c).mpr
        ⟨ℓ, hr.1, basisLayer_rank_le K A f B hB hranks b.val hb, b.val, hb, rfl⟩
    rw [hr.2]
    have he := evaluatedChainSpace_ofFn K A f b.val α (ℓ := ℓ)
    exact he ▸ le_iSup_of_le c (le_iSup_of_le hc le_rfl)

/-- Distinct output chains have independent spans at each eigenvalue. -/
theorem computeJordanChains_independent
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ)
    (hops : Operations.IsCorrect K)
    (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) ({v | ∃ ℓ, v ∈ B ℓ}))
    (hranks : ∀ ℓ b, b ∈ B ℓ → 1 ≤ ℓ ∧ vectorRank K A f b = ℓ) (α : ℂ) :
    iSupIndep (fun c : ↥(computeJordanChains K A f B ℓbar) => evaluatedChainSpace K c.val α) := by
  classical
  have hex (c : ↥(computeJordanChains K A f B ℓbar)) :=
    (mem_computeJordanChains_iff K hops A f B ℓbar c.val).mp c.property
  choose ℓ hp hl b hb he using hex
  let g : ↥(computeJordanChains K A f B ℓbar) → {v | ∃ ℓ, v ∈ B ℓ} :=
    fun c => ⟨b c, ℓ c, hb c⟩
  have hg : Function.Injective g := by
    intro c d h
    have hbd : b c = b d := congrArg Subtype.val h
    have hℓ : ℓ c = ℓ d := by
      rw [← (hranks _ _ (hb c)).2, ← (hranks _ _ (hb d)).2, hbd]
    apply Subtype.ext
    rw [← he c, ← he d]
    simp only [hℓ, hbd, Fin.val_cast]
  have hind := (chainSpaces_independent_of_jordanKrylovIndependent K A f
    ({v | ∃ ℓ, v ∈ B ℓ}) hB.2 α).comp hg
  have hs : (fun c : ↥(computeJordanChains K A f B ℓbar) => evaluatedChainSpace K c.val α) =
      (fun b : {v | ∃ ℓ, v ∈ B ℓ} => chainSpace K A f b.val (vectorRank K A f b.val) α) ∘ g := by
    funext c
    change evaluatedChainSpace K c.val α = chainSpace K A f (b c) (vectorRank K A f (b c)) α
    rw [← he c, evaluatedChainSpace_ofFn, (hranks _ _ (hb c)).2]
  rw [hs]
  exact hind

/-- Across all roots, Algorithm 5 spans the complete complexified primary kernel. -/
theorem computeJordanChains_span
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ)
    (hops : Operations.IsCorrect K)
    (hf : Irreducible f) (hm : f.Monic)
    (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) ({v | ∃ ℓ, v ∈ B ℓ}))
    (hranks : ∀ ℓ b, b ∈ B ℓ → 1 ≤ ℓ ∧ vectorRank K A f b = ℓ)
    (α : Fin f.natDegree → ℂ) (hinj : Function.Injective α)
    (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    (⨆ i, ⨆ c ∈ computeJordanChains K A f B ℓbar, evaluatedChainSpace K c (α i)) =
      complexSpan K (powerKernel K A f ℓbar) := by
  simp_rw [computeJordanChains_chainSpan K A f B ℓbar hops hB hranks]
  rw [iSup_comm]
  exact iSup_rootChainSpan_eq_complexSpan_powerKernel K A f hf hm
    ({v | ∃ ℓ, v ∈ B ℓ}) hB α hinj hroot

end SympyProofs.JordanKrylov
