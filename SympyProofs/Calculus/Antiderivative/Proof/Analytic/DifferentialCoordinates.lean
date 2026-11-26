module

public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.OpenSet

/-! Change analytic coordinates through an isomorphism of rational differential fields. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Model

open Filter Topology

variable {n : ℕ} (e : M ℂ n ≃+* M ℂ n) {G H : ℂ → Fin n → ℂ} {V : Set ℂ}

/-- A differential coordinate change carries solutions to solutions whenever its inverse
coordinate expressions have the specified pointwise values on an open set. -/
theorem solvedBy_of_changeCoordinates {v w : List (M ℂ n)} (hV : IsOpen V)
    (hD : ∀ x, e (derivation ℂ v x) = derivation ℂ w (e x))
    (map : ∀ z ∈ V, ∀ {x c}, HasValue (G z) x c → HasValue (H z) (e x) c)
    (coord : ∀ z ∈ V, ∀ i : Fin n,
      HasValue (G z) (e.symm (polynomial ℂ (MvPolynomial.X i))) (H z i))
    (sol : ∀ z ∈ V, SolvedBy v G z) : ∀ z ∈ V, SolvedBy w H z := by
  intro z hz i
  let x := e.symm (polynomial ℂ (MvPolynomial.X i))
  obtain ⟨hr,hd⟩ := hasDerivAt_evalAt (sol z hz)
    (show RegularAt (G z) x from ⟨_,coord z hz i⟩)
  have hv := map z hz hr.hasValue
  rw [hD,show e x = _ from e.apply_symm_apply _,derivation_X] at hv
  refine ⟨⟨_,hv⟩, ?_⟩
  rw [hv.evalAt]
  apply hd.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hz] with a ha
  exact (coord a ha i).evalAt.symm

/-- An identity in the source coordinates transfers to the new coordinates and hence
vanishes formally when the new coordinates are algebraically independent. -/
theorem independentOn_of_changeCoordinates
    (map : ∀ z ∈ V, ∀ {x c}, HasValue (G z) x c → HasValue (H z) (e x) c)
    (indep : IndependentOn H V) : IndependentOn G V := by
  intro p hp
  have he : e (polynomial ℂ p) = 0 := indep.eq_zero fun z hz =>
    map z hz (hp z hz ▸ HasValue.polynomial p)
  have h := e.injective (he.trans (map_zero e).symm)
  exact (IsFractionRing.injective (MvPolynomial (Fin n) ℂ) (M ℂ n)) (h.trans (map_zero _).symm)

end SympyProofs.Calculus.Antiderivative.Model
