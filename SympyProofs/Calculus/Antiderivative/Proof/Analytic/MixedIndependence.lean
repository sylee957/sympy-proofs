module

public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.MixedPoint
public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.Independence
public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.DifferentialCoordinates
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.ConstantModel

/-! Admissible mixed primitive, exponential and tangent solutions are algebraically
independent on a nonempty open set when their coordinates avoid stationary special values. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R ℂ] [FaithfulSMul R ℂ] {n : ℕ}

/-- A nondegenerate native complex solution to an admissible mixed tower satisfies no
polynomial identity on any nonempty open set. -/
theorem Tower.independent_of_solution (t : Tower R n) (ht : t.Admissible ℂ)
    {G : ℂ → Fin n → ℂ} {V : Set ℂ} (hV : IsOpen V) (hn : V.Nonempty)
    (sol : ∀ z ∈ V, t.SolvedBy G z) (nz : ∀ z ∈ V, t.Nondegenerate (G z)) :
    Model.IndependentOn G V := by
  classical
  let c : K R 0 →+* K ℂ 0 := (K.CRingHom 0).comp (Model.constantHom ℂ)
  let i : K ℂ 0 := K.C Complex.I
  have hc (a : K R 0) : Model.constantHom ℂ (c a) = Model.constantHom ℂ a :=
    modelConstant_C ℂ (Model.constantHom ℂ a)
  have hi : i^2 = -1 := by
    change (K.CRingHom 0 Complex.I)^2 = -1
    rw [← map_pow,Complex.I_sq,map_neg,map_one]
  have hv : Model.constantHom ℂ i = Complex.I := modelConstant_C ℂ Complex.I
  let e := t.changeModel ℂ Complex.I Complex.I_ne_zero
  let u := (t.compile c i).tower
  let H := fun z => Points.point t (G z)
  have D (x : M ℂ n) : e (t.modelD ℂ x) = u.modelD ℂ (e x) := by
    have hd := t.changeModel_D ℂ c hc i hi x
    simpa only [hv] using hd
  have hu : u.Admissible ℂ := (t.compile_admissible_iff ℂ c hc i hi).mpr ht
  have map (z) (hz : z ∈ V) {x b} (h : Model.HasValue (G z) x b) :
      Model.HasValue (H z) (e x) b := Points.change_value t _ (nz z hz) h
  apply Model.independentOn_of_changeCoordinates e map
  apply u.independent_of_solution_reduced (t.compile c i).tangentFree hu hV hn
  · exact Model.solvedBy_of_changeCoordinates e hV D map (fun z hz => Points.inverse_value t _
      (nz z hz)) sol
  · exact fun z hz => Points.nondegenerate c i t _ (nz z hz)

end SympyProofs.Calculus.Antiderivative
