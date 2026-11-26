module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Criterion
public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Repeated
public import SympyProofs.Calculus.Antiderivative.Proof.Poles
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Complete

/-! The simple-fraction characterization in the differential model of a tower step. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial Differential
open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]

/-- Exponential generators have a possible special pole at zero. -/
def exponential : ReducedGen (K R n) → Bool
  | .prim _ => false
  | .exp _ => true

/-- Coefficient of the generator in its affine velocity. -/
def slope (t : Tower R n) : ReducedGen (K R n) → K R n
  | .prim _ => 0
  | .exp u => t.D u

/-- Constant term in the generator velocity. -/
private def intercept : ReducedGen (K R n) → K R n
  | .prim b => b
  | .exp _ => 0

local notation "ι" => algebraMap (M k n)[X] (RatFunc (M k n))

/-- Saturation in the model is exactly cancellation of the repeated factors, a constant
polynomial part, rational residues at the computed irreducibles, and the lower relation. -/
theorem model_iff (t : Tower R n) (g : ReducedGen (K R n)) (hg : g.Admissible k t)
    (T : Poly (K R n)) (ht : T ≠ 0) (W N : (K R n)[X]) (c : K R n) :
    let d := poleDerivative (exponential g) T
    let G := gcd T d
    let S := T / G
    N = W / Poly.equiv G → (N / Poly.equiv S).coeff 0 = c →
    (Saturated (Model.extendVariable (t.modelD k) (t.modelVelocity k g))
        (ι (W.map (val k)) / ι (Step.modelPoly (val k) T)) ↔
      (Poly.equiv G ∣ W ∧ N / Poly.equiv S = C c) ∧
        (∀ p ∈ factorTower S, ∃ r : ℚ, Poly.equiv p ∣ N - C (r : K R n) *
          Poly.equiv (Step.polyDer t.D (g.velocity t.D) S)) ∧
        ∃ e : ℚ, t.SaturatedLog k (val k c + (e : M k n) * val k (slope t g))) := by
  intro d G S hN hc
  let j := val (R := R) (n := n) k
  let a := j (slope t g)
  let b := j (intercept g)
  let _ : CharZero (K R n) := j.charZero
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let _ : Differential (RatFunc (M k n)) :=
    ⟨Model.extendVariable (t.modelD k) (t.modelVelocity k g)⟩
  let _ : DifferentialAlgebra (M k n) (RatFunc (M k n)) := ⟨fun _ => Model.extendVariable_C ..⟩
  have vel : t.modelVelocity k g = C a * X + C b := by
    cases g <;> simp [a, b, slope, intercept, Tower.modelVelocity, j]
  have dx : deriv (RatFunc.X : RatFunc (M k n)) = RatFunc.C a * RatFunc.X + RatFunc.C b := by
    rw [show deriv (RatFunc.X : RatFunc (M k n)) = _ from Model.extendVariable_X .., vel]
    simp
  have δ : t.polyDerModel k g = Extension.affine a b := by rw [Tower.polyDerModel, vel]
  have tw : Saturated deriv (RatFunc.C a) := by
    cases g with
    | prim v => simpa [a, j, slope] using saturated_zero (F := RatFunc (M k n)) deriv
    | exp v =>
      have hx := saturated_log deriv (RatFunc.X_ne_zero (K := M k n))
      rw [dx] at hx
      simpa [b, intercept, RatFunc.X_ne_zero (K := M k n)] using hx
  have v1 : j ((g.velocity t.D).coeff 1) = a := by
    have he := congrArg (fun p : (M k n)[X] => p.coeff 1) (t.modelPoly_velocity k g)
    rw [vel] at he
    simpa [j] using he
  have lead (p : (M k n)[X]) (pm : p.Monic) := t.degree_polyDerModel k g pm
  have sq : Squarefree (Poly.equiv S) := by
    cases g with
    | prim v => exact Step.squarefreeParts_spec ht
    | exp v => exact (Step.expNormalDen_spec ht).1
  have sf := ((separable_map j).mpr (PerfectField.separable_iff_squarefree.mpr sq)).squarefree
  have ns (p : (M k n)[X]) (hp : Prime p) (hd : p ∣ (Poly.equiv S).map j) :
      ¬ p ∣ t.polyDerModel k g p := by
    dsimp only [S, G, d] at hd
    cases g with
    | prim v => exact t.prime_normal_prim k v hg hp
    | exp v =>
      apply t.prime_normal_exp k v hg hp
      intro hz
      apply (Step.expNormalDen_spec ht).2
      apply (Polynomial.map_dvd_map' j).mp
      simpa [exponential, poleDerivative] using (X_dvd_iff.mpr hz).trans hd
  have sx : exponential g = true → ∃ v, Extension.affine a b X = v * X := by
    intro he
    cases g with
    | prim v => contradiction
    | exp v => exact ⟨C a, by simp [Extension.affine, b, intercept]⟩
  have s0 : S ≠ 0 := (map_ne_zero_iff _ Poly.equiv.injective).mp sq.ne_zero
  let fs := (factorTower S).map Poly.equiv
  have fsprod : C (Poly.equiv S).leadingCoeff * fs.prod = Poly.equiv S := by
    simpa only [fs, map_mul, Poly.equiv_C, Poly.leadingCoeff_equiv, map_list_prod] using
      congrArg Poly.equiv (factorTower_product S s0)
  have fi : ∀ p ∈ fs, Irreducible p := by
    intro p hp
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hp
    exact (MulEquiv.irreducible_iff (Poly.equiv (R := K R n))).mpr
      (factorTower_irreducible S s0 P hP)
  have crit := saturated_iff j dx tw (by simpa only [δ, v1, j] using lead)
    N (Poly.equiv S) (Poly.equiv (Step.polyDer t.D (g.velocity t.D) S)) fs sq.ne_zero sf
    (by simpa only [δ] using ns)
    (by change Step.modelPoly (val k) _ = _; rw [t.modelPoly_polyDer k g S, δ]; rfl)
    fsprod fi c hc
  simp only [fs, List.forall_mem_map] at crit
  have necessary := repeated_dvd j (exponential g) T W ht (Extension.affine a b) deriv
    (Extension.LiouvilleForm.affineDeriv_map dx) sx
  have cancel (hd : Poly.equiv G ∣ W) :
      ι (W.map j) / ι (Step.modelPoly j T) = ι (N.map j) / ι (Step.modelPoly j S) := by
    rw [hN]
    exact cancel_repeated j T d W ht hd
  constructor
  · intro hs
    have hd := necessary hs
    rw [cancel hd] at hs
    obtain ⟨const, residues, lower⟩ := crit.mp hs
    exact ⟨⟨hd, const⟩, residues, lower⟩
  · rintro ⟨⟨hd, const⟩, residues, lower⟩
    rw [cancel hd]
    exact crit.mpr ⟨const, residues, lower⟩

end SympyProofs.Calculus.Antiderivative.Logarithmic
