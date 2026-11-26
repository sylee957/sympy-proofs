module

public import SympyProofs.Calculus.Antiderivative.Proof.TowerConstants
public import SympyProofs.Calculus.Antiderivative.Proof.Answer
public import SympyProofs.Calculus.Antiderivative.Proof.Coefficients
import SympyProofs.Calculus.Antiderivative.Extension.LogDeriv

/-! An inadmissible affine generator creates a new constant that persists in every extension. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Tower

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

private theorem X_pow_ne_C {F : Type} [Field F] (m : ℕ) (hm : 0 < m) (x : F) :
    (RatFunc.X : RatFunc F)^m ≠ RatFunc.C x := by
  intro h
  apply (RatFunc.transcendental_X (K := F)).pow hm
  rw [h, ← RatFunc.algebraMap_eq_C]
  exact isAlgebraic_algebraMap x

private theorem gen_admissible_of_constants (t : Tower R n) (g : ReducedGen (K R n))
    (ht : (t.step g).Admissible k) : g.Admissible k t := by
  let e := Model.stepEquiv k n
  let D := Model.extendVariable (t.modelD k) (t.modelVelocity k g)
  have scalar (x : RatFunc (M k n)) (hx : D x = 0) : ∃ b : M k n, x = RatFunc.C b := by
    have hd : (t.step g).modelD k (e.symm x) = 0 := by
      apply e.injective
      rw [map_zero, show e ((t.step g).modelD k (e.symm x)) = _ from t.stepEquiv_modelD k g _,
        RingEquiv.apply_symm_apply]
      exact hx
    obtain ⟨a,ha⟩ := (ht (e.symm x)).mp hd
    exact ⟨Model.C k n a,(e.symm_apply_eq.mp ha).trans (Model.stepEquiv_scalar k a)⟩
  cases g with
  | prim b =>
    rintro ⟨y,hy⟩
    have hx : D RatFunc.X = RatFunc.C (val k b) := by simp [D, modelVelocity]
    obtain ⟨a,ha⟩ := scalar (RatFunc.X - RatFunc.C y)
      (by rw [map_sub, hx, show D (RatFunc.C y) = _ from Model.extendVariable_C .., hy, sub_self])
    apply X_pow_ne_C 1 Nat.one_pos (a + y)
    simpa only [pow_one, map_add] using (sub_eq_iff_eq_add.mp ha)
  | exp u =>
    rintro ⟨m,y,hm,hy,he⟩
    let a := val k (t.D u)
    have xn := RatFunc.X_ne_zero (K := M k n)
    have yn : RatFunc.C y ≠ 0 := (map_ne_zero_iff _ RatFunc.C_injective).mpr hy
    have hx : D RatFunc.X = RatFunc.C a * RatFunc.X := by simp [D, modelVelocity, a]
    let z := (RatFunc.X : RatFunc (M k n))^m / RatFunc.C y
    have hz : z ≠ 0 := div_ne_zero (pow_ne_zero _ xn) yn
    have log : D z / z = 0 := by
      dsimp only [z]
      rw [Extension.logDeriv_div (pow_ne_zero _ xn) yn, Extension.logDeriv_pow xn, hx,
        mul_div_cancel_right₀ _ xn, show D (RatFunc.C y) = _ from Model.extendVariable_C ..,
        ← map_div₀, he, map_mul, map_natCast, sub_self]
    obtain ⟨c,hc⟩ := scalar z ((div_eq_zero_iff.mp log).resolve_right hz)
    apply X_pow_ne_C m hm (c*y)
    rw [map_mul]
    exact (div_eq_iff yn).mp hc

variable [CharZero k]

/-- A tower step preserves constants precisely when its base and its generator are admissible. -/
theorem admissible_step_iff (t : Tower R n) (g : ReducedGen (K R n)) :
    (t.step g).Admissible k ↔ t.Admissible k ∧ g.Admissible k t := by
  constructor
  · intro h
    refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, gen_admissible_of_constants k t g h⟩
    · let up := Model.includeVars (R := k) (Nat.le_succ n)
      obtain ⟨a, ha⟩ := (h (up x)).mp (by rw [modelD_includeVars, hx, map_zero])
      exact ⟨a, up.injective (ha.trans (Model.includeVars_C k (Nat.le_succ n) a).symm)⟩
    · rintro ⟨c, rfl⟩
      exact t.modelD_C k c
  · rintro ⟨ht, hg⟩
    exact t.admissible_step k g ht hg

end SympyProofs.Calculus.Antiderivative.Tower
