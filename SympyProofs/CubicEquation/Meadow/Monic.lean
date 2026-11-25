module

public import SympyProofs.CubicEquation.Meadow.Formula

/-! # Monic Cardano roots with two total divisions -/

@[expose] public section

noncomputable section
namespace CubicEquation.CardanoComplex

/-- At a nonzero first radicand h, p³/(27h) − q equals h. At h = 0 it equals −q. -/
def quotientU (p q : ℂ) : ℂ :=
  RealCubeRoot.principal (p ^ 3 / (27 * radicandPlus p q) - q)

theorem quotientU_eq (p q : ℂ) : quotientU p q = meadowU p q := by
  unfold quotientU meadowU
  congr 1
  let h := radicandPlus p q
  change p ^ 3 / (27 * h) - q = h - (1 - h * h⁻¹) * q
  by_cases hz : h = 0
  · simp [hz]
  · have hp : h * (h + q) = p ^ 3 / 27 := by
      dsimp [h, radicandPlus, discriminant]
      linear_combination (sqrt_sq (q ^ 2 / 4 + p ^ 3 / 27))
    rw [mul_inv_cancel₀ hz]
    field_simp at hp ⊢
    linear_combination -hp

/-- The three ordered labels for X³+aX²+bX+c, with repetitions. -/
def monicLabels (a b c : ℂ) : Fin 3 → ℂ :=
  let p := complexMonicDepressedP a b
  let q := complexMonicDepressedQ a b c
  let u := quotientU p q
  let v := (-p / 3) / u
  ![u + v - a / 3, omega * u + omega ^ 2 * v - a / 3, omega ^ 2 * u + omega * v - a / 3]

theorem monicLabels_factor (a b c x : ℂ) :
    ∏ i, (x - monicLabels a b c i) = x ^ 3 + a * x ^ 2 + b * x + c := by
  let p := complexMonicDepressedP a b
  let q := complexMonicDepressedQ a b c
  let u := quotientU p q
  let v := (-p / 3) / u
  have hp : u ^ 3 + v ^ 3 = -q ∧ u * v = -p / 3 := by
    simpa only [u, v, quotientU_eq, div_eq_mul_inv] using meadow_pair p q
  have h := factorization_identity (x + a / 3) u v
  rw [hp.1, hp.2] at h
  simp [Fin.prod_univ_three, monicLabels]
  dsimp only [u, v, p, q] at h
  unfold complexMonicDepressedP complexMonicDepressedQ at h ⊢
  linear_combination h

end CubicEquation.CardanoComplex
