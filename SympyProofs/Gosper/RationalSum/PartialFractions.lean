module

public import SympyProofs.Gosper.RationalSum.Preparation

/-! Reconstruction from inverses modulo coprime occurrence powers. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial

section CRT
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Chinese remainder reconstruction with the numerators actually computed by
the algorithm. The proper-degree bound makes the reconstruction exact. -/
theorem partialFractions_reconstruct (F U : ι → Polynomial K)
    (hm : ∀ i, (F i).Monic) (hc : Pairwise (fun i j => IsCoprime (F i) (F j)))
    (hu : ∀ i, F i ∣ (∏ j ∈ Finset.univ.erase i, F j) * U i - 1)
    (N : Polynomial K) (hN : N.degree < (∏ i, F i).degree) :
    N = ∑ i, ((N * U i) %ₘ F i) * ∏ j ∈ Finset.univ.erase i, F j := by
  classical
  let M := ∏ i, F i
  let C := fun i => ∏ j ∈ Finset.univ.erase i, F j
  let A := fun i => (N * U i) %ₘ F i
  have hM : M.Monic := monic_prod_of_monic _ _ (fun i _ => hm i)
  have hC (i) : (C i).Monic := monic_prod_of_monic _ _ (fun j _ => hm j)
  have hprod (i) : F i * C i = M := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hdiv (i) : F i ∣ N - A i * C i := by
    have h₁ := (hu i).mul_left N
    have h₂ := (dvd_modByMonic_sub (N * U i) (F i)).mul_right (C i)
    have he : N - A i * C i = -(N * (C i * U i - 1)) - (A i - N * U i) * C i := by ring
    rw [he]
    exact dvd_sub (dvd_neg.mpr h₁) h₂
  have hother (i j : ι) (hij : i ≠ j) : F i ∣ A j * C j := by
    apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem _ (by simp [hij])
  have htotal : M ∣ N - ∑ i, A i * C i := by
    apply Fintype.prod_dvd_of_coprime hc
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have he : N - ((∑ j ∈ Finset.univ.erase i, A j * C j) + A i * C i) =
        (N - A i * C i) - ∑ j ∈ Finset.univ.erase i, A j * C j := by ring
    rw [he]
    exact dvd_sub (hdiv i) (Finset.dvd_sum fun j hj => hother i j (Finset.mem_erase.mp hj).1.symm)
  have hterm (i) : (A i * C i).degree < M.degree := by
    rw [← hprod i, (hC i).degree_mul, (hC i).degree_mul]
    exact (WithBot.add_lt_add_iff_right (degree_ne_bot.mpr (hC i).ne_zero)).mpr
      (degree_modByMonic_lt _ (hm i))
  have hsum : (∑ i, A i * C i).degree < M.degree := by
    apply (degree_sum_le _ _).trans_lt
    exact (Finset.sup_lt_iff (WithBot.bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hM.ne_zero))).mpr (fun i _ => hterm i)
  have hdeg : (N - ∑ i, A i * C i).degree < M.degree :=
    (degree_sub_le _ _).trans_lt (max_lt hN hsum)
  exact sub_eq_zero.mp ((hM.not_dvd_of_degree_lt · hdeg).mtr htotal)

/-- Rational-function form of the reconstruction identity. -/
theorem partialFractions_fraction (F U : ι → Polynomial K)
    (hm : ∀ i, (F i).Monic) (hc : Pairwise (fun i j => IsCoprime (F i) (F j)))
    (hu : ∀ i, F i ∣ (∏ j ∈ Finset.univ.erase i, F j) * U i - 1)
    (N : Polynomial K) (hN : N.degree < (∏ i, F i).degree) :
    (N : RatFunc K) / ((∏ i, F i : Polynomial K) : RatFunc K) =
      ∑ i, (((N * U i) %ₘ F i : Polynomial K) : RatFunc K) / (F i : RatFunc K) := by
  let C := fun i => ∏ j ∈ Finset.univ.erase i, F j
  have hprod (i) : F i * C i = ∏ j, F j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have he := partialFractions_reconstruct F U hm hc hu N hN
  have hc0 (i) : (C i : RatFunc K) ≠ 0 := by
    simpa using (monic_prod_of_monic _ _ (fun j _ => hm j)).ne_zero
  conv_lhs => rw [he]
  simp only [RatFunc.coePolynomial, map_sum, map_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hprod i, map_mul]
  exact mul_div_mul_right _ _ (hc0 i)

end CRT

/-- Normalizing the extended-gcd output and taking its remainder really gives
an inverse modulo the coprime divisor. -/
theorem xgcd_inverse (a b : Polynomial ℚ) (hab : IsCoprime a b) :
    let (d, u, _) := EuclideanDomain.xgcdAux a 1 0 b 0 1
    b ∣ a * ((C d.leadingCoeff⁻¹ * u) % b) - 1 := by
  rw [EuclideanDomain.xgcdAux_val, EuclideanDomain.xgcd_val]
  dsimp only
  let d := EuclideanDomain.gcd a b
  let u := EuclideanDomain.gcdA a b
  let v := EuclideanDomain.gcdB a b
  have hd : IsUnit d := hab.isUnit_of_dvd' (EuclideanDomain.gcd_dvd_left a b)
    (EuclideanDomain.gcd_dvd_right a b)
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp hd
  have hnorm : C d.leadingCoeff⁻¹ * d = 1 := by rw [← he]; simp [← C_mul, hc.ne_zero]
  have hbez : a * (C d.leadingCoeff⁻¹ * u) + b * (C d.leadingCoeff⁻¹ * v) = 1 := by
    have he := EuclideanDomain.gcd_eq_gcd_ab a b
    change d = a * u + b * v at he
    rw [← hnorm, he]
    ring
  have h₁ : b ∣ a * (C d.leadingCoeff⁻¹ * u) - 1 :=
    ⟨-(C d.leadingCoeff⁻¹ * v), by linear_combination hbez⟩
  have h₂ : b ∣ a * ((C d.leadingCoeff⁻¹ * u) % b - C d.leadingCoeff⁻¹ * u) :=
    (by
      rw [EuclideanDomain.mod_eq_sub_mul_div]
      convert dvd_neg.mpr (dvd_mul_right b ((C d.leadingCoeff⁻¹ * u) / b)) using 1; ring
      : b ∣ (C d.leadingCoeff⁻¹ * u) % b - C d.leadingCoeff⁻¹ * u).mul_left a
  convert dvd_add h₂ h₁ using 1; ring

end Gosper.RationalSum
