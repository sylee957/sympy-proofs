module

public import SympyProofs.Sum.RationalSum.Preparation

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

open scoped Classical Std.WP

private def halfEuclid (r previous u previousU : Polynomial ℚ) : Polynomial ℚ × Polynomial ℚ :=
  if _hr : r = 0 then (previous, previousU) else
    let q := previous / r
    halfEuclid (previous % r) r (previousU - q * u) u
termination_by r.degree
decreasing_by exact degree_mod_lt _ _hr

private theorem halfEuclid_eq_aux (r previous u previousU v previousV : Polynomial ℚ) :
    halfEuclid r previous u previousU =
      let z := EuclideanDomain.xgcdAux r u v previous previousU previousV
      (z.1, z.2.1) := by
  induction r, previous using EuclideanDomain.GCD.induction
      generalizing u previousU v previousV with
  | H0 previous => simp [halfEuclid, EuclideanDomain.xgcd_zero_left]
  | H1 r previous hr ih =>
    rw [halfEuclid, dite_eq_right hr, EuclideanDomain.xgcdAux_rec hr]
    exact ih _ _ _ _

set_option experimental.vcgen true in
private theorem inverseMod_eq_halfEuclid (a b : Polynomial ℚ) :
    inverseMod a b =
      let z := halfEuclid a b 1 0
      (C z.1.leadingCoeff⁻¹ * z.2) % b := by
  dsimp only
  generalize he : inverseMod a b = out
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ (r, previous, u, previousU) =>
      halfEuclid r previous u previousU = halfEuclid a b 1 0 ∧
      (r ≠ 0 → r.natDegree + pref.length < a.natDegree + 1)
  case vc1 => simp
  case vc2 =>
    rename_i r previous u previousU hi s1 s2
    have hr : r = 0 := by
      by_contra hr
      have h := hi.2 hr
      simp only [Std.Internal.ForIn.toList_range, Std.Legacy.Range.size, Nat.sub_zero,
        Nat.add_sub_cancel, Nat.div_one, List.length_range'] at h
      omega
    have h := hi.1
    rw [hr, halfEuclid] at h
    simp only [↓reduceDIte] at h
    rw [← h]
  case vc3 =>
    rename_i pref cur suff hs r previous u previousU hi s1 s2 hr
    exact ⟨hi.1, fun h => (h hr).elim⟩
  case vc4 =>
    rename_i pref cur suff hs r previous u previousU hi s1 s2 hr
    refine ⟨?_, ?_⟩
    · have h := hi.1
      rw [halfEuclid, dite_eq_right hr] at h
      exact h
    · intro hn
      have hdeg : next.natDegree < r.natDegree :=
        natDegree_lt_natDegree hn (degree_mod_lt _ hr)
      have hbound := hi.2 hr
      simp only [List.length_append, List.length_singleton]
      omega

/-- The half-Euclidean routine returns an inverse for every coprime input pair. -/
theorem inverseMod_spec (a b : Polynomial ℚ) (hab : IsCoprime a b) :
    b ∣ a * inverseMod a b - 1 := by
  rw [inverseMod_eq_halfEuclid, halfEuclid_eq_aux a b 1 0 0 1,
    EuclideanDomain.xgcdAux_val, EuclideanDomain.xgcd_val]
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
