module

public import SympyProofs.Calculus.Risch.Algebra.CoprimeCover
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The logarithmic part of a fraction `A / D` with squarefree denominator, over an arbitrary
field `F` with a derivation `δ` of `F[X]`.

For `x` in `F` let `G x` be the greatest common divisor of `A - x D′` and `D` with leading
coefficient one. If the prime factors of `D` are normal, the `G x` for distinct `x` are
coprime. When the degrees of the `G x`, for `x` in a finite set, add up to the degree of
`D`, the fraction is the sum of the `x G′ₓ / Gₓ` up to a constant, and when every prime
factor of `D` has a residue in the set, the degrees do add up. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Residue

open Polynomial

variable {F : Type*} [Field F]

local notation "ι" => algebraMap F[X] (RatFunc F)

open Classical in
/-- The greatest common divisor with leading coefficient one. -/
noncomputable def mgcd (a b : F[X]) : F[X] :=
  EuclideanDomain.gcd a b * C (EuclideanDomain.gcd a b).leadingCoeff⁻¹

open Classical in
theorem mgcd_dvd_gcd (a b : F[X]) : mgcd a b ∣ EuclideanDomain.gcd a b := by
  by_cases h : EuclideanDomain.gcd a b = 0
  · rw [mgcd, h, zero_mul]
  · exact (associated_mul_unit_left _ _ (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (inv_ne_zero (leadingCoeff_ne_zero.mpr h))))).dvd

theorem mgcd_dvd_left {a b : F[X]} : mgcd a b ∣ a := by
  classical exact (mgcd_dvd_gcd a b).trans (EuclideanDomain.gcd_dvd_left a b)

theorem mgcd_dvd_right {a b : F[X]} : mgcd a b ∣ b := by
  classical exact (mgcd_dvd_gcd a b).trans (EuclideanDomain.gcd_dvd_right a b)

theorem mgcd_bezout (a b : F[X]) : ∃ u v : F[X], u * a + v * b = mgcd a b := by
  classical
  refine ⟨EuclideanDomain.gcdA a b * C (EuclideanDomain.gcd a b).leadingCoeff⁻¹,
    EuclideanDomain.gcdB a b * C (EuclideanDomain.gcd a b).leadingCoeff⁻¹, ?_⟩
  rw [mgcd]
  linear_combination (-(C (EuclideanDomain.gcd a b).leadingCoeff⁻¹)) *
    EuclideanDomain.gcd_eq_gcd_ab a b

theorem dvd_mgcd {p a b : F[X]} (ha : p ∣ a) (hb : p ∣ b) : p ∣ mgcd a b := by
  obtain ⟨u, v, e⟩ := mgcd_bezout a b
  rw [← e]
  exact dvd_add (dvd_mul_of_dvd_right ha u) (dvd_mul_of_dvd_right hb v)

theorem mgcd_monic {a b : F[X]} (hb : b ≠ 0) : (mgcd a b).Monic := by
  classical
  exact monic_mul_leadingCoeff_inv fun h => hb (EuclideanDomain.gcd_eq_zero_iff.mp h).2

/-- A common divisor with leading coefficient one that is a combination of the two
polynomials is their greatest common divisor. -/
theorem mgcd_unique {g a b : F[X]} (hg : g.Monic) (ga : g ∣ a) (gb : g ∣ b)
    (bez : ∃ u v : F[X], u * a + v * b = g) (hb : b ≠ 0) : g = mgcd a b := by
  refine eq_of_monic_of_associated hg (mgcd_monic hb) (associated_of_dvd_dvd (dvd_mgcd ga gb) ?_)
  obtain ⟨u, v, e⟩ := bez
  rw [← e]
  exact dvd_add (dvd_mul_of_dvd_right mgcd_dvd_left u) (dvd_mul_of_dvd_right mgcd_dvd_right v)

/-- The part of `D` with residue `x`: the greatest common divisor of `A - x D′` and `D`. -/
noncomputable def resGcd (δ : Derivation ℤ F[X] F[X]) (A D : F[X]) (x : F) : F[X] :=
  mgcd (A - C x * δ D) D

/-- If every prime factor of `D` has a residue in `S`, the degrees of the parts add up to
the degree of `D`. -/
theorem degree_sum_of_residues (δ : Derivation ℤ F[X] F[X]) {D A : F[X]} (hs : Squarefree D)
    (normal : ∀ p : F[X], Prime p → p ∣ D → ¬ p ∣ δ p) (S : Finset F)
    (res : ∀ p : F[X], Prime p → p ∣ D → ∃ x ∈ S, p ∣ A - C x * δ D) :
    ∑ x ∈ S, (resGcd δ A D x).natDegree = D.natDegree :=
  degree_sum_of_cover hs S _ (fun _ _ => mgcd_dvd_right)
    (fun _ _ _ _ hxy => isCoprime_of_ne δ hs normal hxy mgcd_dvd_right mgcd_dvd_left
      mgcd_dvd_left)
    fun p hp hpD => by
      obtain ⟨x, hx, h⟩ := res p hp hpD
      exact ⟨x, hx, dvd_mgcd h hpD⟩

/-- If the degrees of the parts add up to the degree of `D`, then `A / D` is the sum of the
`x G′ₓ / Gₓ` minus a constant. Here `tw` describes the leading coefficient of a derivative:
`δ G - (deg G) tw G` has smaller degree than `G` when `G` has leading coefficient one. -/
theorem logPart_identity (δ : Derivation ℤ F[X] F[X]) (tw : F)
    (hδ : ∀ G : F[X], G.Monic → (δ G - C ((G.natDegree : F) * tw) * G).degree < G.degree)
    {D A : F[X]} (hs : Squarefree D) (normal : ∀ p : F[X], Prime p → p ∣ D → ¬ p ∣ δ p)
    (deg : A.degree < D.degree) (S : Finset F)
    (sum : ∑ x ∈ S, (resGcd δ A D x).natDegree = D.natDegree) :
    ι A / ι D = ∑ x ∈ S, RatFunc.C x * (ι (δ (resGcd δ A D x)) / ι (resGcd δ A D x)) -
      RatFunc.C ((∑ x ∈ S, ((resGcd δ A D x).natDegree : F) * x) * tw) := by
  have hD : D ≠ 0 := hs.ne_zero
  obtain ⟨G, hG⟩ : ∃ G : F → F[X], G = resGcd δ A D := ⟨_, rfl⟩
  rw [← hG] at sum ⊢
  have dvd : ∀ x, G x ∣ D := fun x => by rw [hG]; exact mgcd_dvd_right
  have left : ∀ x, G x ∣ A - C x * δ D := fun x => by rw [hG]; exact mgcd_dvd_left
  have mon : ∀ x, (G x).Monic := fun x => by rw [hG]; exact mgcd_monic hD
  have great : ∀ x (p : F[X]), p ∣ D → p ∣ A - C x * δ D → p ∣ G x := fun x p h1 h2 => by
    rw [hG]; exact dvd_mgcd h2 h1
  have cop : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → IsCoprime (G x) (G y) := fun x _ y _ hxy =>
    isCoprime_of_ne δ hs normal hxy (dvd x) (left x) (left y)
  have cover : ∀ p : F[X], Prime p → p ∣ D → ∃ x ∈ S, p ∣ G x := fun p hp hpD =>
    exists_dvd_of_degree_sum hD S G (fun x _ => dvd x) cop sum hp hpD
  choose H hH using dvd
  have Hn : ∀ x, H x ≠ 0 := fun x z => hD (by rw [hH x, z, mul_zero])
  have key := residue_sum_dvd δ hs normal S.toList S.nodup_toList G H
    (fun c _ => (hH c).symm) (fun c _ p _ hp => hp.trans (left c))
    (fun c _ p _ hpD hr => great c p hpD hr)
    (fun p hp hpD => by
      obtain ⟨x, hx, h⟩ := cover p hp hpD
      exact ⟨x, Finset.mem_toList.mpr hx, h.trans (left x)⟩)
  rw [Finset.sum_map_toList] at key
  obtain ⟨κ, hκ⟩ : ∃ κ : F, κ = (∑ x ∈ S, ((G x).natDegree : F) * x) * tw := ⟨_, rfl⟩
  rw [← hκ]
  have e : ∑ x ∈ S, C x * (C (((G x).natDegree : F) * tw) * G x) * H x = C κ * D := by
    have : κ = ∑ x ∈ S, x * (((G x).natDegree : F) * tw) := by
      rw [hκ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [C_mul (a := x)]
    linear_combination (C x * C (((G x).natDegree : F) * tw)) * (hH x).symm
  have split : ∑ x ∈ S, C x * (δ (G x) - C (((G x).natDegree : F) * tw) * G x) * H x =
      ∑ x ∈ S, C x * δ (G x) * H x - C κ * D := by
    rw [← e, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have dN : D ∣ A - ∑ x ∈ S, C x * (δ (G x) - C (((G x).natDegree : F) * tw) * G x) * H x := by
    rw [split, ← sub_add]
    exact dvd_add key (dvd_mul_left _ _)
  have degN : (A - ∑ x ∈ S, C x * (δ (G x) - C (((G x).natDegree : F) * tw) * G x) * H x).degree
      < D.degree := by
    refine (degree_sub_le _ _).trans_lt (max_lt deg ?_)
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff
      (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hD))).mpr fun x _ => ?_)
    have h1 : (C x * (δ (G x) - C (((G x).natDegree : F) * tw) * G x) * H x).degree ≤
        ((δ (G x) - C (((G x).natDegree : F) * tw) * G x) * H x).degree := by
      rw [mul_assoc]
      by_cases hx : x = 0
      · rw [hx, C_0, zero_mul, degree_zero]
        exact bot_le
      · rw [degree_C_mul hx]
    refine h1.trans_lt ?_
    have h2 : D.degree = (G x).degree + (H x).degree := by
      conv_lhs => rw [hH x]
      rw [degree_mul]
    rw [degree_mul, h2]
    exact WithBot.add_lt_add_right (degree_ne_bot.mpr (Hn x)) (hδ (G x) (mon x))
  have N0 := eq_zero_of_dvd_of_degree_lt dN degN
  rw [split] at N0
  have eA : A = ∑ x ∈ S, C x * δ (G x) * H x - C κ * D := sub_eq_zero.mp N0
  have iD : ι D ≠ 0 := RatFunc.algebraMap_ne_zero hD
  rw [div_eq_iff iD, sub_mul, Finset.sum_mul]
  conv_lhs => rw [eA]
  rw [map_sub, map_sum, map_mul, RatFunc.algebraMap_C]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have iG : ι (G x) ≠ 0 := RatFunc.algebraMap_ne_zero (mon x).ne_zero
  have hD' : ι D = ι (G x) * ι (H x) := by rw [← map_mul, ← hH x]
  rw [map_mul, map_mul, RatFunc.algebraMap_C, hD']
  field_simp

end SympyProofs.Calculus.Risch.Residue
