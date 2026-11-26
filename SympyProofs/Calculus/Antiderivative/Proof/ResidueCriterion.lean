module

public import SympyProofs.Calculus.Antiderivative.Proof.ResidueIdentity
public import SympyProofs.Calculus.Antiderivative.Extension.SimplePole
public import SympyProofs.Calculus.Antiderivative.Extension.LogDeriv
import Mathlib.Tactic.LinearCombination

/-! On a squarefree normal denominator, every elementary integral must have a constant residue
at each prime, even after adding any rational function regular at the normal poles. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Residue

open Polynomial Extension.SimplePole
open scoped Polynomial

section Local

variable {F k : Type} [Field F] [Field k]

noncomputable local instance : Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

local notation "ι" => algebraMap F[X] (RatFunc F)

private theorem local_fraction (δ : Derivation ℤ F[X] F[X]) {p : F[X]} (hp : Prime p)
    (u : RatFunc F) : ∃ e : ℤ, Integral p
      (Extension.extend δ u / u - (e : RatFunc F) * (ι (δ p) / ι p)) := by
  by_cases hu : u = 0
  · refine ⟨0, ?_⟩
    simpa [hu] using integral_algebraMap hp (0 : F[X])
  obtain ⟨N,d,hN,hd,rfl⟩ : ∃ N d : F[X], N ≠ 0 ∧ d ≠ 0 ∧ u = ι N / ι d :=
    ⟨_,_,RatFunc.num_ne_zero hu, RatFunc.denom_ne_zero _, (RatFunc.num_div_denom _).symm⟩
  obtain ⟨i,hi⟩ := local_logDeriv_poly δ hp hN
  obtain ⟨j,hj⟩ := local_logDeriv_poly δ hp hd
  refine ⟨(i:ℤ)-j, ?_⟩
  rw [Extension.logDeriv_div (RatFunc.algebraMap_ne_zero hN) (RatFunc.algebraMap_ne_zero hd),
    Extension.extend_poly, Extension.extend_poly]
  convert hi.sub hp hj using 1
  push_cast
  ring

private theorem simple_fraction (δ : Derivation ℤ F[X] F[X]) (u : RatFunc F) :
    Simple (Extension.extend δ u / u) := by
  by_cases hu : u = 0
  · intro p hp
    simpa [hu] using integral_algebraMap hp (0 : F[X])
  obtain ⟨N,d,hN,hd,rfl⟩ : ∃ N d : F[X], N ≠ 0 ∧ d ≠ 0 ∧ u = ι N / ι d :=
    ⟨_,_,RatFunc.num_ne_zero hu, RatFunc.denom_ne_zero _, (RatFunc.num_div_denom _).symm⟩
  rw [Extension.logDeriv_div (RatFunc.algebraMap_ne_zero hN) (RatFunc.algebraMap_ne_zero hd),
    Extension.extend_poly, Extension.extend_poly]
  exact (simple_logDeriv δ hN).sub (simple_logDeriv δ hd)

private theorem extend_fraction (δ : Derivation ℤ F[X] F[X]) (N d : F[X]) :
    Extension.extend δ (ι N / ι d) = ι (δ N * d - N * δ d) / ι (d*d) := by
  rw [Extension.extend_div]
  simp [pow_two]

/-- A finite Liouville form forces divisibility by the specialized residue numerator at every
normal pole, for any injection of its scalar coefficients into the polynomial coefficient field. -/
theorem local_necessary [CharZero F] (j : k →+* F) (δ : Derivation ℤ F[X] F[X])
    {A D : F[X]} {L : RatFunc F} (hs : Squarefree D) {p : F[X]} (hp : Prime p) (hd : p ∣ D)
    (normal : ¬p ∣ δ p) (hL : Integral p L) {I : Type} [Fintype I]
    (c : I → k) (u : I → RatFunc F) (w : RatFunc F)
    (he : ι A / ι D + L = Extension.extend δ w +
      ∑ i, RatFunc.C (j (c i)) * (Extension.extend δ (u i) / u i)) :
    ∃ z : k, p ∣ A - C (j z) * δ D := by
  obtain ⟨E,rfl⟩ := hd
  have hE : ¬ p ∣ E := fun h => hp.not_isUnit (hs p (mul_dvd_mul_left p h))
  have hp0 : ι p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
  have E0 : E ≠ 0 := fun z => hE (z ▸ dvd_zero p)
  have hE0 : ι E ≠ 0 := RatFunc.algebraMap_ne_zero E0
  have cint (i : I) : Integral p (RatFunc.C (j (c i))) := by
    rw [← RatFunc.algebraMap_C]
    exact integral_algebraMap hp _
  have s1 : Integral p (ι p * (ι A / ι (p * E))) := ⟨A,E,hE, by rw [map_mul]; field_simp⟩
  have s3 (i : I) : Integral p (ι p * (RatFunc.C (j (c i)) * (Extension.extend δ (u i) / u i))) := by
    have h := (cint i).mul hp (simple_fraction δ (u i) p hp)
    rwa [mul_left_comm] at h
  have sw : Integral p (ι p * Extension.extend δ w) := by
    have e : ι p * Extension.extend δ w = ι p * (ι A / ι (p * E)) + ι p * L -
        ∑ i, ι p * (RatFunc.C (j (c i)) * (Extension.extend δ (u i) / u i)) := by
      rw [← Finset.mul_sum]
      linear_combination (-(ι p)) * he
    rw [e]
    exact ((s1.add hp ((integral_algebraMap hp p).mul hp hL)).sub hp
      (integral_finset_sum hp _ _ fun i _ => s3 i))
  obtain ⟨N,d,hd,cop,rfl⟩ : ∃ N d : F[X], d ≠ 0 ∧ IsCoprime N d ∧ w = ι N / ι d :=
    ⟨_,_,RatFunc.denom_ne_zero _, RatFunc.isCoprime_num_denom _, (RatFunc.num_div_denom _).symm⟩
  rw [extend_fraction] at sw
  have npd := not_dvd_of_simple_deriv δ hp normal hd cop sw
  have iw : Integral p (Extension.extend δ (ι N / ι d)) := by
    rw [extend_fraction]
    refine ⟨δ N * d - N * δ d, d*d, fun h => (hp.dvd_mul.mp h).elim npd npd, ?_⟩
    exact div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero (mul_ne_zero hd hd))
  choose f hf using fun i => local_fraction δ hp (u i)
  refine ⟨∑ i, c i * (f i : k), ?_⟩
  apply dvd_of_integral_residue δ hp hE
  have cc : RatFunc.C (j (∑ i, c i * (f i : k))) =
      ∑ i, RatFunc.C (j (c i)) * (f i : RatFunc F) := by simp
  have eq : ι A / ι (p * E) - RatFunc.C (j (∑ i, c i * (f i : k))) * (ι (δ p) / ι p) =
      ∑ i, RatFunc.C (j (c i)) * (Extension.extend δ (u i) / u i -
        (f i : RatFunc F) * (ι (δ p) / ι p)) + Extension.extend δ (ι N / ι d) - L := by
    rw [cc, Finset.sum_mul]
    simp only [mul_sub, Finset.sum_sub_distrib, mul_assoc]
    linear_combination he
  rw [eq]
  exact ((integral_finset_sum hp _ _ fun i _ => (cint i).mul hp (hf i)).add hp iw).sub hp hL

end Local

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _
noncomputable local instance : Algebra ℤ (RatFunc (M k n)) := Ring.toIntAlgebra _

local notation "ι" => algebraMap (M k n)[X] (RatFunc (M k n))

/-- A Liouville form forces a constant residue on every normal prime divisor, including for
numerators formed using arbitrary scalars in the model. -/
theorem model_residues_necessary (t : Tower R n) (g : ReducedGen (K R n)) (A D : (M k n)[X])
    (hsq : Squarefree D) (hn : ∀ p : (M k n)[X], Prime p → p ∣ D → ¬ p ∣ t.polyDerModel k g p)
    (L : RatFunc (M k n)) (hL : ∀ p : (M k n)[X], Prime p → p ∣ D → Integral p L)
    (form : (t.step g).Elementary k ((Model.stepEquiv k n).symm (ι A / ι D + L))) :
    ∀ p : (M k n)[X], Prime p → p ∣ D →
      ∃ c : k, p ∣ A - C (Model.C k n c) * t.polyDerModel k g D := by
  classical
  obtain ⟨w,logs,hform⟩ := form
  let e := Model.stepEquiv k n
  let δ := t.polyDerModel k g
  let term (v : k × M k (n+1)) := Model.C k (n+1) v.1 * ((t.step g).modelD k v.2 / v.2)
  have hs : (logs.map term).sum = ∑ i : Fin logs.length, term (logs.get i) := by
    rw [← Fin.sum_ofFn]
    change _ = (List.ofFn (term ∘ logs.get)).sum
    rw [← List.map_ofFn, List.ofFn_get]
  have hstep (x : M k (n+1)) : e ((t.step g).modelD k x) = Extension.extend δ (e x) :=
    t.stepEquiv_modelD k g x
  have hC (c : k) : e (Model.C k (n+1) c) = RatFunc.C (Model.C k n c) := by
    change Model.stepEquiv k n (Model.C k (n+1) c) = _
    rw [← Model.includeVars_C k (Nat.le_succ n) c, Model.stepEquiv_include]
  intro p hp hd
  apply local_necessary (Model.C k n) δ hsq hp hd (hn p hp hd) (hL p hp hd)
    (fun i : Fin logs.length => (logs.get i).1) (fun i => e (logs.get i).2) (e w)
  change _ = (t.step g).modelD k w + (logs.map term).sum at hform
  have hv := congrArg e hform
  change e (e.symm (ι A / ι D + L)) = _ at hv
  rw [RingEquiv.apply_symm_apply, map_add, hs, map_sum, hstep] at hv
  simpa only [term, map_mul, map_div₀, hstep, hC] using hv

/-- In a tower step, every normal denominator prime of an elementary fraction has a constant
residue. A term integral at those primes may be retained in the integrand. -/
theorem residues_necessary (t : Tower R n) (g : ReducedGen (K R n)) {a d : Poly (K R n)}
    (h : Input k t g a d) (L : RatFunc (M k n))
    (hL : ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) d → Integral p L)
    (form : (t.step g).Elementary k (val k (K.join a d) + (Model.stepEquiv k n).symm L)) :
    ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) d →
      ∃ c : k, p ∣ Step.modelPoly (val k) a - C (Model.C k n c) *
        t.polyDerModel k g (Step.modelPoly (val k) d) := by
  apply model_residues_necessary k t g _ _ h.squarefree h.normal L hL
  convert form using 1
  apply (Model.stepEquiv k n).injective
  simp [K.join, val_joinPoly]

/-- When every prime has a constant residue, the executable logarithmic step succeeds. -/
theorem logPart_of_residues [IsAlgClosed k] (t : Tower R n) (g : ReducedGen (K R n))
    {a d : Poly (K R n)} (h : Input k t g a d)
    (hl : ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) d →
      ∃ c : k, p ∣ Step.modelPoly (val k) a - C (Model.C k n c) *
        t.polyDerModel k g (Step.modelPoly (val k) d)) :
    logPart a d (Step.polyDer t.D (g.velocity t.D) d) ((g.velocity t.D).coeff 1) ≠ none := by
  classical
  intro fail
  let e := Step.polyDer t.D (g.velocity t.D) d
  let D := Step.modelPoly (val k) d
  let A := Step.modelPoly (val k) a
  let δ := t.polyDerModel k g
  let S := roots (a := a) (d := d) (e := e) k
  let emb : k ↪ M k n := ⟨Model.C k n, (Model.C k n).injective⟩
  have hd := h.den_ne_zero k
  have hz := h.resultant_ne_zero k
  have hs := constantRoots_squarefree k hz
  have cover (p : (M k n)[X]) (hp : Prime p) (hpd : p ∣ D) :
      ∃ x ∈ S.map emb, p ∣ A - C x * δ D := by
    obtain ⟨c,hc⟩ := hl p hp hpd
    refine ⟨emb c, Finset.mem_map.mpr ⟨c, ?_, rfl⟩, hc⟩
    change c ∈ (Step.modelPoly (Model.constantHom k)
      (constantRoots (residuePolynomial a d e))).roots.toFinset
    rw [Multiset.mem_toFinset, mem_roots hs.ne_zero, residue_roots k a d e hd c,
      show e = Step.polyDer t.D (g.velocity t.D) d from rfl,
      Tower.modelPoly_polyDer]
    exact fun H => hp.not_isUnit (H.isUnit_of_dvd' hpd hc)
  have sum := Extension.Residue.degree_sum_of_residues δ (A := A)
    h.squarefree h.normal (S.map emb) cover
  rw [Finset.sum_map] at sum
  have agree (z : k) : Extension.Residue.resGcd δ A (Step.modelPoly (val k) d) (emb z) =
      residueGcd k a d e z := by
    simp only [Extension.Residue.resGcd, residueGcd, e, Tower.modelPoly_polyDer]
    rfl
  change ∑ z ∈ S, (Extension.Residue.resGcd δ A (Step.modelPoly (val k) d) (emb z)).natDegree =
    (Step.modelPoly (val k) d).natDegree at sum
  simp only [agree] at sum
  have dg : (Step.modelPoly (val k) d).natDegree = d.natDegree := by simp [natDegree_map]
  rw [dg] at sum
  have tot := (accounted_spec k hd hz).trans sum
  change logPart a d e _ = none at fail
  rw [logPart] at fail
  split at fail
  · contradiction
  · cases hu : uniformPart a d e with
    | some out => rw [hu] at fail; contradiction
    | none =>
      rw [hu] at fail
      dsimp only at fail
      rw [rawPieces_filter k hd hz, tot, ite_eq_left rfl] at fail
      contradiction

/-- On a proper fraction with squarefree normal denominator, failure of the logarithmic
calculation excludes every elementary integral, including after a term regular at the poles. -/
theorem logPart_complete [IsAlgClosed k] (t : Tower R n) (g : ReducedGen (K R n))
    {a d : Poly (K R n)}
    (h : Input k t g a d) (L : RatFunc (M k n))
    (hL : ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) d → Integral p L)
    (fail : logPart a d (Step.polyDer t.D (g.velocity t.D) d) ((g.velocity t.D).coeff 1) = none) :
    ¬ (t.step g).Elementary k (val k (K.join a d) + (Model.stepEquiv k n).symm L) := by
  classical
  intro form
  exact logPart_of_residues k t g h (residues_necessary k t g h L hL form) fail

end SympyProofs.Calculus.Antiderivative.Residue
