import SympyProofs.JordanKrylov.Algorithms.BasisAnnihilators
import Std.Tactic.Do
import Std.WP

namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped Std.WP

/-- Array dimensions depend only on the input family and factor count. -/
theorem computeBasisAnnihilators_sizes
    (K : Type) [Field K] [DecidableEq K] [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (factors : Array (K[X] × ℕ))
    (e : Fin m → (Fin n → K)) :
    let out := computeBasisAnnihilators K A factors e
    out.1.size = m ∧ out.2.size = m ∧ ∀ row ∈ out.2, row.size = factors.size := by
  generalize h : computeBasisAnnihilators K A factors e = out
  dsimp only
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ (ps, ms) => ps.size = pref.length ∧ ms.size = pref.length ∧
      ∀ row ∈ ms, row.size = factors.size
  · fun _ suff (b0, _, rest, counts) =>
      counts.size + rest.length = factors.size ∧
        (rest = suff.map (fun j => factors[j.val]) ∨ b0 = 0)
  · fun _ _ _ => True
  · fun _ _ _ => True
  case vc1 => simp [polynomials, multiplicities]
  case vc2 =>
    rename_i ps ms hi
    simpa using hi
  case vc3 =>
    simp only [counts, Array.size_empty, remaining, Array.length_toList, Nat.zero_add, true_and]
    left
    simpa [← List.ofFn_eq_map] using (List.ofFn_getElem (xs := factors.toList)).symm
  case vc4 =>
    rename_i pref i suff hsplit ps ms hout current c rest counts hi _ _
    refine ⟨by simpa [polynomials] using hout.1, by simpa [multiplicities] using hout.2.1, ?_⟩
    intro row hr
    simp only [multiplicities, Array.mem_push] at hr
    rcases hr with hr | rfl
    · exact hout.2.2 row hr
    · simpa using hi.1
  case vc5 =>
    rename_i current c rest counts hi _ _ hz
    exact ⟨hi.1, Or.inr hz⟩
  case vc6 =>
    rename_i pref j suff hsplit current c rest counts hi _ _ hn co nextB nextC nextProbe used _ _
    have hr := hi.2.resolve_right hn
    constructor
    · simpa [counts, remaining, hr, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi.1
    · left; simp [remaining, hr]


/-- If the cofactor alone does not annihilate, another copy of the current factor is necessary. -/
private theorem necessary_power {K : Type*} [Field K] {d c f g : K[X]} (r : ℕ)
    (hc : c.Monic) (hf : Irreducible f) (hcd : c ∣ d)
    (hyes : d ∣ c * (f ^ r * g)) (hno : ¬ d ∣ c * g) : c * f ∣ d := by
  obtain ⟨q, rfl⟩ := hcd
  have hq : q ∣ f ^ r * g := (mul_dvd_mul_iff_left hc.ne_zero).mp hyes
  have hn : ¬ q ∣ g := fun h => hno (mul_dvd_mul_left c h)
  have hfq : f ∣ q := by
    by_contra h
    exact hn ((hf.coprime_pow_of_not_dvd r h).dvd_of_dvd_mul_left hq)
  exact mul_dvd_mul_left c hfq

private theorem apply_mul (K : Subfield ℂ) [Operations K]
    (hops : Operations.IsCorrect K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (c p : K[X]) (v : Fin n → K) :
    Operations.applyMatrix p A (aeval A c *ᵥ v) = aeval A (c * p) *ᵥ v := by
  rw [hops.applyMatrix_eq, mul_comm c p, map_mul, mulVec_mulVec]

/-- Grouped factor searches compute the minimal annihilator of each input vector. -/
theorem computeBasisAnnihilators_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (factors : Array (K[X] × ℕ)) (e : Fin m → (Fin n → K))
    (hg : ∀ fm ∈ factors, fm.1.Monic ∧ Irreducible fm.1)
    (hfactorization : A.charpoly =
      (factors.toList.flatMap (fun fm => List.replicate fm.2 fm.1)).prod) :
    (computeBasisAnnihilators K A factors e).1 =
      ((List.finRange m).map (fun i => minimalAnnihilatingPolynomial K A (e i))).toArray := by
  let product := fun fs : List (K[X] × ℕ) => (fs.map (fun fm => fm.1 ^ fm.2)).prod
  generalize h : computeBasisAnnihilators K A factors e = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ (ps, _) => ps = (pref.map (fun i => minimalAnnihilatingPolynomial K A (e i))).toArray
  · by
      let v := b0
      exact fun _ suff (b0, c, rest, counts) =>
        (rest = suff.map (fun j => factors[j.val]) ∨ b0 = 0) ∧ c.Monic ∧ c ∣ minimalAnnihilatingPolynomial K A v ∧
        b0 = aeval A c *ᵥ v ∧
        minimalAnnihilatingPolynomial K A v ∣ c * product rest
  · fun pref _ c => c = product pref
  · by
      let v := b0
      rename_i pref j suff hsplit current c rest counts hi _ _ hn co hc
      exact fun pref _ (b0, c, probe, used) =>
        c.Monic ∧ c ∣ minimalAnnihilatingPolynomial K A v ∧
        b0 = aeval A c *ᵥ v ∧ probe = aeval A (c * product remaining) *ᵥ v ∧
        minimalAnnihilatingPolynomial K A v ∣
          c * (factors[j.val].1 ^ (factors[j.val].2 - pref.length) * product remaining)
  case vc1 => rfl
  case vc2 => assumption
  case vc3 =>
    simp only [remaining, candidate, hops.one_eq,
      monic_one, one_dvd, map_one, one_mulVec, one_mul, true_and]
    constructor
    · left; simpa [← List.ofFn_eq_map] using (List.ofFn_getElem (xs := factors.toList)).symm
    apply (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
    have he : product factors.toList = A.charpoly := by
      simpa [product, List.flatMap_def, List.prod_flatten, List.map_map, Function.comp_def, List.prod_replicate] using hfactorization.symm
    rw [he, Matrix.aeval_self_charpoly, zero_mulVec]
  case vc4 =>
    rename_i pref i suff hsplit out ms hout current c rest counts hi _ _
    rcases hi with ⟨hr, hc, hd, hb, hcover⟩
    have he : c = minimalAnnihilatingPolynomial K A (e i) := by
      apply eq_of_monic_of_dvd_of_natDegree_le
        (minimalAnnihilatingPolynomial_monic K A (e i)) hc
      · rcases hr with hr | hz
        · simpa [hr, product] using hcover
        · exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr (hb.symm.trans hz)
      · exact natDegree_le_of_dvd hd (minimalAnnihilatingPolynomial_monic K A _).ne_zero
    simp [polynomials, hout, he]
  case vc6 =>
    simp [cofactor, hops.one_eq, product]
  case vc11 =>
    rename_i pref g exponent suff hsplit c hc
    simp [cofactor, hops.mul_eq, hops.pow_eq, hc, product]
  case vc7 =>
    rename_i pref j suff hsplit current c rest counts hi _ _ hn co hc
    rcases hi with ⟨hr, hmon, hd, hb, hcover⟩
    have hr := hr.resolve_right hn
    refine ⟨hmon, hd, hb, ?_, ?_⟩
    · by_cases hempty : remaining = []
      · simp [probe, hempty, product, hb]
      · simp [probe, List.isEmpty_iff, hempty, hc, hb, apply_mul K hops]
    · simpa only [List.length_nil, Nat.sub_zero, remaining, hr,
        List.map_cons, List.tail_cons, product, List.map_cons, List.prod_cons] using hcover
  case vc8 =>
    rename_i pref j suff hsplit current c rest counts hi _ _ hn co hc nextB nextC nextProbe nextUsed hnext _ _
    refine ⟨?_, hnext.1, hnext.2.1, hnext.2.2.1, ?_⟩
    · left
      simp only [remaining, hi.1.resolve_right hn, List.map_cons, List.tail_cons]
    · simpa only [List.length_range, Nat.sub_self, pow_zero, one_mul] using hnext.2.2.2.2
  case vc9 =>
    rename_i current c probeValue used hi _ _ hz
    refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, ?_⟩
    simp only [List.length_range, Nat.sub_self, pow_zero, one_mul]
    exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
      (hi.2.2.2.1.symm.trans hz)
  case vc10 =>
    rename_i factorPref jFactor suffix hsplit oldB oldC rest counts houter _ _ hnonzero co hco _
      steps j tail hsteps current c probeValue used hi _ _ hn
    have hf := hg factors[jFactor.val] (Array.getElem_mem _)
    have hlen : steps.length < factors[jFactor.val].2 := by
      have hl := congrArg List.length hsteps
      simp only [List.length_range, List.length_append, List.length_cons] at hl
      omega
    have hnext := necessary_power (factors[jFactor.val].2 - steps.length) hi.1 hf.2 hi.2.1
      hi.2.2.2.2 (fun hdiv => hn (hi.2.2.2.1.trans
        ((minimalAnnihilatingPolynomial_dvd_iff K A _ _).mp hdiv)))
    dsimp only [candidate, b0, probe]
    rw [hops.mul_eq]
    refine ⟨hi.1.mul hf.1, hnext, ?_, ?_, ?_⟩
    · rw [hi.2.2.1, apply_mul K hops]
    · rw [hi.2.2.2.1, apply_mul K hops, mul_right_comm c]
    · simp only [List.length_append, List.length_singleton]
      have hex : factors[jFactor.val].2 - steps.length = (factors[jFactor.val].2 - (steps.length + 1)) + 1 := by omega
      have he : c * factors[jFactor.val].1 * (factors[jFactor.val].1 ^ (factors[jFactor.val].2 - (steps.length + 1)) * product remaining) =
          c * (factors[jFactor.val].1 ^ (factors[jFactor.val].2 - steps.length) * product remaining) := by
        rw [hex, pow_succ]
        ring
      rw [he]
      exact hi.2.2.2.2
  case vc5 =>
    rename_i current c rest counts hi _ _ hz
    exact ⟨Or.inr hz, hi.2⟩

/-- Interpret an exponent list in the order of the supplied factors. -/
noncomputable def annihilatorFactorProduct {K : Type*} [Field K]
    (factors : List (K[X] × ℕ)) (counts : List ℕ) : K[X] :=
  ((factors.zip counts).map (fun p => p.1.1 ^ p.2)).prod

private theorem annihilatorFactorProduct_append {K : Type*} [Field K]
    (fs gs : List (K[X] × ℕ)) (rs ss : List ℕ) (h : fs.length = rs.length) :
    annihilatorFactorProduct (fs ++ gs) (rs ++ ss) =
      annihilatorFactorProduct fs rs * annihilatorFactorProduct gs ss := by
  simp [annihilatorFactorProduct, List.zip_append h]

private theorem annihilatorFactorProduct_zeros {K : Type*} [Field K]
    (fs : List (K[X] × ℕ)) :
    annihilatorFactorProduct fs (List.replicate fs.length 0) = 1 := by
  induction fs with
  | nil => rfl
  | cons fm fs ih => simpa [annihilatorFactorProduct, List.replicate_succ] using ih

/-- Saved exponent rows reconstruct the polynomial array in the same order. -/
theorem computeBasisAnnihilators_factorization
    (K : Type) [Field K] [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (factors : Array (K[X] × ℕ))
    (e : Fin m → (Fin n → K)) :
    ((computeBasisAnnihilators K A factors e).2.toList.map
      (fun counts => annihilatorFactorProduct factors.toList counts.toList)) =
      (computeBasisAnnihilators K A factors e).1.toList := by
  generalize h : computeBasisAnnihilators K A factors e = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun _ _ (ps, ms) => ms.toList.map
      (fun counts => annihilatorFactorProduct factors.toList counts.toList) = ps.toList
  · fun _ suff (b0, c, rest, counts) =>
      ∃ done, factors.toList = done ++ rest ∧ counts.size = done.length ∧
        c = annihilatorFactorProduct done counts.toList ∧
          (rest = suff.map (fun j => factors[j.val]) ∨ b0 = 0)
  · fun _ _ _ => True
  · by
      rename_i pref j suff hsplit current c rest counts hi _ _ hn co
      exact fun _ _ (_, nextC, _, used) => nextC = c * factors[j.val].1 ^ used
  case vc1 => rfl
  case vc2 => assumption
  case vc3 =>
    refine ⟨[], rfl, rfl, ?_, ?_⟩
    · simp [candidate, hops.one_eq, annihilatorFactorProduct]
    · left; simpa [remaining, ← List.ofFn_eq_map] using
        (List.ofFn_getElem (xs := factors.toList)).symm
  case vc4 =>
    rename_i pref i suff hsplit ps ms hout current c rest counts hi _ _
    obtain ⟨done, hs, hsize, hc, _⟩ := hi
    simp only [multiplicities, polynomials, Array.toList_push, List.map_append,
      List.map_singleton, Array.toList_append, Array.toList_replicate, hout]
    rw [hs, annihilatorFactorProduct_append _ _ _ _ (by simpa using hsize.symm),
      annihilatorFactorProduct_zeros, mul_one, hc]
  case vc5 =>
    rename_i current c rest counts hi _ _ hz
    obtain ⟨done, hs, hn, hc, _⟩ := hi
    exact ⟨done, hs, hn, hc, Or.inr hz⟩
  case vc6 => simp
  case vc7 =>
    rename_i pref j suff hsplit current c rest cs hi _ _ hn co nextB nextC nextProbe used hnext _ _
    obtain ⟨done, hs, hsize, hc, hr⟩ := hi
    have hr := hr.resolve_right hn
    refine ⟨done ++ [factors[j.val]], ?_, ?_, ?_, ?_⟩
    · simpa [remaining, hr, List.append_assoc] using hs
    · simp [counts, hsize]
    · simp only [counts, Array.toList_push]
      rw [annihilatorFactorProduct_append _ _ _ _ (by simpa using hsize.symm)]
      simpa [annihilatorFactorProduct, hc] using hnext
    · left; simp [remaining, hr]
  case vc8 => assumption
  case vc9 =>
    rename_i current c probeValue used hi _ _ hn
    simp only [candidate, hops.mul_eq, hi, used, pow_succ, mul_assoc]

private theorem factor_emultiplicity_zero {K : Type*} [Field K]
    {f g : K[X]} (hf : f.Monic) (hi : Irreducible f)
    (hg : g.Monic) (hj : Irreducible g) (hne : f ≠ g) :
    emultiplicity f g = 0 := by
  apply emultiplicity_eq_zero.mpr
  intro hd
  exact hne (Polynomial.eq_of_monic_of_associated hf hg
    ((hi.dvd_irreducible_iff_associated hj).mp hd))

private theorem factorProduct_emultiplicity_absent {K : Type*} [Field K]
    (f : K[X]) (hf : f.Monic) (hi : Irreducible f)
    (fs : List (K[X] × ℕ)) (rs : List ℕ)
    (hg : ∀ fm ∈ fs, fm.1.Monic ∧ Irreducible fm.1)
    (hn : f ∉ fs.map Prod.fst) :
    emultiplicity f (annihilatorFactorProduct fs rs) = 0 := by
  induction fs generalizing rs with
  | nil => simp [annihilatorFactorProduct, emultiplicity_of_one_right hi.not_isUnit]
  | cons a fs ih =>
    cases rs with
    | nil => simp [annihilatorFactorProduct, emultiplicity_of_one_right hi.not_isUnit]
    | cons r rs =>
      have ha := hg a (by simp)
      have hne : f ≠ a.1 := by simpa using (by simpa using hn : f ≠ a.1 ∧ f ∉ fs.map Prod.fst).1
      have ht : f ∉ fs.map Prod.fst := (by simpa using hn : f ≠ a.1 ∧ f ∉ fs.map Prod.fst).2
      change emultiplicity f (a.1 ^ r * annihilatorFactorProduct fs rs) = 0
      rw [emultiplicity_mul hi.prime, emultiplicity_pow hi.prime,
        factor_emultiplicity_zero hf hi ha.1 ha.2 hne,
        ih rs (fun fm h => hg fm (by simp [h])) ht]
      simp

private theorem factorProduct_emultiplicity_get {K : Type*} [Field K]
    (fs : List (K[X] × ℕ)) (rs : List ℕ)
    (hg : ∀ fm ∈ fs, fm.1.Monic ∧ Irreducible fm.1)
    (hd : (fs.map Prod.fst).Nodup) (hlen : rs.length = fs.length)
    (j : Fin fs.length) :
    emultiplicity fs[j.val].1 (annihilatorFactorProduct fs rs) =
      (rs[j.val]'(by omega) : ℕ) := by
  induction fs generalizing rs with
  | nil => exact Fin.elim0 j
  | cons a fs ih =>
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      have ha := hg a (by simp)
      have hg' : ∀ fm ∈ fs, fm.1.Monic ∧ Irreducible fm.1 :=
        fun fm h => hg fm (by simp [h])
      have hd' := List.nodup_cons.mp hd
      have hl : rs.length = fs.length := by simpa using hlen
      rcases j with ⟨j, hj⟩
      cases j with
      | zero =>
        change emultiplicity a.1 (a.1 ^ r * annihilatorFactorProduct fs rs) = (r : ℕ)
        rw [emultiplicity_mul ha.2.prime, emultiplicity_pow_self ha.2.ne_zero ha.2.not_isUnit,
          factorProduct_emultiplicity_absent a.1 ha.1 ha.2 fs rs hg' hd'.1, add_zero]
      | succ j =>
        have hj' : j < fs.length := by simpa using hj
        have hb := hg' fs[j] (List.getElem_mem hj')
        have hne : fs[j].1 ≠ a.1 := by
          intro he
          apply hd'.1
          exact List.mem_map.mpr ⟨fs[j], List.getElem_mem hj', he⟩
        change emultiplicity fs[j].1 (a.1 ^ r * annihilatorFactorProduct fs rs) =
          (rs[j]'(by omega) : ℕ)
        rw [emultiplicity_mul hb.2.prime, emultiplicity_pow hb.2.prime,
          factor_emultiplicity_zero hb.1 hb.2 ha.1 ha.2 hne]
        simpa using ih rs hg' hd'.2 hl ⟨j, hj'⟩


/-- Every polynomial entry is the minimal annihilator of its input vector. -/
theorem computeBasisAnnihilators_polynomial
    (K : Subfield ℂ) [DecidableEq K] [Operations K] (hops : Operations.IsCorrect K)
    {n m : ℕ} (A : Matrix (Fin n) (Fin n) K) (factors : Array (K[X] × ℕ))
    (e : Fin m → (Fin n → K))
    (hg : ∀ fm ∈ factors, fm.1.Monic ∧ Irreducible fm.1)
    (hfactorization : A.charpoly =
      (factors.toList.flatMap (fun fm => List.replicate fm.2 fm.1)).prod)
    (i : Fin m) {hi : i.val < (computeBasisAnnihilators K A factors e).1.size} :
    (computeBasisAnnihilators K A factors e).1[i.val] =
      minimalAnnihilatingPolynomial K A (e i) := by
  have h := computeBasisAnnihilators_correct K hops A factors e hg hfactorization
  have he := congrArg (fun xs => xs[i.val]?) h
  simpa [hi] using he

/-- Every saved exponent is the multiplicity in the corresponding polynomial. -/
theorem computeBasisAnnihilators_rank
    (K : Type) [Field K] [DecidableEq K] [Operations K] (hops : Operations.IsCorrect K)
    {n m : ℕ} (A : Matrix (Fin n) (Fin n) K) (factors : Array (K[X] × ℕ))
    (e : Fin m → (Fin n → K))
    (hg : ∀ fm ∈ factors, fm.1.Monic ∧ Irreducible fm.1)
    (hd : (factors.toList.map Prod.fst).Nodup) (i : Fin m) (j : Fin factors.size)
    {hi : i.val < (computeBasisAnnihilators K A factors e).2.size}
    {hj : j.val < (computeBasisAnnihilators K A factors e).2[i.val].size}
    {hp : i.val < (computeBasisAnnihilators K A factors e).1.size} :
    (computeBasisAnnihilators K A factors e).2[i.val][j.val] =
      multiplicity factors[j.val].1 (computeBasisAnnihilators K A factors e).1[i.val] := by
  have hs := (computeBasisAnnihilators_sizes K A factors e).2.2
    (computeBasisAnnihilators K A factors e).2[i.val] (Array.getElem_mem _)
  have he := factorProduct_emultiplicity_get factors.toList
    (computeBasisAnnihilators K A factors e).2[i.val].toList
    (by simpa using hg) hd (by simpa using hs) ⟨j.val, by simp⟩
  have h := computeBasisAnnihilators_factorization K hops A factors e
  have hentry := congrArg (fun xs => xs[i.val]?) h
  have hprod : annihilatorFactorProduct factors.toList
      (computeBasisAnnihilators K A factors e).2[i.val].toList =
      (computeBasisAnnihilators K A factors e).1[i.val] := by
    simpa [hi, hp] using hentry
  rw [hprod] at he
  exact (multiplicity_eq_of_emultiplicity_eq_some he).symm

end SympyProofs.JordanKrylov
