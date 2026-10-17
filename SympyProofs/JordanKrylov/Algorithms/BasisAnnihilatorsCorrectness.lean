import SympyProofs.JordanKrylov.Algorithms.BasisAnnihilators
import Std.Tactic.Do
import Std.WP

namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped Std.WP

private def column (ms : Array (Array ℕ)) (j : ℕ) : Array ℕ := ms[j]?.getD #[]

private theorem column_modify (ms : Array (Array ℕ)) (j k r : ℕ) (hj : j < ms.size) :
    column (ms.modify j (fun c => c.push r)) k =
      if k = j then (column ms k).push r else column ms k := by
  simp only [column, Array.getElem?_modify]
  by_cases h : k = j
  · subst k; simp [hj]
  · simp [h, Ne.symm h]

private theorem column_sizes_push {q r : ℕ} (ms : Array (Array ℕ))
    (pref suff : List (Fin q)) (j : Fin q) (used : ℕ)
    (hsplit : List.finRange q = pref ++ j :: suff)
    (hi : ms.size = q ∧ ∀ k : Fin q,
      (column ms k.val).size = r + if k ∈ pref then 1 else 0) :
    (ms.modify j.val (fun c => c.push used)).size = q ∧
      ∀ k : Fin q, (column (ms.modify j.val (fun c => c.push used)) k.val).size =
        r + if k ∈ pref ++ [j] then 1 else 0 := by
  refine ⟨by simpa using hi.1, ?_⟩
  intro k
  have hj : j.val < ms.size := Nat.lt_of_lt_of_eq j.isLt hi.1.symm
  rw [column_modify _ _ _ _ hj]
  have hn : j ∉ pref := by
    intro hmem
    have hnd := List.nodup_finRange q
    rw [hsplit] at hnd
    exact (List.nodup_append.mp hnd).2.2 j hmem j (by simp) rfl
  by_cases hk : k = j
  · subst k; simp [hi.2, hn]
  · simp [Fin.val_ne_iff.mpr hk, hi.2, hk]

/-- There is one polynomial per vector and one equally long column per factor. -/
theorem computeBasisAnnihilators_sizes
    (K : Type) [Field K] [DecidableEq K] [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (factors : Array (K[X] × ℕ))
    (e : Fin m → (Fin n → K)) :
    let out := computeBasisAnnihilators K A factors e
    out.1.size = m ∧ out.2.size = factors.size ∧ ∀ col ∈ out.2, col.size = m := by
  generalize h : computeBasisAnnihilators K A factors e = out
  dsimp only
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ (ps, ms) => ps.size = pref.length ∧ ms.size = factors.size ∧
      ∀ k : Fin factors.size, (column ms k.val).size = pref.length
  · by
      rename_i outerPref i outerSuff hsplit ps ms hi
      exact fun pref _ (ms, _, _, _) => ms.size = factors.size ∧
        ∀ k : Fin factors.size, (column ms k.val).size = outerPref.length + if k ∈ pref then 1 else 0
  · fun _ _ _ => True
  · fun _ _ _ => True
  case vc1 => simp [polynomials, multiplicities, column]
  case vc2 =>
    rename_i ps ms hi
    refine ⟨by simpa using hi.1, hi.2.1, ?_⟩
    intro col hc
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hc
    have he := hi.2.2 ⟨k, Nat.lt_of_lt_of_eq hk hi.2.1⟩
    simpa [column, hk] using he
  case vc3 =>
    rename_i pref i suff hsplit ps ms hi
    simpa using hi.2
  case vc4 =>
    rename_i pref i suff hsplit ps ms hout nextMs current c rest hi _ _
    refine ⟨by simpa [polynomials] using hout.1, hi.1, ?_⟩
    intro k
    simpa using hi.2 k
  case vc5 =>
    rename_i pref j suff hsplit ms current c rest hi _ _ jp hn co nextB nextC used nextProbe _ _
    exact column_sizes_push ms pref suff j used hsplit hi
  case vc6 =>
    rename_i pref j suff hsplit ms current c rest hi _ _ jp hz
    exact column_sizes_push ms pref suff j 0 hsplit hi

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
      exact fun _ suff (ms, b0, c, rest) =>
        rest = suff.map (fun j => factors[j.val]) ∧ c.Monic ∧ c ∣ minimalAnnihilatingPolynomial K A v ∧
        b0 = aeval A c *ᵥ v ∧
        minimalAnnihilatingPolynomial K A v ∣ c * product rest
  · fun pref _ c => c = product pref
  · by
      let v := b0
      rename_i pref j suff hsplit ms current c rest hi _ _ jp hn co hc
      exact fun pref _ (b0, c, used, probe) =>
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
    · simpa [← List.ofFn_eq_map] using (List.ofFn_getElem (xs := factors.toList)).symm
    apply (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
    have he : product factors.toList = A.charpoly := by
      simpa [product, List.flatMap_def, List.prod_flatten, List.map_map, Function.comp_def, List.prod_replicate] using hfactorization.symm
    rw [he, Matrix.aeval_self_charpoly, zero_mulVec]
  case vc4 =>
    rename_i pref i suff hsplit out ms hout nextMs current c rest hi _ _
    rcases hi with ⟨hr, hc, hd, hb, hcover⟩
    have he : c = minimalAnnihilatingPolynomial K A (e i) := by
      apply eq_of_monic_of_dvd_of_natDegree_le
        (minimalAnnihilatingPolynomial_monic K A (e i)) hc
      · simpa [hr, product] using hcover
      · exact natDegree_le_of_dvd hd (minimalAnnihilatingPolynomial_monic K A _).ne_zero
    simp [polynomials, hout, he]
  case vc5 =>
    simp [cofactor, hops.one_eq, product]
  case vc10 =>
    rename_i pref g exponent suff hsplit c hc
    simp [cofactor, hops.mul_eq, hops.pow_eq, hc, product]
  case vc6 =>
    rename_i pref j suff hsplit ms current c rest hi _ _ jp hn co hc
    rcases hi with ⟨hr, hmon, hd, hb, hcover⟩
    refine ⟨hmon, hd, hb, ?_, ?_⟩
    · by_cases hempty : remaining = []
      · simp [probe, hempty, product, hb]
      · simp [probe, List.isEmpty_iff, hempty, hc, hb, apply_mul K hops]
    · simpa only [List.length_nil, Nat.sub_zero, remaining, hr,
        List.map_cons, List.tail_cons, product, List.map_cons, List.prod_cons] using hcover
  case vc7 =>
    rename_i pref j suff hsplit ms current c rest hi _ _ jp hn co hc nextB nextC nextUsed nextProbe hnext _ _
    refine ⟨?_, hnext.1, hnext.2.1, hnext.2.2.1, ?_⟩
    · simp only [remaining, hi.1, List.map_cons, List.tail_cons]
    · simpa only [List.length_range, Nat.sub_self, pow_zero, one_mul] using hnext.2.2.2.2
  case vc8 =>
    rename_i current c used probeValue hi _ _ hz
    refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, ?_⟩
    simp only [List.length_range, Nat.sub_self, pow_zero, one_mul]
    exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
      (hi.2.2.2.1.symm.trans hz)
  case vc9 =>
    rename_i factorPref jFactor suffix hsplit ms oldB oldC rest houter _ _ jp hnonzero co hco _
      steps j tail hsteps current c used probeValue hi _ _ hn
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
  case vc11 =>
    rename_i pref j suff hsplit ms current c rest hi _ _ jp hz
    have hz : current = 0 := Classical.not_not.mp hz
    refine ⟨by simp [remaining, hi.1], hi.2.1, hi.2.2.1, hi.2.2.2.1, ?_⟩
    apply dvd_mul_of_dvd_left
    exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr (hi.2.2.2.1.symm.trans hz)

private def entry (ms : Array (Array ℕ)) (i j : ℕ) : ℕ := (column ms j)[i]?.getD 0

private theorem entry_push (ms : Array (Array ℕ)) (j k i used : ℕ) (hj : j < ms.size) :
    entry (ms.modify j (fun c => c.push used)) i k =
      if k = j ∧ i = (column ms j).size then used else entry ms i k := by
  unfold entry
  rw [column_modify _ _ _ _ hj]
  by_cases hk : k = j
  · subst k; by_cases hi : i = (column ms j).size <;> simp [Array.getElem?_push, hi]
  · simp [hk]

/-- Reconstruct one vector's polynomial from the indicated factor columns. -/
noncomputable def annihilatorFactorProduct {K : Type*} [Field K]
    (factors : Array (K[X] × ℕ)) (js : List (Fin factors.size))
    (ms : Array (Array ℕ)) (i : ℕ) : K[X] :=
  (js.map (fun j => factors[j.val].1 ^ entry ms i j.val)).prod

private theorem factorProduct_old {K : Type*} [Field K]
    (factors : Array (K[X] × ℕ)) (js : List (Fin factors.size))
    (ms : Array (Array ℕ)) (i j used : ℕ) (hj : j < ms.size)
    (hi : i < (column ms j).size) :
    annihilatorFactorProduct factors js (ms.modify j (fun c => c.push used)) i =
      annihilatorFactorProduct factors js ms i := by
  unfold annihilatorFactorProduct
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [entry_push _ _ _ _ _ hj]
  simp [Nat.ne_of_lt hi]

private theorem factorProduct_next {K : Type*} [Field K]
    (factors : Array (K[X] × ℕ)) (pref : List (Fin factors.size))
    (ms : Array (Array ℕ)) (i used : ℕ) (j : Fin factors.size)
    (hj : j.val < ms.size) (hi : (column ms j.val).size = i) (hn : j ∉ pref) :
    annihilatorFactorProduct factors (pref ++ [j])
      (ms.modify j.val (fun c => c.push used)) i =
      annihilatorFactorProduct factors pref ms i * factors[j.val].1 ^ used := by
  unfold annihilatorFactorProduct
  simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
  rw [entry_push _ _ _ _ _ hj]
  simp only [hi, and_self, ↓reduceIte]
  congr 1
  congr 1
  apply List.map_congr_left
  intro k hk
  have hne : k ≠ j := by intro he; subst k; exact hn hk
  rw [entry_push _ _ _ _ _ hj]
  simp [Fin.val_ne_iff.mpr hne]

private def FactorState {K : Type*} [Field K]
    (factors : Array (K[X] × ℕ)) (ps : Array K[X])
    (pref : List (Fin factors.size)) (ms : Array (Array ℕ)) (c : K[X]) : Prop :=
  ms.size = factors.size ∧
  (∀ k : Fin factors.size, (column ms k.val).size = ps.size + if k ∈ pref then 1 else 0) ∧
  (∀ i, (hi : i < ps.size) →
    annihilatorFactorProduct factors (List.finRange factors.size) ms i = ps[i]) ∧
  c = annihilatorFactorProduct factors pref ms ps.size

private theorem factorState_push {K : Type*} [Field K]
    (factors : Array (K[X] × ℕ)) (ps : Array K[X])
    (pref suff : List (Fin factors.size)) (j : Fin factors.size)
    (ms : Array (Array ℕ)) (c : K[X]) (used : ℕ)
    (hsplit : List.finRange factors.size = pref ++ j :: suff)
    (hi : FactorState factors ps pref ms c) :
    FactorState factors ps (pref ++ [j])
      (ms.modify j.val (fun col => col.push used)) (c * factors[j.val].1 ^ used) := by
  have hsz := column_sizes_push ms pref suff j used hsplit ⟨hi.1, hi.2.1⟩
  have hj : j.val < ms.size := Nat.lt_of_lt_of_eq j.isLt hi.1.symm
  have hn : j ∉ pref := by
    intro hm
    have hnd := List.nodup_finRange factors.size
    rw [hsplit] at hnd
    exact (List.nodup_append.mp hnd).2.2 j hm j (by simp) rfl
  have hlen : (column ms j.val).size = ps.size := by simpa [hn] using hi.2.1 j
  refine ⟨hsz.1, hsz.2, ?_, ?_⟩
  · intro i hi'
    rw [factorProduct_old _ _ _ _ _ _ hj (by omega)]
    exact hi.2.2.1 i hi'
  · rw [factorProduct_next _ _ _ _ _ _ hj hlen hn, hi.2.2.2]

/-- Every vector's exponent entries reconstruct its returned polynomial. -/
theorem computeBasisAnnihilators_factorization
    (K : Type) [Field K] [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (factors : Array (K[X] × ℕ))
    (e : Fin m → (Fin n → K)) :
    ∀ i (hi : i < (computeBasisAnnihilators K A factors e).1.size),
      annihilatorFactorProduct factors (List.finRange factors.size)
        (computeBasisAnnihilators K A factors e).2 i =
      (computeBasisAnnihilators K A factors e).1[i] := by
  generalize h : computeBasisAnnihilators K A factors e = out
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun _ _ (ps, ms) => ms.size = factors.size ∧
      (∀ k : Fin factors.size, (column ms k.val).size = ps.size) ∧
      ∀ i (hi : i < ps.size), annihilatorFactorProduct factors (List.finRange factors.size) ms i = ps[i]
  · by
      rename_i pref i suff hsplit ps ms hi
      exact fun pref _ (ms, _, c, _) => FactorState factors ps pref ms c
  · fun _ _ _ => True
  · by
      rename_i pref j suff hsplit ms current c rest hi _ _ jp hn co
      exact fun _ _ (_, nextC, used, _) => nextC = c * factors[j.val].1 ^ used
  case vc1 => simp [multiplicities, polynomials, column]
  case vc2 =>
    rename_i ps ms hi i hidx
    exact hi.2.2 i hidx
  case vc3 =>
    rename_i pref i suff hsplit ps ms hi
    exact ⟨hi.1, by simpa using hi.2.1, hi.2.2, by simp [candidate, hops.one_eq, annihilatorFactorProduct]⟩
  case vc4 =>
    rename_i pref i suff hsplit ps ms hout nextMs current c rest hi _ _
    refine ⟨hi.1, ?_, ?_⟩
    · intro k; simpa [polynomials] using hi.2.1 k
    · intro k hk
      by_cases hlt : k < ps.size
      · simpa [polynomials, Array.getElem_push, hlt] using hi.2.2.1 k hlt
      · have he : k = ps.size := by simp only [polynomials, Array.size_push] at hk; omega
        subst k
        simpa [polynomials] using hi.2.2.2.symm
  case vc5 => simp
  case vc6 =>
    rename_i pref j suff hsplit ms current c rest hi _ _ jp hn co nextB nextC used nextProbe hnext _ _
    rw [hnext]
    exact factorState_push factors _ pref suff j ms c used hsplit hi
  case vc7 => assumption
  case vc8 =>
    rename_i current c used probeValue hi _ _ hn
    simp only [candidate, hops.mul_eq, hi, used, pow_succ, mul_assoc]
  case vc9 =>
    rename_i pref j suff hsplit ms current c rest hi _ _ jp hz
    simpa using factorState_push factors _ pref suff j ms c 0 hsplit hi

private theorem factor_emultiplicity_zero {K : Type*} [Field K]
    {f g : K[X]} (hf : f.Monic) (hi : Irreducible f)
    (hg : g.Monic) (hj : Irreducible g) (hne : f ≠ g) :
    emultiplicity f g = 0 := by
  apply emultiplicity_eq_zero.mpr
  intro hd
  exact hne (Polynomial.eq_of_monic_of_associated hf hg
    ((hi.dvd_irreducible_iff_associated hj).mp hd))

private theorem factorProduct_emultiplicity_get {K : Type*} [Field K]
    (factors : Array (K[X] × ℕ)) (ms : Array (Array ℕ)) (i : ℕ)
    (hg : ∀ fm ∈ factors, fm.1.Monic ∧ Irreducible fm.1)
    (hd : (factors.toList.map Prod.fst).Nodup) (j : Fin factors.size) :
    emultiplicity factors[j.val].1 (annihilatorFactorProduct factors (List.finRange factors.size) ms i) =
      (entry ms i j.val : ℕ) := by
  have hf := hg factors[j.val] (Array.getElem_mem _)
  unfold annihilatorFactorProduct
  rw [← List.ofFn_eq_map, List.prod_ofFn]
  rw [Finset.emultiplicity_prod hf.2.prime, Finset.sum_eq_single j]
  · exact emultiplicity_pow_self hf.2.ne_zero hf.2.not_isUnit _
  · intro k hk hkj
    have hgk := hg factors[k.val] (Array.getElem_mem _)
    have hne : factors[j.val].1 ≠ factors[k.val].1 := by
      intro he
      have hi := List.nodup_iff_injective_getElem.mp hd
        (a₁ := ⟨j.val, by simp⟩) (a₂ := ⟨k.val, by simp⟩) (by simpa using he)
      exact hkj (Fin.ext (congrArg Fin.val hi).symm)
    rw [emultiplicity_pow hf.2.prime,
      factor_emultiplicity_zero hf.1 hf.2 hgk.1 hgk.2 hne]
    simp
  · simp

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

/-- Column `j`, entry `i`, is the factor multiplicity in polynomial `i`. -/
theorem computeBasisAnnihilators_rank
    (K : Type) [Field K] [DecidableEq K] [Operations K] (hops : Operations.IsCorrect K)
    {n m : ℕ} (A : Matrix (Fin n) (Fin n) K) (factors : Array (K[X] × ℕ))
    (e : Fin m → (Fin n → K))
    (hg : ∀ fm ∈ factors, fm.1.Monic ∧ Irreducible fm.1)
    (hd : (factors.toList.map Prod.fst).Nodup) (i : Fin m) (j : Fin factors.size)
    {hj : j.val < (computeBasisAnnihilators K A factors e).2.size}
    {hi : i.val < (computeBasisAnnihilators K A factors e).2[j.val].size}
    {hp : i.val < (computeBasisAnnihilators K A factors e).1.size} :
    (computeBasisAnnihilators K A factors e).2[j.val][i.val] =
      multiplicity factors[j.val].1 (computeBasisAnnihilators K A factors e).1[i.val] := by
  have he := factorProduct_emultiplicity_get factors
    (computeBasisAnnihilators K A factors e).2 i.val hg hd j
  rw [computeBasisAnnihilators_factorization K hops A factors e i.val hp] at he
  have he := (multiplicity_eq_of_emultiplicity_eq_some he).symm
  simpa [entry, column, hi, hj] using he

end SympyProofs.JordanKrylov
