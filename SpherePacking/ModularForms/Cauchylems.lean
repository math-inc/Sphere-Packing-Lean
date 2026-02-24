module
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import SpherePacking.ModularForms.SummableLemmas.Basic
public import SpherePacking.ModularForms.SummableLemmas.Cotangent
public import SpherePacking.ModularForms.SummableLemmas.G2
public import SpherePacking.ModularForms.SummableLemmas.QExpansion
public import SpherePacking.ModularForms.SummableLemmas.IntPNat
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Order.Filter.AtTopBot.Interval


/-!
# Cauchylems

This file defines `summable_term` and proves results such as `cc`, `sum_Icc_eq_sum_Ico_succ`,
`CauchySeq_Icc_iff_CauchySeq_Ico`, ...
-/

open scoped Topology BigOperators Real Nat ArithmeticFunction.sigma

open UpperHalfPlane EisensteinSeries Metric Filter Function Complex

/-- The classical identity `∑_{n ∈ ℤ} (n^2)⁻¹ = 2 ζ(2)` (as a complex series). -/
public lemma zeta_two_eqn : ∑' (n : ℤ), ((n : ℂ) ^ 2)⁻¹ = 2 * riemannZeta 2 := by
  simpa using
    (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) (by rfl) (by simp)).symm

private lemma sum_Icc_neg_nat_eq_add_endpoints (f : ℤ → ℂ) (N : ℕ) (hn : 1 ≤ N) :
    ∑ m ∈ Finset.Icc (-N : ℤ) N, f m =
      f N + f (-N : ℤ) + ∑ m ∈ Finset.Icc (-(N - 1) : ℤ) (N - 1), f m := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn) with ⟨N', rfl⟩
  simpa [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, add_assoc] using
    (Finset.sum_Icc_succ_eq_add_endpoints (f := f) (N := N'))

/-- If the symmetric partial sums over `Icc (-N) N` form a Cauchy sequence, then `f n → 0`. -/
public lemma cc (f : ℤ → ℂ) (hc : CauchySeq fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, f m)
  (hs : ∀ n , f n = f (-n)) :
  Tendsto f atTop (𝓝 0) := by
  have h := cauchySeq_iff_tendsto_dist_atTop_0.mp hc
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  rw [Metric.tendsto_atTop] at Hg ⊢
  simp only [gt_iff_lt, ge_iff_le, dist_zero_right] at Hg ⊢
  intro ε hε
  have hh := Hg (2 * ε) (by linarith)
  obtain ⟨N, hN⟩ := hh
  use N + 1
  intro n hn
  have H3 := H n.natAbs (n - 1).natAbs N ?_ ?_
  · rw [sum_Icc_neg_nat_eq_add_endpoints (f := f) (N := n.natAbs)] at H3
    · have hN0 : (0 : ℤ) ≤ (↑N : ℤ) := by exact_mod_cast Nat.zero_le N
      have hn0 : 0 ≤ n := le_trans (add_nonneg hN0 zero_le_one) hn
      have hn1 : (1 : ℤ) ≤ n := le_trans (le_add_of_nonneg_left hN0) hn
      have h1 : (n.natAbs : ℤ) = n := (Int.eq_natAbs_of_nonneg hn0).symm
      have h2 : ((n - 1).natAbs : ℤ) = n - 1 :=
        (Int.eq_natAbs_of_nonneg (sub_nonneg.2 hn1)).symm
      simp only [h1, h2, (hs n).symm] at H3
      have hfn : f n + f n = 2 * f n := by ring
      simp only [hfn] at H3
      have H3n : 2 * ‖f n‖ ≤ g N := by
        have H3' : dist (2 * f n) 0 ≤ g N := by
          simpa [dist_add_right, zero_add] using H3
        have H3'' : ‖2 * f n‖ ≤ g N := by
          simpa [dist_zero_right] using H3'
        simpa [norm_mul, Complex.norm_two] using H3''
      have HN := hN N (by rfl)
      have := le_trans H3n (le_abs_self (g N))
      have hgnn : 2 * ‖f n‖ < 2 * ε := lt_of_le_of_lt this HN
      nlinarith
    omega
  · omega
  omega

/-- Convert a sum over `Icc l u` into a sum over `Ico l u` plus the endpoint term. -/
public lemma sum_Icc_eq_sum_Ico_succ {α : Type*} [AddCommMonoid α] (f : ℤ → α)
    {l u : ℤ} (h : l ≤ u) :
    ∑ m ∈ Finset.Icc l u, f m = (∑ m ∈ Finset.Ico l u, f m) + f u := by
  simpa using (Finset.sum_Icc_eq_sum_Ico_add (f := f) h)

/-- Cauchy convergence of symmetric sums over `Icc` implies Cauchy convergence over `Ico`. -/
public lemma CauchySeq_Icc_iff_CauchySeq_Ico (f : ℤ → ℂ) (hs : ∀ n, f n = f (-n))
  (hc : CauchySeq (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, f m) ) :
  CauchySeq (fun N : ℕ => ∑ m ∈ Finset.Ico (-N : ℤ) N, f m) := by
  have h0 := cc f hc hs
  have : CauchySeq fun n : ℕ => f n := by
    simpa using (Filter.Tendsto.cauchySeq (x := (0 : ℂ))
      (h0.comp (tendsto_natCast_atTop_atTop (R := ℤ))))
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨b, hb, H, hbb⟩ := hc
  obtain ⟨a, ha, H2, haa⟩ := this
  refine ⟨b + a, ?_, ?_, ?_⟩
  · intro n
    simp only [Pi.add_apply]
    apply add_nonneg
    · exact hb n
    apply ha n
  · intro n m N hn hm
    have H3 := H n m N hn hm
    simp only [dist_eq_norm] at H3 ⊢
    rw [Finset.sum_Icc_eq_sum_Ico_add (f := f) (by omega),
      Finset.sum_Icc_eq_sum_Ico_add (f := f) (by omega)] at H3
    refine le_trans (norm_le_add_norm_add _ (f n - f m)) ?_
    refine add_le_add ?_ (H2 n m N hn hm)
    apply le_trans ?_ H3
    apply le_of_eq
    congr
    ring
  · have HG := Filter.Tendsto.add hbb haa
    simpa using HG

/-- A Cauchy-sequence statement extracted from `G2_prod_summable1`. -/
public theorem extracted_2 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, 1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) := by
  simpa using (Filter.Tendsto.cauchySeq
    ((G2_prod_summable1 z b).hasSum.comp (by simpa using (Finset.tendsto_Ico_neg (R := ℤ)))))

/-- A Cauchy-sequence statement after inserting the correction term `δ`. -/
public theorem extracted_2_δ (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n) := by
  simpa using (Filter.Tendsto.cauchySeq
    ((G2_prod_summable1_δ z b).hasSum.comp (by simpa using (Finset.tendsto_Ico_neg (R := ℤ)))))


/-- A telescoping identity for a sum of inverse linear terms over `Ico (-b) b`. -/
public theorem telescope_aux (z : ℍ) (m : ℤ) (b : ℕ) :
  ∑ n ∈ Finset.Ico (-b : ℤ) b, (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) =
    1 / (↑m * ↑z - ↑b) - 1 / (↑m * ↑z + ↑b) := by
  -- telescoping on `ℤ` (Mathlib)
  convert Finset.sum_Ico_int_sub b (fun n : ℤ ↦ 1 / ((m : ℂ) * (z : ℂ) + n)) using 2
  · simp [sub_eq_add_neg, add_assoc]
  · simp [sub_eq_add_neg]

/-- The sequence `d ↦ 1 / (b * z + d)` tends to `0` as `d → ∞`. -/
public theorem tendstozero_inv_linear (z : ℍ) (b : ℤ) :
  Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z + ↑d)) atTop (𝓝 0) := by
  simpa using EisensteinSeries.tendsto_zero_inv_linear (z := (z : ℂ)) b

/-- The sequence `d ↦ 1 / (b * z - d)` tends to `0` as `d → ∞`. -/
public theorem tendstozero_inv_linear_neg (z : ℍ) (b : ℤ) :
  Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z - ↑d)) atTop (𝓝 0) := by
  simpa using EisensteinSeries.tendsto_zero_inv_linear_sub (z := (z : ℂ)) b


/-- A Cauchy-sequence statement for telescoping sums over `Ico (-N) N`. -/
public theorem extracted_3 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)) := by
  conv =>
      enter [1]
      intro d
      rw [telescope_aux ]
  apply Filter.Tendsto.cauchySeq (x := 0)
  have h1 : Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z - ↑d)) atTop (𝓝 0) :=
    tendstozero_inv_linear_neg z b
  have h2 : Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z + ↑d)) atTop (𝓝 0) :=
    tendstozero_inv_linear z b
  have := Filter.Tendsto.sub h1 h2
  simpa using this

/-- A Cauchy-sequence statement for the series `∑ (b * z + n)⁻²` over symmetric intervals. -/
public theorem extracted_4 (z : ℍ) (b : ℤ) :
  CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' x : ℤ, (((b : ℂ) * (z : ℂ) + x) ^ 2)⁻¹)
  have ht := (G2_summable_aux b z 2 (by rfl)).hasSum.comp Finset.tendsto_Ico_neg
  simpa using ht

theorem extracted_5 (z : ℍ) (b : ℤ) :
  CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z - ↑n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' x : ℤ, (((b : ℂ) * (z : ℂ) - x) ^ 2)⁻¹)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, one_div] using
    (summable_neg _ (G2_summable_aux b z 2 (by rfl))).hasSum.comp Finset.tendsto_Ico_neg

public lemma CauchySeq.congr (f g : ℕ → ℂ) (hf : f = g) (hh : CauchySeq g) : CauchySeq f := by
  simpa [hf] using hh

/-- If `f` is a Cauchy sequence, then `c • f` is also a Cauchy sequence. -/
public lemma cauchy_seq_mul_const (f : ℕ → ℂ) (c : ℂ) :
    CauchySeq f → CauchySeq (c • f) := by
  intro hf
  simpa [Function.comp] using
    (UniformContinuous.comp_cauchySeq (uniformContinuous_const_smul c) hf)

lemma auxer (a c : ℂ) : a + 2*2*c - 2*c = a + 2*c := by ring

noncomputable def summable_term (z : ℍ) : ℤ → ℂ :=
  (fun m : ℤ => (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

lemma term_evem (z : ℍ) (m : ℤ) : summable_term z m = summable_term z (-m) := by
  dsimp [summable_term]
  nth_rw 2 [int_sum_neg]
  refine tsum_congr fun n => by
    simp [Int.cast_neg]; ring_nf

/-- An identity rewriting a symmetric sum of `summable_term` as an even part plus a correction. -/
public lemma t8 (z : ℍ) :
  (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2))) =
  (fun _ : ℕ => 2*((riemannZeta 2))) +
  (fun N : ℕ => ∑ m ∈ Finset.range (N), 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) := by
  funext m
  simp only [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one,
    Nat.cast_one, div_one, pow_one, Pi.add_apply]
  have hsum :
      (∑ x ∈ Finset.Icc (-m : ℤ) m, summable_term z x) =
        2 * ∑ x ∈ Finset.range (m + 1), summable_term z x - summable_term z 0 := by
    simpa [two_nsmul, sub_eq_add_neg, two_mul, nsmul_eq_mul] using
      (Finset.sum_Icc_of_even_eq_range (f := summable_term z)
        (fun n => (term_evem (z := z) (m := n)).symm)
        m)
  -- Put the sum into the canonical `summable_term` form, then apply the even-sum identity.
  change (∑ x ∈ Finset.Icc (-m : ℤ) m, summable_term z x) = _
  rw [hsum]
  simp only [summable_term, one_div]
  have hz0 :
      (∑' (n : ℤ), ((((0 : ℤ) : ℂ) * (z : ℂ) + (n : ℂ)) ^ 2)⁻¹) = ∑' (n : ℤ), ((n : ℂ) ^ 2)⁻¹ := by
    simp only [Int.cast_zero, zero_mul, zero_add]
  rw [hz0]
  rw [zeta_two_eqn]
  nth_rw 2 [add_comm]
  have := sum_range_zero (fun m : ℤ => (∑' (n : ℤ), (((m : ℂ) * z + n) ^ 2)⁻¹)) m
  rw [this, hz0, zeta_two_eqn, add_comm, mul_add, ← mul_assoc, auxer]
  congr
  rw [Finset.mul_sum]
  congr
  ext d
  let Z : ℍ := ⟨((d : ℤ) + 1) * z, by
    have hd : (0 : ℝ) < ((d : ℤ) + 1 : ℝ) := by exact_mod_cast Nat.succ_pos d
    simpa [mul_im, intCast_re, intCast_im, coe_re, coe_im, zero_mul, add_zero] using mul_pos hd z.2⟩
  have := q_exp_iden 2 (by rfl) (z := Z)
  simp only [one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one,
    Nat.factorial_one, Nat.cast_one, div_one, pow_one, Z] at *
  simp only [Int.cast_add, Int.cast_one]
  rw [this]
  ring_nf
  congr
  ext r
  congr 1
  congr 1
  simp only [Int.cast_natCast]
  ring_nf

/-- A tendsto statement for the auxiliary `G2_c` series after rewriting with `t9`. -/
public theorem G2_c_tendsto (z : ℍ) :
  Tendsto
    (fun N ↦
      ∑ x ∈ Finset.range N,
        2 * (2 * ↑π * Complex.I) ^ 2 * ∑' (n : ℕ+), ↑↑n * cexp (2 * ↑π * Complex.I * (↑x + 1) * ↑z *
          ↑↑n))
    atTop (𝓝 (-8 * ↑π ^ 2 * ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) := by
    rw [← t9]
    have hf : Summable fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
        ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) := by
        conv =>
          enter [1]
          ext m
          rw [show (m : ℂ) + 1 = (((m + 1) : ℕ) : ℂ) by simp]
        have := nat_pos_tsum2' (f := fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
        ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m) * z * n)) )
        rw [← this]
        have := (a4 2 z).prod_symm.prod
        apply Summable.mul_left
        apply this.congr
        intro b
        rfl
    have := hf.hasSum
    have V := this.comp tendsto_finset_range
    simpa [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one,
      Nat.cast_one, div_one, pow_one] using V

/-- Cauchy convergence of the symmetric partial sums defining the `G2_c` series. -/
public lemma G2_cauchy (z : ℍ) :
    CauchySeq (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))
    := by
  rw [t8]
  simp only [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one,
    Nat.cast_one, div_one, pow_one]
  refine CauchySeq.const_add ?_
  exact (G2_c_tendsto z).cauchySeq
