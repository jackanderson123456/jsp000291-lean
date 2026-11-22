import Nodes
import ParameterSet

namespace FloorPowers.Example
open Polynomial Finset

private theorem base_exists : ∃ α : ℝ, 159/100 ≤ α ∧ α ≤ 8/5 ∧ node 4 = α+α⁻¹ := by
  obtain ⟨hl,hu⟩ := node_mem 4
  change ((2223177/1000000 : ℚ):ℝ) ≤ node 4 at hl
  change node 4 ≤ (((2223177+1)/1000000 : ℚ):ℝ) at hu
  norm_num at hl hu
  let f (x : ℝ) := x^2-node 4*x+1
  have signs : f (159/100) ≤ 0 ∧ 0 ≤ f (8/5) := by dsimp [f]; constructor <;> linarith
  obtain ⟨α, hα, hz⟩ := intermediate_value_Icc (by norm_num : (159/100:ℝ) ≤ 8/5)
    (show ContinuousOn f _ from (by unfold f; fun_prop : Continuous f).continuousOn) signs
  have hpos : 0 < α := lt_of_lt_of_le (by norm_num) hα.1
  refine ⟨α, hα.1, hα.2, ?_⟩
  dsimp [f] at hz
  field_simp
  nlinarith

noncomputable def base : ℝ := Classical.choose base_exists
noncomputable def coefficient : ℝ := (2/5) * weight node 4 * base^12

theorem base_bounds : 159/100 ≤ base ∧ base ≤ 8/5 ∧ node 4 = base+base⁻¹ :=
  Classical.choose_spec base_exists

theorem base_in_range : 1 < base ∧ base < (1+Real.sqrt 5)/2 := by
  obtain ⟨h₁,h₂,_⟩ := base_bounds
  have hroot := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hpos := Real.sqrt_nonneg 5
  have : 11/5 < Real.sqrt 5 := by nlinarith
  constructor <;> linarith

theorem coefficient_pos : 0 < coefficient := by
  have := large_weight.1
  have hb : 0 < base := by linarith [base_in_range.1]
  unfold coefficient
  positivity

private theorem small_nodes (i : Fin 5) (hi : i < 4) : |node i| ≤ 2 := by
  obtain ⟨hl,hu⟩ := node_mem i
  have hs : ∀ j : Fin 5, j < 4 → -2 ≤ (box j).lo ∧ (box j).hi ≤ 2 := by decide +kernel
  have h := hs i hi
  apply abs_le.mpr
  exact ⟨le_trans (by exact_mod_cast h.1) hl,hu.trans (by exact_mod_cast h.2)⟩

private theorem small_contribution (k : ℕ) :
    |weight node 0 * (Chebyshev.C ℝ (k:ℤ)).eval (node 0) +
     weight node 1 * (Chebyshev.C ℝ (k:ℤ)).eval (node 1) +
     weight node 2 * (Chebyshev.C ℝ (k:ℤ)).eval (node 2) +
     weight node 3 * (Chebyshev.C ℝ (k:ℤ)).eval (node 3)| ≤ 81/100 := by
  let a (i : Fin 5) := weight node i * (Chebyshev.C ℝ (k:ℤ)).eval (node i)
  have bound (i : Fin 5) (hi : i < 4) : |a i| ≤ |weight node i| * 2 := by
    unfold a
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (stable_bound (small_nodes i hi) k) (abs_nonneg _)
  change |a 0 + a 1 + a 2 + a 3| ≤ _
  linarith [abs_add_le (a 0) (a 1), abs_add_le (a 0 + a 1) (a 2),
    abs_add_le (a 0 + a 1 + a 2) (a 3), bound 0 (by decide), bound 1 (by decide),
    bound 2 (by decide), bound 3 (by decide), weights_small]

private theorem mirror_bound (n : ℕ) : 0 ≤ weight node 4 * (base⁻¹)^(n+12) ∧
    weight node 4 * (base⁻¹)^(n+12) < 19/100 := by
  have hb := base_bounds.1
  have h₁ := base_in_range.1
  have hw := large_weight
  have pos : 0 < base := by linarith
  have hp : (159/100:ℝ)^12 ≤ base^(n+12) :=
    (pow_le_pow_left₀ (by norm_num) hb 12).trans (pow_le_pow_right₀ h₁.le (by omega))
  rw [inv_pow, ← div_eq_mul_inv]
  constructor
  · exact div_nonneg (by linarith) (pow_nonneg pos.le _)
  · apply (div_lt_iff₀ (pow_pos pos _)).mpr
    norm_num at hp
    linarith

/-- The algebraically specified floor sequence consists entirely of even integers. -/
theorem every_floor_even (n : ℕ) : Even ⌊coefficient * base^n⌋ := by
  let k := n+12
  obtain ⟨z,hz⟩ := integer_trace node_injective node_root k
  rw [Fin.sum_univ_five,base_bounds.2.2,outside_value (by linarith [base_in_range.1])] at hz
  have hs := abs_le.mp (small_contribution k)
  have hm := mirror_bound n
  change 0 ≤ weight node 4 * (base⁻¹)^k ∧ weight node 4 * (base⁻¹)^k < 19/100 at hm
  have approx : (5*z:ℝ) < weight node 4 * base^k ∧ weight node 4 * base^k < 5*z+2 := by
    constructor <;> linarith [hz,hs.1,hs.2,hm.1,hm.2,mul_add (weight node 4) (base^k) ((base⁻¹)^k)]
  refine ⟨z, Int.floor_eq_iff.mpr ?_⟩
  have hproduct : coefficient * base^n = (2/5)*(weight node 4 * base^k) := by
    dsimp [coefficient,k]
    rw [pow_add]
    ring
  rw [hproduct]
  push_cast
  constructor <;> linarith [approx.1,approx.2]

theorem incomplete_example : ¬ Complete (terms coefficient base) := by
  have he (n : ℕ) : Even (terms coefficient base n) := by
    have hp : 0 ≤ coefficient * base^n := mul_nonneg coefficient_pos.le
      (pow_nonneg (by linarith [base_in_range.1]) n)
    obtain ⟨z,hz⟩ := every_floor_even n
    rw [← Int.natCast_floor_eq_floor hp] at hz
    refine ⟨z.toNat, ?_⟩
    unfold terms
    omega
  rintro ⟨u, hu⟩
  obtain ⟨s,hs,ht⟩ := hu (2*u+1) (by omega)
  have evenSum : Even (s.sum id) := by
    apply even_iff_two_dvd.mpr
    apply Finset.dvd_sum
    intro x hx
    obtain ⟨n,rfl⟩ := hs x hx
    exact even_iff_two_dvd.mp (he n)
  obtain ⟨z,hz⟩ := evenSum
  omega

theorem golden_ratio_conjecture_false :
    ∃ t α : ℝ, 0 < t ∧ 1 < α ∧ α < (1+Real.sqrt 5)/2 ∧ ¬ Complete (terms t α) :=
  ⟨coefficient,base,coefficient_pos,base_in_range.1,base_in_range.2,incomplete_example⟩

#print axioms every_floor_even
#print axioms golden_ratio_conjecture_false

end FloorPowers.Example
