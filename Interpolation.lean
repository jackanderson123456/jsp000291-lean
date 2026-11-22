import Mathlib

namespace FloorPowers.Example

open Polynomial Finset
open scoped Polynomial

def q (x : ℝ) := x^5-6*x^3-x^2+7*x+1
def h (x : ℝ) := (((2*x+4)*x-2)*x-6)*x-1

private noncomputable def Q : ℤ[X] := X^5-6*X^3-X^2+7*X+1
private noncomputable def H : ℤ[X] := (((2*X+4)*X-2)*X-6)*X-1

def num (y : Fin 5 → ℝ) (i : Fin 5) := h (y i) * ∏ j ∈ univ.erase i, (2-y j)
def den (y : Fin 5 → ℝ) (i : Fin 5) := ∏ j ∈ univ.erase i, (y i-y j)
noncomputable def weight (y : Fin 5 → ℝ) (i : Fin 5) := num y i / den y i

private theorem weight_basis (y : Fin 5 → ℝ) (i : Fin 5) :
    weight y i = h (y i) * (Lagrange.basis univ y i).eval 2 := by
  simp only [weight, num, den, Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul,
    eval_C, eval_sub, eval_X]
  rw [mul_div_assoc, ← prod_div_distrib]
  congr 1
  apply prod_congr rfl
  intro j _
  rw [div_eq_mul_inv, mul_comm]

/-- The weighted sum is an integer congruent to one modulo five, for every exponent. -/
theorem integer_trace {y : Fin 5 → ℝ} (hinj : Function.Injective y) (hy : ∀ i, q (y i) = 0)
    (n : ℕ) : ∃ z : ℤ, (5*z+1 : ℝ) =
      ∑ i, weight y i * (Chebyshev.C ℝ (n:ℤ)).eval (y i) := by
  classical
  let p := H * Chebyshev.C ℤ (n:ℤ)
  let r := p %ₘ Q
  have hQ : Q.Monic := by unfold Q; monicity!
  have degQ : Q.degree = 5 := by unfold Q; compute_degree!
  have hq₂ : Q.eval 2 = -5 := by norm_num [Q]
  have hh₂ : H.eval 2 = 43 := by norm_num [H]
  have hp : p.eval 2 = 86 := by simp [p,hh₂,Chebyshev.C_eval_two]
  have hr := congrArg (eval (2:ℤ)) (modByMonic_add_div p Q)
  change (r+Q*(p /ₘ Q)).eval 2 = _ at hr
  rw [eval_add, eval_mul, hq₂, hp] at hr
  let z := (p /ₘ Q).eval 2 + 17
  have hz : r.eval 2 = 5*z+1 := by dsimp [z]; omega
  let f := r.map (Int.castRingHom ℝ)
  have hdeg : f.degree < (#(univ : Finset (Fin 5)) : WithBot ℕ) := by
    simpa [degQ] using degree_map_le.trans_lt (degree_modByMonic_lt p hQ (R := ℤ))
  have hroot (i : Fin 5) : aeval (y i) Q = 0 := by simpa [Q,q,map_ofNat] using hy i
  have hf (i : Fin 5) : f.eval (y i) = h (y i)*(Chebyshev.C ℝ (n:ℤ)).eval (y i) := by
    rw [show f = r.map (Int.castRingHom ℝ) from rfl,eval_map]
    change aeval (y i) r = _
    rw [show r = p %ₘ Q from rfl, aeval_modByMonic_eq_self_of_root (hroot i)]
    simp [p,H,h,map_ofNat]
  have eqn := congrArg (eval (2:ℝ)) (Lagrange.eq_interpolate (s := univ) hinj.injOn hdeg)
  rw [Lagrange.interpolate_apply,eval_finsetSum] at eqn
  refine ⟨z, ?_⟩
  calc
    (5*(z:ℝ)+1) = (r.eval 2 : ℤ) := by exact_mod_cast hz.symm
    _ = f.eval 2 := by
      simpa [f] using (eval_map_apply (p := r) (Int.castRingHom ℝ) (2:ℤ)).symm
    _ = _ := eqn.trans (sum_congr rfl (fun i _ ↦ by
      rw [eval_mul,eval_C,hf, weight_basis]; ring))

theorem stable_bound {y : ℝ} (hy : |y| ≤ 2) (n : ℕ) :
    |(Chebyshev.C ℝ (n:ℤ)).eval y| ≤ 2 := by
  have h := abs_le.mp hy
  let θ := Real.arccos (y/2)
  have he : 2*Real.cos θ = y := by
    dsimp [θ]
    rw [Real.cos_arccos (by linarith) (by linarith)]
    ring
  rw [← he,Chebyshev.C_two_mul_real_cos,abs_mul]
  simpa using mul_le_mul_of_nonneg_left (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
    (by norm_num : (0:ℝ) ≤ 2)

theorem outside_value {α : ℝ} (ha : 0 < α) (n : ℕ) :
    (Chebyshev.C ℝ (n:ℤ)).eval (α+α⁻¹) = α^n + (α⁻¹)^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp
  | more n h₀ h₁ =>
    have hr := Chebyshev.C_add_two ℝ (n:ℤ)
    push_cast at *
    rw [hr,eval_sub,eval_mul,eval_X,h₁,h₀]
    have hn : α*α⁻¹=1 := mul_inv_cancel₀ ha.ne'
    rw [pow_succ, pow_succ, pow_succ, pow_succ]
    linear_combination (α^n + (α⁻¹)^n) * hn

end FloorPowers.Example
