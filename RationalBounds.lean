import Mathlib

namespace FloorPowers

/-- Rational enclosures used in the five-root example. -/
structure Bounds where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

namespace Bounds

def Contains (I : Bounds) (x : ℝ) := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (q : ℚ) : Bounds := ⟨q,q⟩
def add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : Bounds) : Bounds := ⟨a.lo - b.hi, a.hi - b.lo⟩
def mul (a b : Bounds) : Bounds :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

theorem point_mem (q : ℚ) : (point q).Contains q := ⟨le_rfl,le_rfl⟩

theorem add_mem {a b : Bounds} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := by
  simpa [Contains,add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem sub_mem {a b : Bounds} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.sub b).Contains (x-y) := by
  simpa [Contains,sub] using And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

private theorem linear_bounds {a b x r L U : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (h₁ : L ≤ a*r ∧ a*r ≤ U) (h₂ : L ≤ b*r ∧ b*r ≤ U) : L ≤ x*r ∧ x*r ≤ U := by
  rcases le_total 0 r with hr | hr
  · exact ⟨h₁.1.trans (mul_le_mul_of_nonneg_right ha hr), (mul_le_mul_of_nonneg_right hb hr).trans h₂.2⟩
  · exact ⟨h₂.1.trans (mul_le_mul_of_nonpos_right hb hr), (mul_le_mul_of_nonpos_right ha hr).trans h₁.2⟩

theorem mul_mem {a b : Bounds} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := by
  apply linear_bounds hx.1 hx.2
  all_goals
    rw [mul_comm _ y]
    apply linear_bounds hy.1 hy.2
    all_goals
      rw [mul_comm]
      simp only [mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul, min_le_iff, le_max_iff]
      simp

/-- If numerator and denominator have rational bounds, the quotient is bounded
by cross multiplication; all endpoint tests are rational. -/
def QuotientBounds (a b c : Bounds) : Prop :=
  (0 < b.lo ∧ (mul (point c.lo) b).hi ≤ a.lo ∧ a.hi ≤ (mul (point c.hi) b).lo) ∨
  (b.hi < 0 ∧ (mul (point c.hi) b).hi ≤ a.lo ∧ a.hi ≤ (mul (point c.lo) b).lo)

instance (a b c : Bounds) : Decidable (QuotientBounds a b c) := by
  unfold QuotientBounds
  infer_instance

theorem quotient_mem {a b c : Bounds} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hq : QuotientBounds a b c) : c.Contains (x/y) := by
  have hl := mul_mem (point_mem c.lo) hy
  have hu := mul_mem (point_mem c.hi) hy
  rcases hq with ⟨hb,h₁,h₂⟩ | ⟨hb,h₁,h₂⟩
  · have hy' : 0 < y := lt_of_lt_of_le (by exact_mod_cast hb) hy.1
    exact ⟨(le_div_iff₀ hy').mpr ((hl.2.trans (by exact_mod_cast h₁)).trans hx.1),
      (div_le_iff₀ hy').mpr ((hx.2.trans (by exact_mod_cast h₂)).trans hu.1)⟩
  · have hy' : y < 0 := lt_of_le_of_lt hy.2 (by exact_mod_cast hb)
    exact ⟨(le_div_iff_of_neg hy').mpr ((hx.2.trans (by exact_mod_cast h₂)).trans hl.1),
      (div_le_iff_of_neg hy').mpr ((hu.2.trans (by exact_mod_cast h₁)).trans hx.1)⟩

end Bounds
end FloorPowers
