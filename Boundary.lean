import FloorPowers

namespace FloorPowers
open Finset

private def mass (a : ℕ → ℕ) (n : ℕ) := (range n).sum a

private theorem mass_succ (a : ℕ → ℕ) (n : ℕ) : mass a (n+1) = mass a n + a n :=
  sum_range_succ ..

private theorem sum_le_mass {a : ℕ → ℕ} {n m : ℕ}
    (hr : Represents (initial a n : Set ℕ) m) : m ≤ mass a n := by
  obtain ⟨s, hs, rfl⟩ := hr
  calc
    s.sum id ≤ (initial a n).sum id := sum_le_sum_of_subset (fun x hx ↦ hs x hx)
    _ ≤ _ := sum_image_le_of_nonneg (fun _ _ ↦ Nat.zero_le _)

/-- For at-least-doubling sequences, one gap below a new term forces arbitrarily late gaps. -/
private theorem no_gap {a : ℕ → ℕ} (hc : Complete a) (ha : Monotone a)
    (hd : ∀ i, 2*a i ≤ a (i+1)) (hu : ∀ n m, ∃ k ≥ n, m < a k) (j : ℕ) :
    a j ≤ mass a j + 1 := by
  by_contra! hg
  have persist : ∀ k ≥ j, mass a k + 1 < a k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hg
    | succ i hi ih => rw [mass_succ]; have := hd i; omega
  obtain ⟨u, hrep⟩ := hc
  obtain ⟨k, hk, hbig⟩ := hu j u
  have tooLarge := sum_le_mass (localize ha (persist (k+1) (by omega))
    (hrep (mass a (k+1)+1) (by rw [mass_succ]; omega)))
  omega

/-- A complete sequence that at least doubles at every step consists of zeroes followed
by the binary powers. -/
theorem binary_rigidity {a : ℕ → ℕ} (hc : Complete a) (ha : Monotone a)
    (hd : ∀ i, 2*a i ≤ a (i+1)) (hu : ∀ n m, ∃ k ≥ n, m < a k) :
    ∃ j : ℕ, (∀ i < j, a i = 0) ∧ ∀ l : ℕ, a (j+l) = 2^l := by
  classical
  have hex : ∃ i, 0 < a i := by obtain ⟨i, _, hi⟩ := hu 0 0; exact ⟨i, hi⟩
  let j := Nat.find hex
  have hj : 0 < a j := Nat.find_spec hex
  have hprev : ∀ i < j, a i = 0 := fun i hi ↦ Nat.eq_zero_of_not_pos (Nat.find_min hex hi)
  have emptyMass : mass a j = 0 := sum_eq_zero (fun i hi ↦ hprev i (mem_range.mp hi))
  have safe := no_gap hc ha hd hu
  have hbinary : ∀ l : ℕ, a (j+l) = 2^l ∧ a (j+l) = mass a (j+l) + 1 := by
    intro l
    induction l with
    | zero => have := safe j; simp; omega
    | succ l ih =>
      change a ((j+l)+1) = 2^(l+1) ∧ a ((j+l)+1) = mass a ((j+l)+1) + 1
      have h₁ := safe ((j+l)+1)
      have h₂ := hd (j+l)
      rw [mass_succ] at h₁ ⊢
      rw [pow_succ]
      omega
  exact ⟨j, hprev, fun l ↦ (hbinary l).1⟩

theorem floor_doubles {t α : ℝ} (ht : 0 < t) (hα : 2 ≤ α) (n : ℕ) :
    2 * terms t α n ≤ terms t α (n+1) := by
  let x := t*α^n
  have hx : 0 ≤ x := by dsimp [x]; positivity
  apply Nat.le_floor
  simp only [terms, Nat.cast_mul, Nat.cast_ofNat, pow_succ, ← mul_assoc]
  change 2*(⌊x⌋₊:ℝ) ≤ x*α
  linarith [Nat.floor_le hx, mul_le_mul_of_nonneg_left hα hx]

private theorem binary_complete : Complete (fun n : ℕ ↦ 2^n) := by
  apply complete_of_block (n := 0) (u := 0)
  · intro j _ i hi
    exact pow_lt_pow_right₀ (by decide : (1:ℕ) < 2) hi
  · intro j _; simp [pow_succ, Nat.mul_comm]
  · intro m
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt m (by decide : (1:ℕ) < 2)
    exact ⟨k, by omega, hk⟩
  · intro m _ hm
    simp only [pow_zero, zero_add] at hm
    exact ⟨∅, by simp, by simp; omega⟩

/-- This characterizes all positive real coefficients at the boundary base two. -/
theorem complete_base_two_iff {t : ℝ} (ht : 0 < t) :
    Complete (terms t 2) ↔ ∃ j : ℕ, t = 1/2^j := by
  constructor
  · intro hc
    obtain ⟨j, _, h⟩ := binary_rigidity hc (terms_mono ht (by norm_num))
      (floor_doubles ht le_rfl) (terms_unbounded ht (by norm_num))
    let x := t*2^j
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have bounds (l : ℕ) : (2:ℝ)^l ≤ x*2^l ∧ x*2^l < 2^l+1 := by
      have hl := h l
      rw [terms, pow_add, ← mul_assoc] at hl
      change ⌊x*2^l⌋₊ = 2^l at hl
      have hfloor := (Nat.floor_eq_iff (by positivity : 0 ≤ x*(2:ℝ)^l)).mp hl
      simpa using hfloor
    have hx₁ : 1 ≤ x := by simpa using (bounds 0).1
    have hx₂ : x ≤ 1 := by
      by_contra! hgt
      obtain ⟨l, hl⟩ := pow_unbounded_of_one_lt (1/(x-1)) (by norm_num : (1:ℝ) < 2)
      have := (div_lt_iff₀ (by linarith : 0 < x-1)).mp hl
      nlinarith [(bounds l).2]
    exact ⟨j, (eq_div_iff (by positivity)).mpr (le_antisymm hx₂ hx₁)⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨u, hu⟩ := binary_complete
    refine ⟨u, fun m hm ↦ represents_mono ?_ (hu m hm)⟩
    rintro _ ⟨l,rfl⟩
    refine ⟨j+l, ?_⟩
    simp [terms, pow_add, ne_of_gt (show 0 < (2:ℝ)^j by positivity)]
    exact_mod_cast Nat.floor_natCast (R := ℝ) ((2:ℕ)^l)

theorem incomplete_above_two {t α : ℝ} (ht : 0 < t) (hα : 2 < α) : ¬ Complete (terms t α) := by
  intro hc
  have h₁ : 1 < α := by linarith
  obtain ⟨j, _, hb⟩ := binary_rigidity hc (terms_mono ht h₁)
    (floor_doubles ht hα.le) (terms_unbounded ht h₁)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2/(t*(α-2))) h₁
  have hpos : 0 < t*(α-2) := mul_pos ht (by linarith)
  have hg : 2 < α^(j+k) * (t*(α-2)) :=
    ((div_lt_iff₀ hpos).mp hk).trans_le (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ h₁.le (show k ≤ j+k by omega)) hpos.le)
  let x := t*α^(j+k)
  have h₀ := Nat.floor_le (show 0 ≤ x by dsimp [x]; positivity)
  have h₁' := Nat.lt_floor_add_one (x*α)
  have h₂ := hb k
  have h₃ := hb (k+1)
  change ⌊x⌋₊ = 2^k at h₂
  rw [← Nat.add_assoc, terms, pow_succ, ← mul_assoc] at h₃
  change ⌊x*α⌋₊ = 2^(k+1) at h₃
  have hstep : (⌊x*α⌋₊:ℝ) = 2 * (⌊x⌋₊:ℝ) := by rw [h₂,h₃,pow_succ]; push_cast; ring
  have hgap : 2 < x*(α-2) := by dsimp [x]; linarith only [hg, mul_left_comm (α^(j+k)) t (α-2), mul_assoc t (α^(j+k)) (α-2)]
  nlinarith

theorem incomplete_at_most_one {t α : ℝ} (ht : 0 < t) (hα₀ : 0 < α) (hα : α ≤ 1) :
    ¬ Complete (terms t α) := by
  rintro ⟨u, hu⟩
  let s := range (⌊t⌋₊+1)
  obtain ⟨q, hq, he⟩ := hu (s.sum id + u + 1) (by omega)
  have hsub : q ⊆ s := by
    intro x hx
    obtain ⟨i,rfl⟩ := hq x hx
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hα₀.le hα (n := i)) ht.le)))
  have hbound : q.sum id ≤ s.sum id := sum_le_sum_of_subset hsub
  rw [he] at hbound
  omega

#print axioms complete_base_two_iff
#print axioms incomplete_above_two

end FloorPowers
