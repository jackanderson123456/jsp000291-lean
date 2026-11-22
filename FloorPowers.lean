import Mathlib

/-! A finite interval criterion for additive completeness of exponential floor sequences. -/

namespace FloorPowers

open Finset

/-- Subsets consist of values. Equal terms at distinct indices cannot be reused. -/
def Represents (S : Set ℕ) (m : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ S) ∧ s.sum id = m

def Complete (a : ℕ → ℕ) : Prop :=
  ∃ u : ℕ, ∀ m ≥ u, Represents (Set.range a) m

def initial (a : ℕ → ℕ) (n : ℕ) : Finset ℕ := (range n).image a

def Block (a : ℕ → ℕ) (n u : ℕ) : Prop :=
  ∀ m, u ≤ m → m < u + a n → Represents (initial a n : Set ℕ) m

private theorem initial_mono {a : ℕ → ℕ} {n k : ℕ} (hn : n ≤ k) :
    initial a n ⊆ initial a k :=
  Finset.image_subset_image (Finset.range_mono hn)

theorem represents_mono {S T : Set ℕ} {m : ℕ} (h : S ⊆ T) :
    Represents S m → Represents T m := by
  rintro ⟨s, hs, he⟩
  exact ⟨s, fun x hx ↦ h (hs x hx), he⟩

theorem localize {a : ℕ → ℕ} (ha : Monotone a) {n m : ℕ} (hm : m < a n)
    (hr : Represents (Set.range a) m) : Represents (initial a n : Set ℕ) m := by
  obtain ⟨s, hs, hsum⟩ := hr
  refine ⟨s, ?_, hsum⟩
  intro x hx
  obtain ⟨i, rfl⟩ := hs x hx
  have hle : a i ≤ m := hsum ▸ Finset.single_le_sum (f := id) (fun _ _ ↦ Nat.zero_le _) hx
  exact mem_image.mpr ⟨i, mem_range.mpr (lt_of_not_ge (fun h ↦ (ha h).not_gt (hle.trans_lt hm))), rfl⟩

private theorem extend {a : ℕ → ℕ} {n m : ℕ} (hfresh : ∀ i < n, a i < a n)
    (hr : Represents (initial a n : Set ℕ) m) :
    Represents (initial a (n+1) : Set ℕ) (a n + m) := by
  obtain ⟨s, hs, he⟩ := hr
  have hn : a n ∉ s := by
    intro h
    obtain ⟨i, hi, hval⟩ := mem_image.mp (hs _ h)
    exact (hfresh i (mem_range.mp hi)).ne hval
  refine ⟨insert (a n) s, ?_, by rw [sum_insert hn, he]; rfl⟩
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact mem_image.mpr ⟨n, mem_range.mpr (by omega), rfl⟩
  · exact initial_mono (Nat.le_succ n) (hs _ hx)

private theorem propagate {a : ℕ → ℕ} {n u : ℕ} (hfresh : ∀ i < n, a i < a n)
    (hd : a (n+1) ≤ 2 * a n) (hb : Block a n u) : Block a (n+1) u := by
  intro m h₁ h₂
  by_cases hm : m < u + a n
  · exact represents_mono (initial_mono (Nat.le_succ n)) (hb _ h₁ hm)
  · have hr := extend hfresh (hb (m - a n) (by omega) (by omega))
    rwa [Nat.add_sub_of_le (show a n ≤ m by omega)] at hr

/-- A finite interval propagates forever once each new term is fresh and at most doubles. -/
theorem complete_of_block {a : ℕ → ℕ} {n u : ℕ}
    (hnew : ∀ j ≥ n, ∀ i < j, a i < a j)
    (hd : ∀ j ≥ n, a (j+1) ≤ 2 * a j)
    (hunb : ∀ m, ∃ k ≥ n, m < a k) (hb : Block a n u) : Complete a := by
  have allBlocks : ∀ k ≥ n, Block a k u := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hb
    | succ j hj ih => exact propagate (hnew j hj) (hd j hj) ih
  refine ⟨u, fun m hm ↦ ?_⟩
  obtain ⟨k, hk, hlarge⟩ := hunb m
  refine represents_mono ?_ (allBlocks k hk m hm (by omega))
  intro x hx
  obtain ⟨i, _, rfl⟩ := mem_image.mp hx
  exact ⟨i, rfl⟩

/-- Eventual completeness produces an interval witness as soon as the two adjacent
lengths have sufficient room on each side. -/
theorem block_of_complete {a : ℕ → ℕ} (ha : Monotone a) {u k : ℕ}
    (hc : ∀ m ≥ u, Represents (Set.range a) m) (hfresh : ∀ i < k, a i < a k)
    (hg : a k + u ≤ a (k+1)) (hd : a (k+1) + u ≤ 2 * a k) : Block a (k+1) u := by
  intro m h₁ h₂
  by_cases hm : m < a (k+1)
  · exact localize ha hm (hc _ h₁)
  · have h₃ : u ≤ m - a k := by omega
    have hr := extend hfresh (localize ha (show m - a k < a k by omega) (hc _ h₃))
    rwa [Nat.add_sub_of_le (show a k ≤ m by omega)] at hr

noncomputable def terms (t α : ℝ) (n : ℕ) : ℕ := ⌊t * α^n⌋₊

/-- Two real inequalities at a single index control all subsequent floor errors. -/
def Margin (t α : ℝ) (n u : ℕ) : Prop :=
  (u:ℝ) + 2 ≤ t * α^n * (α-1) ∧ (u:ℝ) + 2 ≤ t * α^n * (2-α)

theorem margin_mono {t α : ℝ} (ht : 0 < t) (hα : 1 < α) (h₂ : α < 2)
    {i j u : ℕ} (hij : i ≤ j) (hm : Margin t α i u) : Margin t α j u := by
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hα.le hij) ht.le
  exact ⟨hm.1.trans (mul_le_mul_of_nonneg_right hp (by linarith)),
    hm.2.trans (mul_le_mul_of_nonneg_right hp (by linarith))⟩

theorem exists_margin {t α : ℝ} (ht : 0 < t) (hα : 1 < α) (h₂ : α < 2)
    (u : ℕ) : ∃ j, Margin t α j u := by
  let b := t * min (α-1) (2-α)
  have hb : 0 < b := mul_pos ht (lt_min (by linarith) (by linarith))
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (((u:ℝ)+2)/b) hα
  have h := ((div_lt_iff₀ hb).mp hj).le
  have hj' : 0 ≤ α^j * t := by positivity
  constructor
  case w => exact j
  change _ ≤ _ ∧ _ ≤ _
  dsimp [b] at h
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_left (α-1) (2-α)) hj']
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_right (α-1) (2-α)) hj']

theorem margin_steps {t α : ℝ} (ht : 0 < t) (hα : 1 < α) {i u : ℕ}
    (hm : Margin t α i u) :
    terms t α i + u < terms t α (i+1) ∧ terms t α (i+1) + u ≤ 2 * terms t α i := by
  let x := t * α^i
  have hpos : 0 ≤ x := by dsimp [x]; positivity
  have hpos' : 0 ≤ x*α := mul_nonneg hpos (by linarith)
  have h₀ := Nat.floor_le hpos
  have h₁ := Nat.lt_floor_add_one x
  have h₂ := Nat.floor_le hpos'
  have h₃ := Nat.lt_floor_add_one (x*α)
  change (u:ℝ) + 2 ≤ x*(α-1) ∧ (u:ℝ) + 2 ≤ x*(2-α) at hm
  rcases hm with ⟨hm, hm'⟩
  simp only [terms, pow_succ, ← mul_assoc]
  change ⌊x⌋₊ + u < ⌊x*α⌋₊ ∧ ⌊x*α⌋₊ + u ≤ 2 * ⌊x⌋₊
  constructor
  · exact_mod_cast (show (⌊x⌋₊:ℝ) + u < ⌊x*α⌋₊ by nlinarith)
  · exact_mod_cast (show (⌊x*α⌋₊:ℝ) + u ≤ 2 * ⌊x⌋₊ by nlinarith)

theorem terms_mono {t α : ℝ} (ht : 0 < t) (hα : 1 < α) : Monotone (terms t α) :=
  fun _ _ hij ↦ Nat.floor_mono (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hα.le hij) ht.le)

private theorem fresh_after {a : ℕ → ℕ} (ha : Monotone a) {j : ℕ} (hj : a j < a (j+1)) :
    ∀ i < j+1, a i < a (j+1) := fun i hi ↦ (ha (show i ≤ j by omega)).trans_lt hj

theorem terms_unbounded {t α : ℝ} (ht : 0 < t) (hα : 1 < α) (n m : ℕ) :
    ∃ k ≥ n, m < terms t α k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (((m:ℝ)+1)/t) hα
  have hm : m+1 ≤ terms t α k := Nat.le_floor (by
    push_cast
    linarith [((div_lt_iff₀ ht).mp hk), mul_comm (α^k) t])
  exact ⟨max n k, le_max_left .., (Nat.lt_of_succ_le hm).trans_le (terms_mono ht hα (le_max_right ..))⟩

/-- All arithmetic on the initial values in this test is finite. -/
def blockTest (a : ℕ → ℕ) (n u : ℕ) : Prop :=
  Ico u (u + a n) ⊆ (initial a n).powerset.image (fun s ↦ s.sum id)

theorem blockTest_iff (a : ℕ → ℕ) (n u : ℕ) : blockTest a n u ↔ Block a n u := by
  constructor
  · intro h m h₁ h₂
    obtain ⟨s, hs, he⟩ := mem_image.mp (h (mem_Ico.mpr ⟨h₁,h₂⟩))
    exact ⟨s, fun _ hx ↦ mem_powerset.mp hs hx, he⟩
  · intro h m hm
    obtain ⟨h₁,h₂⟩ := mem_Ico.mp hm
    obtain ⟨s, hs, he⟩ := h m h₁ h₂
    exact mem_image.mpr ⟨s, mem_powerset.mpr (fun _ hx ↦ hs _ hx), he⟩

/-- On the full open strip, completeness is equivalent to two explicit polynomial
inequalities and a subset-sum test on just one finite initial segment. -/
theorem complete_iff_finite_test {t α : ℝ} (ht : 0 < t) (hα : 1 < α) (h₂ : α < 2) :
    Complete (terms t α) ↔ ∃ k u : ℕ, Margin t α k 0 ∧ blockTest (terms t α) (k+1) u := by
  have mono := terms_mono ht hα
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨j, hj⟩ := exists_margin ht hα h₂ u
    have hk := margin_mono ht hα h₂ (Nat.le_succ j) hj
    have hstep := margin_steps ht hα hk
    have hprev := (margin_steps ht hα hj).1
    refine ⟨j+1, u, ⟨?_, ?_⟩, (blockTest_iff ..).mpr ?_⟩
    · exact le_trans (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) u]) hk.1
    · exact le_trans (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) u]) hk.2
    · exact block_of_complete mono hu (fresh_after mono (by omega)) hstep.1.le hstep.2
  · rintro ⟨k, u, hk, hb⟩
    refine complete_of_block (n := k+1) (u := u) ?_ ?_ (terms_unbounded ht hα _) ((blockTest_iff ..).mp hb)
    · intro j hj
      obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      exact fresh_after mono (by simpa using (margin_steps ht hα (margin_mono ht hα h₂ (show k ≤ l by omega) hk)).1)
    · intro j hj
      simpa using (margin_steps ht hα (margin_mono ht hα h₂ (show k ≤ j by omega) hk)).2

#print axioms complete_iff_finite_test

end FloorPowers
