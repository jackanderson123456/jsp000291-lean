import Counterexample

namespace FloorPowers
open Finset Filter

/-- The integer and filter formulation in Formal Conjectures, Erdős problem 349. -/
def GoodPair (t α : ℝ) : Prop :=
  ∀ᶠ k : ℤ in atTop, ∃ B : Finset ℤ, (B : Set ℤ) ⊆ Set.range (fun n : ℕ ↦ ⌊t*α^n⌋) ∧
    k = ∑ i ∈ B, i

private theorem cast_represented (a : ℕ → ℕ) (m : ℕ) :
    (∃ s : Finset ℤ, (s : Set ℤ) ⊆ Set.range (fun n ↦ (a n : ℤ)) ∧ (m : ℤ) = s.sum id) ↔
    Represents (Set.range a) m := by
  constructor
  · rintro ⟨s, hs, hm⟩
    have nonneg {x : ℤ} (hx : x ∈ s) : 0 ≤ x := by obtain ⟨i,rfl⟩ := hs hx; exact Int.natCast_nonneg _
    refine ⟨s.image Int.toNat, ?_, ?_⟩
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      obtain ⟨i,rfl⟩ := hs hz
      exact ⟨i, by simp⟩
    · rw [sum_image (fun x hx y hy h ↦ by
        have e := congrArg (fun k : ℕ ↦ (k:ℤ)) h
        simpa [Int.toNat_of_nonneg (nonneg hx),Int.toNat_of_nonneg (nonneg hy)] using e)]
      apply Nat.cast_injective (R := ℤ)
      push_cast
      exact (sum_congr rfl (fun x hx ↦ Int.toNat_of_nonneg (nonneg hx))).trans hm.symm
  · rintro ⟨s,hs,hm⟩
    refine ⟨s.image (fun x : ℕ ↦ (x:ℤ)), ?_, ?_⟩
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      obtain ⟨j,rfl⟩ := hs i hi
      exact ⟨j,rfl⟩
    · rw [sum_image (fun x _ y _ h ↦ by exact_mod_cast h)]
      simpa only [id_eq,Nat.cast_sum] using (congrArg (fun v : ℕ ↦ (v:ℤ)) hm.symm)

theorem goodPair_iff_complete {t α : ℝ} (ht : 0 < t) (hα : 0 < α) :
    GoodPair t α ↔ Complete (terms t α) := by
  have floorCast (n : ℕ) : ((terms t α n : ℕ):ℤ) = ⌊t*α^n⌋ :=
    Int.natCast_floor_eq_floor (mul_nonneg ht.le (pow_nonneg hα.le n))
  simp only [GoodPair, ← floorCast, eventually_atTop]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.toNat, fun m hm ↦ (cast_represented _ m).mp (hz m (by omega))⟩
  · rintro ⟨u,hu⟩
    refine ⟨(u:ℤ), fun z hz ↦ ?_⟩
    have hz' : 0 ≤ z := (Int.natCast_nonneg u).trans hz
    have h := (cast_represented _ z.toNat).mpr (hu _ (by omega))
    rwa [Int.toNat_of_nonneg hz'] at h

/-- Complete description of the coefficient fibers by rational functions of the base. -/
theorem erdos_349 :
    {(t,α) : ℝ × ℝ | 0 < t ∧ 0 < α ∧ GoodPair t α} = parameters := by
  ext ⟨t,α⟩
  constructor
  · rintro ⟨ht,ha,hg⟩
    exact (parameter_set ht ha).mp ((goodPair_iff_complete ht ha).mp hg)
  · intro hp
    have positive : 0 < t ∧ 0 < α := by
      rcases hp with ⟨h₁,h₂,w,_,hl,_⟩ | ⟨rfl,j,rfl⟩
      · have bound : 2/(α^w.k*(α-1)) ≤ t := (le_max_left _ _).trans hl
        exact ⟨lt_of_lt_of_le (div_pos (by norm_num) (mul_pos (pow_pos (by linarith) _) (by linarith))) bound, by linarith⟩
      · constructor <;> positivity
    exact ⟨positive.1,positive.2,(goodPair_iff_complete positive.1 positive.2).mpr
      ((parameter_set positive.1 positive.2).mpr hp)⟩

theorem golden_ratio_counterexample :
    ∃ t α : ℝ, 0 < t ∧ α ∈ Set.Ioo 1 ((1+Real.sqrt 5)/2) ∧ ¬ GoodPair t α := by
  obtain ⟨t,α,ht,h₁,h₂,hf⟩ := Example.golden_ratio_conjecture_false
  exact ⟨t,α,ht,⟨h₁,h₂⟩, fun h ↦ hf ((goodPair_iff_complete ht (by linarith)).mp h)⟩

#print axioms erdos_349
#print axioms golden_ratio_counterexample

end FloorPowers
