import Boundary

namespace FloorPowers

open Finset

/-- A discrete index for a parameter cell, independent of the real parameters. -/
structure Word where
  k : ℕ
  start : ℕ
  digit : Fin (k+2) → ℕ

def Word.value (w : Word) (i : ℕ) : ℕ :=
  if h : i < w.k+2 then w.digit ⟨i,h⟩ else 0

/-- A Boolean on integers only. -/
def Word.accept (w : Word) : Bool :=
  decide (Ico w.start (w.start + w.value (w.k+1)) ⊆
    (initial w.value (w.k+1)).powerset.image (fun s ↦ s.sum id))

private theorem test_congr {a b : ℕ → ℕ} {n u : ℕ} (h : ∀ i ≤ n, a i = b i) :
    blockTest a n u ↔ blockTest b n u := by
  have hpre : initial a n = initial b n :=
    image_congr (fun i hi ↦ h i (mem_range.mp hi).le)
  simp only [blockTest, hpre, h n le_rfl]

noncomputable def Word.lower (w : Word) (α : ℝ) : ℝ :=
  max (2/(α^w.k*(α-1))) <| max (2/(α^w.k*(2-α))) <|
    (univ : Finset (Fin (w.k+2))).sup' univ_nonempty (fun i ↦ (w.digit i : ℝ)/α^(i:ℕ))

noncomputable def Word.upper (w : Word) (α : ℝ) : ℝ :=
  (univ : Finset (Fin (w.k+2))).inf' univ_nonempty (fun i ↦ ((w.digit i : ℝ)+1)/α^(i:ℕ))

theorem Word.mem_interval {w : Word} {t α : ℝ} (ht : 0 < t) (hα : 1 < α) (h₂ : α < 2) :
    t ∈ Set.Ico (w.lower α) (w.upper α) ↔
      Margin t α w.k 0 ∧ ∀ i : Fin (w.k+2), terms t α i = w.digit i := by
  have ha₀ : 0 < α := by linarith
  have hd₁ : 0 < α^w.k*(α-1) := mul_pos (pow_pos ha₀ _) (by linarith)
  have hd₂ : 0 < α^w.k*(2-α) := mul_pos (pow_pos ha₀ _) (by linarith)
  simp only [Set.mem_Ico, Word.lower, Word.upper, max_le_iff, sup'_le_iff, lt_inf'_iff,
    mem_univ, forall_const, div_le_iff₀ hd₁, div_le_iff₀ hd₂, ← mul_assoc]
  constructor
  · rintro ⟨⟨h₁,h₂',hlo⟩, hhi⟩
    refine ⟨by simpa [Margin] using And.intro h₁ h₂', fun i ↦ ?_⟩
    exact (Nat.floor_eq_iff (by positivity)).mpr
      ⟨(div_le_iff₀ (pow_pos ha₀ _)).mp (hlo i), (lt_div_iff₀ (pow_pos ha₀ _)).mp (hhi i)⟩
  · rintro ⟨hm, hdigits⟩
    have h₁ : 2 ≤ t * α^w.k*(α-1) := by simpa using hm.1
    have h₂' : 2 ≤ t * α^w.k*(2-α) := by simpa using hm.2
    have hf (i : Fin (w.k+2)) := (Nat.floor_eq_iff (by positivity : 0 ≤ t*α^(i:ℕ))).mp (hdigits i)
    exact ⟨⟨h₁, h₂', fun i ↦ (div_le_iff₀ (pow_pos ha₀ _)).mpr (hf i).1⟩,
      fun i ↦ (lt_div_iff₀ (pow_pos ha₀ _)).mpr (hf i).2⟩

/-- The union contains no infinite sequence or representation predicates. Each word
indexes one explicitly computable half-open interval of coefficients for a fixed base. -/
theorem complete_iff_union_of_intervals {t α : ℝ} (ht : 0 < t) (hα : 1 < α) (h₂ : α < 2) :
    Complete (terms t α) ↔ ∃ w : Word, w.accept = true ∧ t ∈ Set.Ico (w.lower α) (w.upper α) := by
  rw [complete_iff_finite_test ht hα h₂]
  constructor
  · rintro ⟨k, u, hg, hb⟩
    let w : Word := ⟨k, u, fun i ↦ terms t α i⟩
    refine ⟨w, ?_, (Word.mem_interval ht hα h₂).mpr ⟨hg, fun _ ↦ rfl⟩⟩
    apply decide_eq_true
    exact (test_congr (a := terms t α) (b := w.value) (n := k+1) (u := u) (by
      intro i hi
      simp [Word.value, w, show i < k+2 by omega])).mp hb
  · rintro ⟨w, hacc, hi⟩
    obtain ⟨hg, hword⟩ := (Word.mem_interval ht hα h₂).mp hi
    refine ⟨w.k,w.start,hg, ?_⟩
    apply (test_congr (a := w.value) (b := terms t α) (n := w.k+1) (u := w.start) (by
      intro i hi
      have hlt : i < w.k+2 := by omega
      simpa [Word.value, hlt] using (hword ⟨i,hlt⟩).symm)).mp
    unfold blockTest
    exact of_decide_eq_true hacc

/-- Explicit parameter set for positive coefficients and bases, with initial exponent zero. -/
def parameters : Set (ℝ × ℝ) :=
  {p | (1 < p.2 ∧ p.2 < 2 ∧ ∃ w : Word, w.accept = true ∧ p.1 ∈ Set.Ico (w.lower p.2) (w.upper p.2)) ∨
    (p.2 = 2 ∧ ∃ j : ℕ, p.1 = 1/2^j)}

theorem parameter_set {t α : ℝ} (ht : 0 < t) (hα : 0 < α) :
    Complete (terms t α) ↔ (t,α) ∈ parameters := by
  by_cases h₁ : α ≤ 1
  · simp [parameters, incomplete_at_most_one ht hα h₁, not_lt.mpr h₁, show α ≠ 2 by linarith]
  have h₁' := lt_of_not_ge h₁
  rcases lt_trichotomy α 2 with h₂ | rfl | h₂
  · simp [parameters, h₁', h₂, h₂.ne, complete_iff_union_of_intervals ht h₁' h₂]
  · simp [parameters, complete_base_two_iff ht]
  · simp [parameters, incomplete_above_two ht h₂, h₂.not_gt, h₂.ne']

/-- Every good coefficient on the open strip has a right neighborhood of good coefficients. -/
theorem right_stability {t α : ℝ} (ht : 0 < t) (hα : 1 < α) (h₂ : α < 2)
    (hg : Complete (terms t α)) : ∃ T > t, ∀ s ∈ Set.Ico t T, Complete (terms s α) := by
  obtain ⟨w, hw, hlo, hhi⟩ := (complete_iff_union_of_intervals ht hα h₂).mp hg
  exact ⟨_, hhi, fun s hs ↦ (complete_iff_union_of_intervals (ht.trans_le hs.1) hα h₂).mpr
    ⟨w, hw, hlo.trans hs.1, hs.2⟩⟩

#print axioms parameter_set
#print axioms right_stability

end FloorPowers
