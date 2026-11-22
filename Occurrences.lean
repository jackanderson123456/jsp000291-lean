import ParameterSet

/-! The corresponding answer when the summands must have distinct indices. -/

namespace FloorPowers.Occurrences
open Finset

def Complete (a : ℕ → ℕ) : Prop := ∃ u : ℕ, ∀ m ≥ u, ∃ s : Finset ℕ, s.sum a = m

private def PrefixRep (a : ℕ → ℕ) (n m : ℕ) :=
  ∃ s : Finset ℕ, s ⊆ range n ∧ s.sum a = m

private def Block (a : ℕ → ℕ) (n u : ℕ) :=
  ∀ m, u ≤ m → m < u+a n → PrefixRep a n m

private theorem localRep {a : ℕ → ℕ} (ha : Monotone a) {m n : ℕ} (hm : m < a n)
    (hr : ∃ s : Finset ℕ, s.sum a = m) : PrefixRep a n m := by
  obtain ⟨s,hs⟩ := hr
  refine ⟨s,?_,hs⟩
  intro i hi
  have hle : a i ≤ m := hs ▸ single_le_sum (f := a) (fun _ _ ↦ Nat.zero_le _) hi
  exact mem_range.mpr (lt_of_not_ge (fun h ↦ (ha h).not_gt (hle.trans_lt hm)))

private theorem extend {a : ℕ → ℕ} {m n : ℕ} (hr : PrefixRep a n m) :
    PrefixRep a (n+1) (a n+m) := by
  obtain ⟨s,hs,he⟩ := hr
  refine ⟨insert n s,?_,by rw [sum_insert (fun hn ↦ (lt_irrefl n) (mem_range.mp (hs hn))),he]⟩
  intro i hi
  rcases mem_insert.mp hi with rfl | h
  · exact mem_range.mpr (Nat.lt_succ_self _)
  · exact range_mono (Nat.le_succ n) (hs h)

private theorem complete_iff_block {t α : ℝ} (ht : 0 < t) (ha : 1 < α) (h₂ : α < 2) :
    Complete (terms t α) ↔ ∃ k u : ℕ, Margin t α k 0 ∧ Block (terms t α) (k+1) u := by
  let a := terms t α
  have mono : Monotone a := terms_mono ht ha
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨k,hk⟩ := exists_margin ht ha h₂ u
    have hstep := margin_steps ht ha hk
    change a k + u < a (k+1) ∧ a (k+1)+u ≤ 2*a k at hstep
    refine ⟨k,u,⟨le_trans (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) u]) hk.1,
      le_trans (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) u]) hk.2⟩,?_⟩
    intro m hm hmax
    change m < u + a (k+1) at hmax
    by_cases h : m < a (k+1)
    · exact localRep mono h (hu _ hm)
    · have hr := extend (localRep mono (show m-a k < a k by omega) (hu _ (by omega : u ≤ m-a k)))
      rwa [Nat.add_sub_of_le (show a k ≤ m by omega)] at hr
  · rintro ⟨k,u,hk,hb⟩
    have allBlocks : ∀ j ≥ k+1, Block a j u := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact hb
      | succ j hj ih =>
        intro m hm hmax
        by_cases h : m < u+a j
        · obtain ⟨s,hs,he⟩ := ih _ hm h
          exact ⟨s,hs.trans (range_mono (Nat.le_succ j)),he⟩
        · have hd : a (j+1) ≤ 2*a j := by
            simpa [a] using (margin_steps ht ha (margin_mono ht ha h₂ (show k ≤ j by omega) hk)).2
          have hr := extend (ih (m-a j) (by omega) (by omega))
          rwa [Nat.add_sub_of_le (show a j ≤ m by omega)] at hr
    refine ⟨u,fun m hm ↦ ?_⟩
    obtain ⟨j,hj,hlen⟩ := terms_unbounded ht ha (k+1) m
    change m < a j at hlen
    obtain ⟨s,_,he⟩ := allBlocks j hj m hm (by omega)
    exact ⟨s,he⟩

def accept (w : Word) : Bool :=
  decide (Ico w.start (w.start+w.value (w.k+1)) ⊆
    (range (w.k+1)).powerset.image (fun s ↦ s.sum w.value))

private theorem accept_iff {a : ℕ → ℕ} {w : Word}
    (digits : ∀ i : Fin (w.k+2), a i = w.digit i) :
    accept w = true ↔ Block a (w.k+1) w.start := by
  have hv (i : ℕ) (hi : i ≤ w.k+1) : w.value i = a i := by
    have hlt : i < w.k+2 := by omega
    simpa [Word.value,hlt] using (digits ⟨i,hlt⟩).symm
  have he {s : Finset ℕ} (hs : s ⊆ range (w.k+1)) : s.sum w.value = s.sum a :=
    sum_congr rfl (fun i hi ↦ hv i (mem_range.mp (hs hi)).le)
  unfold accept
  rw [decide_eq_true_eq]
  rw [hv _ le_rfl]
  constructor
  · intro h m h₁ h₂
    obtain ⟨s,hs,hm⟩ := mem_image.mp (h (mem_Ico.mpr ⟨h₁,h₂⟩))
    exact ⟨s,mem_powerset.mp hs,(he (mem_powerset.mp hs)).symm.trans hm⟩
  · intro h m hm
    obtain ⟨h₁,h₂⟩ := mem_Ico.mp hm
    obtain ⟨s,hs,he'⟩ := h m h₁ h₂
    exact mem_image.mpr ⟨s,mem_powerset.mpr hs,(he hs).trans he'⟩

theorem interval_union {t α : ℝ} (ht : 0 < t) (ha : 1 < α) (h₂ : α < 2) :
    Complete (terms t α) ↔ ∃ w : Word, accept w = true ∧ t ∈ Set.Ico (w.lower α) (w.upper α) := by
  rw [complete_iff_block ht ha h₂]
  constructor
  · rintro ⟨k,u,hg,hb⟩
    let w : Word := ⟨k,u,fun i ↦ terms t α i⟩
    have digits : ∀ i : Fin (w.k+2), terms t α i = w.digit i := fun _ ↦ rfl
    exact ⟨w,(accept_iff digits).mpr hb,(Word.mem_interval ht ha h₂).mpr ⟨hg,digits⟩⟩
  · rintro ⟨w,hw,hmem⟩
    obtain ⟨hg,hv⟩ := (Word.mem_interval ht ha h₂).mp hmem
    exact ⟨w.k,w.start,hg,(accept_iff hv).mp hw⟩

private theorem of_value_complete {a : ℕ → ℕ} (hc : FloorPowers.Complete a) : Complete a := by
  classical
  obtain ⟨u,hu⟩ := hc
  refine ⟨u,fun m hm ↦ ?_⟩
  obtain ⟨s,hs,he⟩ := hu m hm
  let f (x : ℕ) := if h : x ∈ Set.range a then Classical.choose h else 0
  have hf (x : ℕ) (hx : x ∈ s) : a (f x) = x := by
    dsimp only [f]
    rw [dif_pos (hs x hx)]
    exact Classical.choose_spec (hs x hx)
  refine ⟨s.image f,?_⟩
  rw [sum_image (fun x hx y hy h ↦ (hf x hx).symm.trans ((congrArg a h).trans (hf y hy)))]
  exact (sum_congr rfl hf).trans he

private theorem big_base {t α : ℝ} (ht : 0 < t) (ha : 2 ≤ α) :
    Complete (terms t α) ↔ FloorPowers.Complete (terms t α) := by
  refine ⟨?_,of_value_complete⟩
  let a := terms t α
  have mono : Monotone a := terms_mono ht (by linarith)
  have strict (i j : ℕ) (hi : a i ≠ 0) (hij : i < j) : a i < a j := by
    have hd : 2*a i ≤ a (i+1) := floor_doubles ht ha i
    exact lt_of_lt_of_le (by omega : a i < a (i+1)) (mono hij)
  rintro ⟨u,hu⟩
  refine ⟨u,fun m hm ↦ ?_⟩
  obtain ⟨s,he⟩ := hu m hm
  let r := s.filter (fun i ↦ a i ≠ 0)
  have hinj : Set.InjOn a r := by
    intro i hi j hj eqn
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim ((strict i j (mem_filter.mp hi).2 h).ne eqn)
    · exact h
    · exact False.elim ((strict j i (mem_filter.mp hj).2 h).ne eqn.symm)
  refine ⟨r.image a,fun _ h ↦ by obtain ⟨i,_,rfl⟩ := mem_image.mp h; exact ⟨i,rfl⟩,?_⟩
  rw [sum_image hinj]
  change (s.filter _).sum a = _
  simpa only [sum_filter_ne_zero] using (show s.sum a = m from he)

private theorem slow_base {t α : ℝ} (ht : 0 < t) (ha : 0 < α) (h₁ : α < 1) :
    ¬ Complete (terms t α) := by
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr ht) h₁
  have zeroTail (i : ℕ) (hi : N ≤ i) : terms t α i = 0 := by
    have h := (pow_le_pow_of_le_one ha.le h₁.le hi).trans_lt hN
    apply Nat.lt_one_iff.mp
    exact (Nat.floor_lt_one (by positivity)).mpr (by nlinarith [(lt_div_iff₀ ht).mp h])
  rintro ⟨u,hu⟩
  let bound := (range N).sum (terms t α)
  obtain ⟨s,he⟩ := hu (bound+u+1) (by omega)
  have eqsum : (s ∩ range N).sum (terms t α) = s.sum (terms t α) := by
    apply sum_subset (inter_subset_left)
    intro i hi h
    exact zeroTail i (by by_contra! hi'; exact h (mem_inter.mpr ⟨hi,mem_range.mpr hi'⟩))
  have hle : (s ∩ range N).sum (terms t α) ≤ bound := sum_le_sum_of_subset inter_subset_right
  omega

private theorem unit_base (t : ℝ) : Complete (terms t 1) ↔ ⌊t⌋₊ = 1 := by
  constructor
  · rintro ⟨u,hu⟩
    have dvd (m : ℕ) (hm : u ≤ m) : ⌊t⌋₊ ∣ m := by
      obtain ⟨s,he⟩ := hu m hm
      rw [← he]
      apply Finset.dvd_sum
      simp [terms]
    exact Nat.eq_one_of_dvd_one (by simpa using Nat.dvd_sub (dvd (u+1) (by omega)) (dvd u le_rfl))
  · intro h
    exact ⟨0,fun m _ ↦ ⟨range m,by simp [terms,h]⟩⟩

/-- Starting the exponent at zero, with independent summands indexed by a finite set. -/
theorem full_range {t α : ℝ} (ht : 0 < t) (ha : 0 < α) :
    Complete (terms t α) ↔
      (α = 1 ∧ 1 ≤ t ∧ t < 2) ∨
      (1 < α ∧ α < 2 ∧ ∃ w : Word, accept w = true ∧ t ∈ Set.Ico (w.lower α) (w.upper α)) ∨
      (α = 2 ∧ ∃ j : ℕ, t = 1/2^j) := by
  rcases lt_trichotomy α 1 with h | rfl | h
  · simp [slow_base ht ha h,h.ne,h.not_gt,show α ≠ 2 by linarith]
  · simp [unit_base,Nat.floor_eq_iff ht.le]
    norm_num
  rcases lt_trichotomy α 2 with h₂ | rfl | h₂
  · simp [interval_union ht h h₂,h,h₂,h.ne',h₂.ne]
  · simp [big_base ht (le_rfl : (2:ℝ) ≤ 2),complete_base_two_iff ht]
  · simp [big_base ht h₂.le,incomplete_above_two ht h₂,h.ne',h₂.ne',h₂.not_gt]

#print axioms full_range

end FloorPowers.Occurrences
