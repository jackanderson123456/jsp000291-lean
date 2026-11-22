import Interpolation
import RationalBounds

namespace FloorPowers.Example
open Finset Bounds

def micro (i : Fin 5) : ℚ := ![-1938938,-1349121,-142428,1207308,2223177] i

def box (i : Fin 5) : Bounds := ⟨micro i / 1000000,(micro i + 1)/1000000⟩

/-- The endpoints are separated by sign changes, certified at exact rational values. -/
theorem root_exists (i : Fin 5) : ∃ x : ℝ, (box i).Contains x ∧ q x = 0 := by
  have hcont : Continuous q := by unfold q; fun_prop
  have hle : ((box i).lo:ℝ) ≤ (box i).hi := by
    exact_mod_cast (show (box i).lo ≤ (box i).hi by unfold box; linarith)
  have hex : (q (box i).lo ≤ 0 ∧ 0 ≤ q (box i).hi) ∨ (q (box i).hi ≤ 0 ∧ 0 ≤ q (box i).lo) := by
    fin_cases i <;> norm_num [box,micro,q,Matrix.cons_val_fin_one]
  rcases hex with hp | hm
  · exact intermediate_value_Icc hle hcont.continuousOn hp
  · exact intermediate_value_Icc' hle hcont.continuousOn hm

noncomputable def node (i : Fin 5) : ℝ := Classical.choose (root_exists i)

theorem node_mem (i : Fin 5) : (box i).Contains (node i) := (Classical.choose_spec (root_exists i)).1
theorem node_root (i : Fin 5) : q (node i) = 0 := (Classical.choose_spec (root_exists i)).2

theorem node_injective : Function.Injective node := by
  apply StrictMono.injective
  intro i j hij
  have separated : ∀ i j : Fin 5, i < j → (box i).hi < (box j).lo := by decide +kernel
  exact (node_mem i).2.trans_lt ((show ((box i).hi : ℝ) < (box j).lo by exact_mod_cast separated i j hij).trans_le (node_mem j).1)

private def boxH (a : Bounds) : Bounds :=
  let first := ((point 2).mul a).add (point 4)
  let second := (first.mul a).sub (point 2)
  let third := (second.mul a).sub (point 6)
  (third.mul a).sub (point 1)

private theorem boxH_mem {a : Bounds} {x : ℝ} (hx : a.Contains x) : (boxH a).Contains (h x) := by
  simpa [h, boxH] using Bounds.sub_mem (Bounds.mul_mem (Bounds.sub_mem (Bounds.mul_mem (Bounds.sub_mem (Bounds.mul_mem
    (Bounds.add_mem (Bounds.mul_mem (point_mem 2) hx) (point_mem 4)) hx) (point_mem 2)) hx) (point_mem 6)) hx) (point_mem 1)

private def five (f : Fin 5 → Bounds) := ((((f 0).mul (f 1)).mul (f 2)).mul (f 3)).mul (f 4)

private theorem five_mem {f : Fin 5 → Bounds} {v : Fin 5 → ℝ} (hv : ∀ i, (f i).Contains (v i)) :
    (five f).Contains (∏ i, v i) := by
  rw [Fin.prod_univ_five]
  exact mul_mem (mul_mem (mul_mem (mul_mem (hv 0) (hv 1)) (hv 2)) (hv 3)) (hv 4)

private theorem erased {v : Fin 5 → ℝ} (i : Fin 5) :
    ∏ j ∈ univ.erase i, v j = ∏ j, if j = i then 1 else v j := by
  let w (j : Fin 5) := if j = i then (1:ℝ) else v j
  have h := prod_erase_mul univ w (mem_univ i)
  rw [show w i = 1 by simp [w],mul_one] at h
  exact (prod_congr rfl (fun j hj ↦ (if_neg (mem_erase.mp hj).1).symm)).trans h

private def mask (f : Fin 5 → Bounds) (i j : Fin 5) :=
  if j = i then point 1 else f j

private theorem mask_mem {f : Fin 5 → Bounds} {v : Fin 5 → ℝ} (hv : ∀ j, (f j).Contains (v j))
    (i : Fin 5) : (five (mask f i)).Contains (∏ j ∈ univ.erase i, v j) := by
  rw [erased]
  apply five_mem
  intro j
  by_cases h : j = i
  · simpa [mask,h] using point_mem 1
  · simp [mask,h,hv j]

private def numerator (i : Fin 5) := (boxH (box i)).mul (five (mask (fun j ↦ (point 2).sub (box j)) i))
private def denominator (i : Fin 5) := five (mask (fun j ↦ (box i).sub (box j)) i)

private def enclosure (i : Fin 5) : Bounds :=
  ![⟨-204/1000,-203/1000⟩, ⟨59/1000,60/1000⟩, ⟨66/1000,67/1000⟩, ⟨73/1000,74/1000⟩, ⟨42,44⟩] i

private theorem rational_certificate :
    ∀ i, QuotientBounds (numerator i) (denominator i) (enclosure i) := by
  set_option maxRecDepth 2000 in decide +kernel

theorem weight_mem (i : Fin 5) : (enclosure i).Contains (weight node i) := by
  apply quotient_mem (a := numerator i) (b := denominator i) (hq := rational_certificate i)
  · apply Bounds.mul_mem (boxH_mem (node_mem i))
    apply mask_mem
    intro j
    simpa using Bounds.sub_mem (point_mem 2) (node_mem j)
  · exact mask_mem (fun j ↦ Bounds.sub_mem (node_mem i) (node_mem j)) i

theorem weights_small : |weight node 0| + |weight node 1| + |weight node 2| + |weight node 3| ≤ 405/1000 := by
  have bound (i : Fin 5) : |weight node i| ≤ max |((enclosure i).lo:ℝ)| |((enclosure i).hi:ℝ)| := by
    obtain ⟨hl,hu⟩ := weight_mem i
    exact abs_le.mpr ⟨by grind [le_abs_self (-((enclosure i).lo:ℝ)), abs_neg], by grind [le_abs_self ((enclosure i).hi:ℝ)]⟩
  have h₀ := bound 0
  have h₁ := bound 1
  have h₂ := bound 2
  have h₃ := bound 3
  change |weight node 2| ≤ max |((66/1000:ℚ):ℝ)| |((67/1000:ℚ):ℝ)| at h₂
  change |weight node 3| ≤ max |((73/1000:ℚ):ℝ)| |((74/1000:ℚ):ℝ)| at h₃
  norm_num [enclosure,Matrix.cons_val_fin_one] at h₀ h₁ h₂ h₃
  linarith

theorem large_weight : 42 ≤ weight node 4 ∧ weight node 4 ≤ 44 := by
  simpa [Contains,enclosure] using weight_mem 4

end FloorPowers.Example
