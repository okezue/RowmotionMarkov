import RowmotionMarkov.Defs
import RowmotionMarkov.Lumpability

noncomputable section
open Finset BigOperators

variable (r : ℕ) (hr : 0 < r)
  (ns : Fin r → ℕ) (hns : ∀ i, 0 < ns i)
  (ps : Fin r → ℝ) (hps0 : ∀ i, 0 < ps i) (hps1 : ∀ i, ps i < 1)

def levelWt (r : ℕ) (ns : Fin r → ℕ) (ps : Fin r → ℝ) (k : Fin r) : ℝ :=
  (∏ i ∈ Finset.univ.filter (fun i => i.val < k.val), (ps i)⁻¹ ^ (ns i)) *
  ((1 + (ps k)⁻¹) ^ (ns k) - 1)

def totalMass (r : ℕ) (ns : Fin r → ℕ) (ps : Fin r → ℝ) : ℝ :=
  1 + ∑ k : Fin r, levelWt r ns ps k

def exitUp' (r : ℕ) (ns : Fin r → ℕ) (ps : Fin r → ℝ) (k : Fin r) : ℝ :=
  (1 - (ps k) ^ (ns k)) / ((1 + ps k) ^ (ns k) - (ps k) ^ (ns k))

def exitDn' (r : ℕ) (ns : Fin r → ℕ) (ps : Fin r → ℝ) (k : Fin r) : ℝ :=
  (ps k) ^ (ns k) / ((1 + ps k) ^ (ns k) - (ps k) ^ (ns k))

theorem exitRateSum (k : Fin r) :
    exitUp' r ns ps k + exitDn' r ns ps k =
    1 / ((1 + ps k) ^ (ns k) - (ps k) ^ (ns k)) := by
  unfold exitUp' exitDn'; ring

theorem exitUp_pos (hns : ∀ i, 0 < ns i) (hps0 : ∀ i, 0 < ps i)
    (hps1 : ∀ i, ps i < 1) (k : Fin r) :
    0 < exitUp' r ns ps k := by
  unfold exitUp'
  apply div_pos
  · have : (ps k) ^ (ns k) < 1 :=
      pow_lt_one₀ (le_of_lt (hps0 k)) (hps1 k) (by have := hns k; omega)
    linarith
  · have : (ps k) ^ (ns k) < (1 + ps k) ^ (ns k) := by
      apply pow_lt_pow_left₀ (by linarith [hps0 k]) (le_of_lt (hps0 k))
      exact (by have := hns k; omega : ns k ≠ 0)
    linarith

theorem exitDn_pos (hns : ∀ i, 0 < ns i) (hps0 : ∀ i, 0 < ps i) (k : Fin r) :
    0 < exitDn' r ns ps k := by
  unfold exitDn'
  apply div_pos
  · exact pow_pos (hps0 k) (ns k)
  · have : (ps k) ^ (ns k) < (1 + ps k) ^ (ns k) := by
      apply pow_lt_pow_left₀ (by linarith [hps0 k]) (le_of_lt (hps0 k))
      exact (by have := hns k; omega : ns k ≠ 0)
    linarith

end
