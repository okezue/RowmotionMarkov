import RowmotionMarkov.Defs
import RowmotionMarkov.Lumpability

noncomputable section
open Finset BigOperators

variable (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
  (pL pU : ℝ) (hpL0 : 0 < pL) (hpL1 : pL < 1) (hpU0 : 0 < pU) (hpU1 : pU < 1)

def binP (n k : ℕ) (q : ℝ) : ℝ :=
  (n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)

def exitA_rate (a : ℕ) (pL : ℝ) : ℝ := (1 + pL)⁻¹ ^ a

def exitB_rate (b : ℕ) (pU : ℝ) : ℝ := ((1 + pU⁻¹) ^ b - 1)⁻¹

theorem exitA_pos (hpL0 : 0 < pL) : 0 < exitA_rate a pL := by
  unfold exitA_rate; exact pow_pos (inv_pos.mpr (by linarith)) a

theorem exitB_pos (hb : 0 < b) (hpU0 : 0 < pU) : 0 < exitB_rate b pU := by
  unfold exitB_rate
  apply inv_pos_of_pos
  have h1 : 1 < 1 + pU⁻¹ := by linarith [inv_pos.mpr hpU0]
  have h2 : 1 < (1 + pU⁻¹) ^ b :=
    one_lt_pow₀ h1 (by omega)
  linarith

def sectorA_wt (a : ℕ) (pL : ℝ) : ℝ :=
  ∑ k ∈ Finset.range a, (a.choose k : ℝ) * pL⁻¹ ^ k + pL⁻¹ ^ a

def sectorB_wt (a b : ℕ) (pL pU : ℝ) : ℝ :=
  pL⁻¹ ^ a * ((1 + pU⁻¹) ^ b - 1)

theorem sector_mass_pos_A (hpL0 : 0 < pL) : 0 < sectorA_wt a pL := by
  unfold sectorA_wt
  apply add_pos_of_nonneg_of_pos
  · apply sum_nonneg; intro k _
    apply mul_nonneg (Nat.cast_nonneg _)
    exact pow_nonneg (le_of_lt (inv_pos.mpr hpL0)) k
  · exact pow_pos (inv_pos.mpr hpL0) a

theorem sector_mass_pos_B (hb : 0 < b) (hpL0 : 0 < pL) (hpU0 : 0 < pU) :
    0 < sectorB_wt a b pL pU := by
  unfold sectorB_wt
  apply mul_pos
  · exact pow_pos (inv_pos.mpr hpL0) a
  · have h1 : 1 < 1 + pU⁻¹ := by linarith [inv_pos.mpr hpU0]
    have h2 : 1 < (1 + pU⁻¹) ^ b :=
      one_lt_pow₀ h1 (by omega)
    linarith

end
