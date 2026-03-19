import RowmotionMarkov.Defs

noncomputable section
open Finset BigOperators

def tensorK {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (K₁ : MK α) (K₂ : MK β) : MK (α × β) where
  k xy₁ xy₂ := K₁.k xy₁.1 xy₂.1 * K₂.k xy₁.2 xy₂.2
  nn xy₁ xy₂ := mul_nonneg (K₁.nn xy₁.1 xy₂.1) (K₂.nn xy₁.2 xy₂.2)
  rs xy := by
    change ∑ yz : α × β, K₁.k xy.1 yz.1 * K₂.k xy.2 yz.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp [K₂.rs, K₁.rs]

theorem tensor_stat {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (K₁ : MK α) (K₂ : MK β)
    (π₁ : α → ℝ) (π₂ : β → ℝ)
    (h₁ : MK.stat K₁ π₁) (h₂ : MK.stat K₂ π₂) :
    MK.stat (tensorK K₁ K₂) (fun xy => π₁ xy.1 * π₂ xy.2) := by
  refine ⟨fun xy => mul_nonneg (h₁.1 xy.1) (h₂.1 xy.2), ?_, ?_⟩
  · change ∑ xy : α × β, π₁ xy.1 * π₂ xy.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp [h₁.2.1, h₂.2.1]
  · intro yz
    change ∑ xy : α × β, (π₁ xy.1 * π₂ xy.2) * (K₁.k xy.1 yz.1 * K₂.k xy.2 yz.2) =
      π₁ yz.1 * π₂ yz.2
    rw [Fintype.sum_prod_type]
    simp_rw [show ∀ x y, (π₁ x * π₂ y) * (K₁.k x yz.1 * K₂.k y yz.2) =
      (π₁ x * K₁.k x yz.1) * (π₂ y * K₂.k y yz.2) from fun x y => by ring]
    have : ∀ (a : α), ∑ b : β, π₁ a * K₁.k a yz.1 * (π₂ b * K₂.k b yz.2) =
        (π₁ a * K₁.k a yz.1) * ∑ b : β, π₂ b * K₂.k b yz.2 := by
      intro a; rw [← Finset.mul_sum]
    simp_rw [this, ← Finset.sum_mul, h₁.2.2, h₂.2.2]

theorem tensor_rev {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (K₁ : MK α) (K₂ : MK β)
    (π₁ : α → ℝ) (π₂ : β → ℝ)
    (h₁ : MK.rev K₁ π₁) (h₂ : MK.rev K₂ π₂) :
    MK.rev (tensorK K₁ K₂) (fun xy => π₁ xy.1 * π₂ xy.2) := by
  refine ⟨fun xy => mul_nonneg (h₁.1 xy.1) (h₂.1 xy.2), ?_, ?_⟩
  · change ∑ xy : α × β, π₁ xy.1 * π₂ xy.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp [h₁.2.1, h₂.2.1]
  · intro xy₁ xy₂
    show π₁ xy₁.1 * π₂ xy₁.2 * (K₁.k xy₁.1 xy₂.1 * K₂.k xy₁.2 xy₂.2) =
         π₁ xy₂.1 * π₂ xy₂.2 * (K₁.k xy₂.1 xy₁.1 * K₂.k xy₂.2 xy₁.2)
    have r1 := h₁.2.2 xy₁.1 xy₂.1
    have r2 := h₂.2.2 xy₁.2 xy₂.2
    calc π₁ xy₁.1 * π₂ xy₁.2 * (K₁.k xy₁.1 xy₂.1 * K₂.k xy₁.2 xy₂.2)
        = (π₁ xy₁.1 * K₁.k xy₁.1 xy₂.1) * (π₂ xy₁.2 * K₂.k xy₁.2 xy₂.2) := by ring
      _ = (π₁ xy₂.1 * K₁.k xy₂.1 xy₁.1) * (π₂ xy₂.2 * K₂.k xy₂.2 xy₁.2) := by rw [r1, r2]
      _ = _ := by ring

theorem tvd_product_upper {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (μ₁ π₁ : α → ℝ) (μ₂ π₂ : β → ℝ)
    (hμ₁ : ∀ x, 0 ≤ μ₁ x) (hμ₂ : ∀ y, 0 ≤ μ₂ y)
    (hπ₁ : ∀ x, 0 ≤ π₁ x) (hπ₂ : ∀ y, 0 ≤ π₂ y)
    (hμ₂s : ∑ y : β, μ₂ y = 1) (hπ₁s : ∑ x : α, π₁ x = 1) :
    tvd (fun xy : α × β => μ₁ xy.1 * μ₂ xy.2)
        (fun xy : α × β => π₁ xy.1 * π₂ xy.2) ≤
    tvd μ₁ π₁ + tvd μ₂ π₂ := by
  simp only [tvd]
  rw [show (1:ℝ)/2 * ∑ x, |μ₁ x - π₁ x| + (1:ℝ)/2 * ∑ y, |μ₂ y - π₂ y| =
    (1:ℝ)/2 * (∑ x, |μ₁ x - π₁ x| + ∑ y, |μ₂ y - π₂ y|) from by ring]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
  calc ∑ xy : α × β, |μ₁ xy.1 * μ₂ xy.2 - π₁ xy.1 * π₂ xy.2|
      ≤ ∑ xy : α × β, (|μ₁ xy.1 - π₁ xy.1| * |μ₂ xy.2| + |π₁ xy.1| * |μ₂ xy.2 - π₂ xy.2|) := by
        apply sum_le_sum; intro xy _
        calc |μ₁ xy.1 * μ₂ xy.2 - π₁ xy.1 * π₂ xy.2|
            = |(μ₁ xy.1 - π₁ xy.1) * μ₂ xy.2 + π₁ xy.1 * (μ₂ xy.2 - π₂ xy.2)| := by
              congr 1; ring
          _ ≤ |(μ₁ xy.1 - π₁ xy.1) * μ₂ xy.2| + |π₁ xy.1 * (μ₂ xy.2 - π₂ xy.2)| :=
              abs_add_le _ _
          _ = |μ₁ xy.1 - π₁ xy.1| * |μ₂ xy.2| + |π₁ xy.1| * |μ₂ xy.2 - π₂ xy.2| := by
              rw [abs_mul, abs_mul]
    _ = ∑ xy : α × β, |μ₁ xy.1 - π₁ xy.1| * |μ₂ xy.2| +
        ∑ xy : α × β, |π₁ xy.1| * |μ₂ xy.2 - π₂ xy.2| := sum_add_distrib
    _ = (∑ x : α, |μ₁ x - π₁ x|) * (∑ y : β, |μ₂ y|) +
        (∑ x : α, |π₁ x|) * (∑ y : β, |μ₂ y - π₂ y|) := by
        congr 1
        · rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul]
        · rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp_rw [← Finset.sum_mul]; rw [← Finset.mul_sum]
    _ = ∑ x, |μ₁ x - π₁ x| + ∑ y, |μ₂ y - π₂ y| := by
        simp_rw [abs_of_nonneg (hμ₂ _), abs_of_nonneg (hπ₁ _), hμ₂s, hπ₁s]; ring

theorem tvd_product_lower {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (μ₁ π₁ : α → ℝ) (μ₂ π₂ : β → ℝ)
    (hμ₂ : ∀ y, 0 ≤ μ₂ y) (hπ₂ : ∀ y, 0 ≤ π₂ y)
    (hμ₂s : ∑ y : β, μ₂ y = 1) (hπ₂s : ∑ y : β, π₂ y = 1) :
    tvd μ₁ π₁ ≤
    tvd (fun xy : α × β => μ₁ xy.1 * μ₂ xy.2)
        (fun xy : α × β => π₁ xy.1 * π₂ xy.2) := by
  simp only [tvd]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
  calc ∑ x : α, |μ₁ x - π₁ x|
      = ∑ x : α, |∑ y : β, (μ₁ x * μ₂ y - π₁ x * π₂ y)| := by
        congr 1; ext x
        rw [show ∑ y, (μ₁ x * μ₂ y - π₁ x * π₂ y) =
          μ₁ x * ∑ y, μ₂ y - π₁ x * ∑ y, π₂ y from by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]]
        rw [hμ₂s, hπ₂s]; ring
    _ ≤ ∑ x : α, ∑ y : β, |μ₁ x * μ₂ y - π₁ x * π₂ y| := by
        apply sum_le_sum; intro x _; exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ xy : α × β, |μ₁ xy.1 * μ₂ xy.2 - π₁ xy.1 * π₂ xy.2| := by
        rw [Fintype.sum_prod_type]

end
