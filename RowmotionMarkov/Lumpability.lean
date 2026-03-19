import RowmotionMarkov.Defs
import Mathlib.GroupTheory.GroupAction.Basic

noncomputable section
open Finset BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def strongLump (K : MK α) (P : Finset (Finset α)) : Prop :=
  ∀ Bi ∈ P, ∀ Bj ∈ P, ∀ x ∈ Bi, ∀ x' ∈ Bi,
    ∑ y ∈ Bj, K.k x y = ∑ y ∈ Bj, K.k x' y

def gEquiv (G : Type*) [Group G] [MulAction G α] (K : MK α) : Prop :=
  ∀ (g : G) (x y : α), K.k (g • x) (g • y) = K.k x y

theorem orbit_lump (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] [MulAction G α]
    (K : MK α) (hK : gEquiv G K)
    (orbs : Finset (Finset α))
    (hinv : ∀ B ∈ orbs, ∀ g : G, Finset.image (g • ·) B = B)
    (htrans : ∀ B ∈ orbs, ∀ x ∈ B, ∀ x' ∈ B, ∃ g : G, g • x = x') :
    strongLump K orbs := by
  intro Bi hBi Bj hBj x hx x' hx'
  obtain ⟨g, hg⟩ := htrans Bi hBi x hx x' hx'
  subst hg
  suffices h : ∑ y ∈ Bj, K.k (g • x) y = ∑ y ∈ Bj, K.k x y from h.symm
  have step : ∀ y, K.k (g • x) y = K.k x (g⁻¹ • y) := fun y => by
    rw [← hK g x (g⁻¹ • y), smul_inv_smul]
  simp_rw [step]
  apply Finset.sum_nbij (g⁻¹ • ·)
  · intro y hy
    have := hinv Bj hBj g⁻¹
    rw [← this]; exact mem_image_of_mem _ hy
  · intro y₁ _ y₂ _ h; simpa using h
  · intro y hy
    refine ⟨g • y, ?_, by simp⟩
    have := hinv Bj hBj g
    rw [← this]; exact mem_image_of_mem _ hy
  · intro _ _; rfl

end
