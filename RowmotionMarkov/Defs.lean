import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open Finset BigOperators

structure MK (α : Type*) [Fintype α] [DecidableEq α] where
  k : α → α → ℝ
  nn : ∀ x y, 0 ≤ k x y
  rs : ∀ x, ∑ y : α, k x y = 1

namespace MK
variable {α : Type*} [Fintype α] [DecidableEq α]

def comp (A B : MK α) : MK α where
  k x z := ∑ y, A.k x y * B.k y z
  nn x z := sum_nonneg fun y _ => mul_nonneg (A.nn x y) (B.nn y z)
  rs x := by
    rw [sum_comm]; simp_rw [← Finset.mul_sum]; simp [B.rs, A.rs]

def pw (K : MK α) : ℕ → MK α
  | 0 => ⟨fun x y => if x=y then 1 else 0,
    fun x y => by simp only; split_ifs <;> norm_num,
    fun x => by simp only; rw [show (∑ y, if x=y then (1:ℝ) else 0) = 1 from by simp]⟩
  | n+1 => comp (pw K n) K

def stat (K : MK α) (π : α → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ (∑ x, π x = 1) ∧ (∀ y, ∑ x, π x * K.k x y = π y)

def rev (K : MK α) (π : α → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ (∑ x, π x = 1) ∧ (∀ x y, π x * K.k x y = π y * K.k y x)

theorem rev_stat (K : MK α) (π : α → ℝ) (h : rev K π) : stat K π :=
  ⟨h.1, h.2.1, fun y => by
    calc ∑ x, π x * K.k x y = ∑ x, π y * K.k y x := by
          congr 1; ext x; exact h.2.2 x y
      _ = π y * ∑ x, K.k y x := (mul_sum ..).symm
      _ = π y := by rw [K.rs]; ring⟩

end MK

def tvd {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  (1/2) * ∑ x, |μ x - ν x|

def chiSq {α : Type*} [Fintype α] (μ π : α → ℝ) : ℝ :=
  ∑ x, (μ x - π x)^2 / π x

def BC {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  ∑ x, Real.sqrt (μ x * ν x)

def hellSq {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  2 * (1 - BC μ ν)

theorem tvd_nn {α : Type*} [Fintype α] (μ ν : α → ℝ) : 0 ≤ tvd μ ν :=
  mul_nonneg (by norm_num) (sum_nonneg fun x _ => abs_nonneg _)

theorem tvd_symm {α : Type*} [Fintype α] (μ ν : α → ℝ) : tvd μ ν = tvd ν μ := by
  simp only [tvd]; congr 1; congr 1; ext x; rw [abs_sub_comm]

theorem BC_nn {α : Type*} [Fintype α] (μ ν : α → ℝ)
    (_ : ∀ x, 0 ≤ μ x) (_ : ∀ x, 0 ≤ ν x) : 0 ≤ BC μ ν :=
  sum_nonneg fun _ _ => Real.sqrt_nonneg _

end
