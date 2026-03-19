import RowmotionMarkov.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
open Finset BigOperators Real

theorem bc_product {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (μ ν : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x) :
    BC (fun (xs : Fin m → α) => ∏ j, μ (xs j))
       (fun (xs : Fin m → α) => ∏ j, ν (xs j)) =
    (BC μ ν) ^ m := by
  unfold BC
  conv_lhs =>
    arg 2; ext xs
    rw [← Finset.prod_mul_distrib,
        Real.sqrt_prod _ (fun i _ => mul_nonneg (hμ (xs i)) (hν (xs i)))]
  rw [Fintype.sum_pow]

theorem hellSq_product {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (μ ν : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x) :
    hellSq (fun (xs : Fin m → α) => ∏ j, μ (xs j))
           (fun (xs : Fin m → α) => ∏ j, ν (xs j)) =
    2 * (1 - (BC μ ν) ^ m) := by
  unfold hellSq; congr 1; congr 1
  exact bc_product m μ ν hμ hν

theorem bc_tensorPow {α : Type*} [Fintype α] [DecidableEq α]
    (K : MK α) (pi : α → ℝ) (hpi : ∀ x, 0 ≤ pi x) (x : α) (t m : ℕ) :
    BC (fun (xs : Fin m → α) => ∏ j, (MK.pw K t).k x (xs j))
       (fun (xs : Fin m → α) => ∏ j, pi (xs j)) =
    (BC (fun y => (MK.pw K t).k x y) pi) ^ m := by
  exact bc_product m (fun y => (K.pw t).k x y) pi
    (fun y => (K.pw t).nn x y) hpi

end
