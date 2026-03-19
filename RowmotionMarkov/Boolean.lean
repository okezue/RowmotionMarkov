import RowmotionMarkov.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

noncomputable section
open Finset BigOperators Real

variable {n : ℕ}

section CoordChain

def coordK (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : MK Bool where
  k x y := match x, y with
    | false, false => 0
    | false, true  => 1
    | true, false  => q
    | true, true   => 1 - q
  nn x y := by cases x <;> cases y <;> simp <;> linarith
  rs x := by
    simp only [Fintype.sum_bool]
    cases x <;> simp <;> ring

def coordPi (q : ℝ) : Bool → ℝ
  | false => q / (1 + q)
  | true  => 1 / (1 + q)

theorem coordPi_nn {q : ℝ} (hq : 0 < q) (b : Bool) : 0 ≤ coordPi q b := by
  cases b <;> simp [coordPi] <;> positivity

theorem coordPi_sum {q : ℝ} (hq : 0 < q) :
    ∑ b : Bool, coordPi q b = 1 := by
  simp [Fintype.sum_bool, coordPi]; field_simp

theorem coord_rev {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    MK.rev (coordK q hq0 hq1) (coordPi q) :=
  ⟨coordPi_nn hq0, coordPi_sum hq0, fun x y => by
    cases x <;> cases y <;> simp [coordK, coordPi] <;> field_simp <;> ring⟩

end CoordChain

section BooleanChain

variable (p : Fin n → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)

private def kf (p : Fin n → ℝ) (I J : Fin n → Bool) (i : Fin n) : ℝ :=
  match I i, J i with
  | false, false => 0
  | false, true  => 1
  | true, false  => p i
  | true, true   => 1 - p i

def boolK : MK (Fin n → Bool) where
  k I J := ∏ i, kf p I J i
  nn I J := prod_nonneg fun i _ => by
    unfold kf; cases I i <;> cases J i <;> simp
    · exact le_of_lt (hp i).1
    · linarith [(hp i).2]
  rs I := by
    show ∑ J : Fin n → Bool, ∏ i, kf p I J i = 1
    let g : Fin n → Bool → ℝ := fun i b =>
      kf p I (Function.update (fun _ => true) i b) i
    have hg : ∀ (J : Fin n → Bool), ∏ i, kf p I J i = ∏ i, g i (J i) := by
      intro J; congr 1; ext i
      simp only [g, kf, Function.update_self]
    simp_rw [hg, ← Fintype.prod_sum]
    apply Finset.prod_eq_one
    intro i _
    simp only [g, kf, Function.update_self, Fintype.sum_bool]
    cases I i <;> simp

private def pif (p : Fin n → ℝ) (I : Fin n → Bool) (i : Fin n) : ℝ :=
  match I i with
  | false => p i / (1 + p i)
  | true  => 1 / (1 + p i)

def boolPi : (Fin n → Bool) → ℝ := fun I => ∏ i, pif p I i

theorem boolPi_nn (hp : ∀ i, 0 < p i ∧ p i < 1) (I : Fin n → Bool) : 0 ≤ boolPi p I :=
  prod_nonneg fun i _ => by
    simp only [pif]; cases I i <;> simp
    · exact div_nonneg (le_of_lt (hp i).1) (by linarith [(hp i).1])
    · linarith [(hp i).1]

theorem boolPi_sum (hp : ∀ i, 0 < p i ∧ p i < 1) :
    ∑ I : Fin n → Bool, boolPi p I = 1 := by
    unfold boolPi
    let g : Fin n → Bool → ℝ := fun i b =>
      pif p (Function.update (fun _ => true) i b) i
    have hg : ∀ (I : Fin n → Bool), ∏ i, pif p I i = ∏ i, g i (I i) := by
      intro I; congr 1; ext i
      simp only [g, pif, Function.update_self]
    simp_rw [hg, ← Fintype.prod_sum]
    apply Finset.prod_eq_one
    intro i _
    simp only [g, pif, Function.update_self, Fintype.sum_bool]
    field_simp
    exact div_self (by linarith [(hp i).1])

theorem bool_rev : MK.rev (boolK p hp) (boolPi p) := by
  refine ⟨boolPi_nn p hp, boolPi_sum p hp, fun I J => ?_⟩
  show (∏ i, pif p I i) * (∏ i, kf p I J i) = (∏ i, pif p J i) * (∏ i, kf p J I i)
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1; ext i
  simp only [pif, kf]
  cases I i <;> cases J i <;> simp <;> field_simp <;> ring

theorem bool_stat : MK.stat (boolK p hp) (boolPi p) :=
  MK.rev_stat _ _ (bool_rev p hp)

def eigfn (p : Fin n → ℝ) (S : Finset (Fin n)) : (Fin n → Bool) → ℝ :=
  fun I => ∏ i ∈ S, match I i with
    | false => 1 / sqrt (p i)
    | true  => -(sqrt (p i))

def eigval (p : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∏ i ∈ S, (-(p i))

theorem eigfn_ortho (hp : ∀ i, 0 < p i ∧ p i < 1)
    (S T : Finset (Fin n)) (hST : S ≠ T) :
    ∑ I, boolPi p I * eigfn p S I * eigfn p T I = 0 := by
  have hSD : ∃ j, j ∈ S \ T ∨ j ∈ T \ S := by
    by_contra h; push_neg at h
    exact hST (Finset.ext fun x =>
      ⟨fun hx => by_contra fun h' => (h x).1 (mem_sdiff.mpr ⟨hx, h'⟩),
       fun hx => by_contra fun h' => (h x).2 (mem_sdiff.mpr ⟨hx, h'⟩)⟩)
  obtain ⟨j, hj⟩ := hSD
  let g : Fin n → Bool → ℝ := fun i b =>
    (match b with | false => p i / (1 + p i) | true => 1 / (1 + p i)) *
    (if i ∈ S then match b with | false => 1 / sqrt (p i) | true => -(sqrt (p i))
     else 1) *
    (if i ∈ T then match b with | false => 1 / sqrt (p i) | true => -(sqrt (p i))
     else 1)
  have step1 : ∀ I : Fin n → Bool,
      boolPi p I * eigfn p S I * eigfn p T I = ∏ i, g i (I i) := by
    intro I; simp only [boolPi, eigfn, g, pif]
    rw [← Fintype.prod_ite_mem S, ← Fintype.prod_ite_mem T,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp_rw [step1, ← Fintype.prod_sum]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp only [Fintype.sum_bool, g]
  have hsq : sqrt (p j) ^ 2 = p j := Real.sq_sqrt (le_of_lt (hp j).1)
  rcases hj with hj | hj
  · obtain ⟨hjS, hjT⟩ := mem_sdiff.mp hj
    simp only [hjS, hjT, ite_true, ite_false, mul_one]
    field_simp; rw [hsq]; ring
  · obtain ⟨hjT, hjS⟩ := mem_sdiff.mp hj
    simp only [hjS, hjT, ite_true, ite_false, mul_one]
    field_simp; rw [hsq]; ring

theorem eigfn_norm (hp : ∀ i, 0 < p i ∧ p i < 1) (S : Finset (Fin n)) :
    ∑ I, boolPi p I * (eigfn p S I) ^ 2 = 1 := by
  have heq : ∀ I, boolPi p I * (eigfn p S I) ^ 2 =
      boolPi p I * eigfn p S I * eigfn p S I := fun I => by ring
  simp_rw [heq]
  let g : Fin n → Bool → ℝ := fun i b =>
    (match b with | false => p i / (1 + p i) | true => 1 / (1 + p i)) *
    (if i ∈ S then match b with | false => 1 / sqrt (p i) | true => -(sqrt (p i))
     else 1) *
    (if i ∈ S then match b with | false => 1 / sqrt (p i) | true => -(sqrt (p i))
     else 1)
  have step1 : ∀ I, boolPi p I * eigfn p S I * eigfn p S I = ∏ i, g i (I i) := by
    intro I; simp only [boolPi, eigfn, g, pif]
    rw [← Fintype.prod_ite_mem S,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp_rw [step1, ← Fintype.prod_sum]
  apply Finset.prod_eq_one; intro i _
  simp only [Fintype.sum_bool, g]
  have hm : sqrt (p i) * sqrt (p i) = p i := Real.mul_self_sqrt (le_of_lt (hp i).1)
  have hpi : (0:ℝ) < 1 + p i := by linarith [(hp i).1]
  have hsne : sqrt (p i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hp i).1
  split_ifs with h <;> field_simp <;> nlinarith [hm, sq_nonneg (sqrt (p i))]

theorem eigfn_is_eig (hp : ∀ i, 0 < p i ∧ p i < 1)
    (S : Finset (Fin n)) (I : Fin n → Bool) :
    ∑ J, (∏ i, kf p I J i) * eigfn p S J = eigval p S * eigfn p S I := by
  let g : Fin n → Bool → ℝ := fun i b =>
    kf p I (Function.update (fun _ => true) i b) i *
    (if i ∈ S then match b with | false => 1 / sqrt (p i) | true => -(sqrt (p i))
     else 1)
  have step1 : ∀ J : Fin n → Bool,
      (∏ i, kf p I J i) * eigfn p S J = ∏ i, g i (J i) := by
    intro J; simp only [eigfn, g, kf, Function.update_self]
    rw [← Fintype.prod_ite_mem S, ← Finset.prod_mul_distrib]
  simp_rw [step1, ← Fintype.prod_sum]
  rw [eigval, eigfn, ← Fintype.prod_ite_mem S, ← Fintype.prod_ite_mem S,
      ← Finset.prod_mul_distrib]
  congr 1; ext i
  simp only [Fintype.sum_bool, g, kf, Function.update_self]
  have hm : sqrt (p i) * sqrt (p i) = p i := Real.mul_self_sqrt (le_of_lt (hp i).1)
  have hsne : sqrt (p i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hp i).1
  split_ifs with h <;> cases I i <;> simp <;> field_simp <;> nlinarith [hm]

private theorem pw_iter_eig (t : ℕ) (S : Finset (Fin n)) (I : Fin n → Bool) :
    ∑ J, (MK.pw (boolK p hp) t).k I J * eigfn p S J =
    (eigval p S) ^ t * eigfn p S I := by
  induction t generalizing I with
  | zero =>
    simp only [MK.pw, pow_zero, one_mul]
    show ∑ J, (if I = J then 1 else 0) * eigfn p S J = eigfn p S I
    simp
  | succ t ih =>
    simp only [MK.pw, MK.comp, pow_succ]
    show ∑ J, (∑ M, (MK.pw (boolK p hp) t).k I M * (boolK p hp).k M J) *
      eigfn p S J = _
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    have : ∀ M, (MK.pw (boolK p hp) t).k I M *
        ∑ J, (boolK p hp).k M J * eigfn p S J =
        (MK.pw (boolK p hp) t).k I M * (eigval p S * eigfn p S M) := by
      intro M; congr 1
      show ∑ J, (∏ i, kf p M J i) * eigfn p S J = eigval p S * eigfn p S M
      exact eigfn_is_eig p hp S M
    simp_rw [this, ← mul_assoc, mul_comm _ (eigval p S), mul_assoc, ← mul_sum, ih]

private theorem boolPi_pos' (hp : ∀ i, 0 < p i ∧ p i < 1) (I : Fin n → Bool) :
    0 < boolPi p I :=
  prod_pos fun i _ => by
    unfold pif; split
    · exact div_pos (hp i).1 (by linarith [(hp i).1])
    · exact div_pos one_pos (by linarith [(hp i).1])

private theorem chiSq_alt {α : Type*} [Fintype α] (mu pi : α → ℝ)
    (hpi : ∀ x, 0 < pi x) (hmu : ∑ x, mu x = 1) (hpis : ∑ x, pi x = 1) :
    chiSq mu pi = (∑ x, mu x ^ 2 / pi x) - 1 := by
  simp only [chiSq]
  have hsub : ∀ x, (mu x - pi x)^2 / pi x = mu x ^ 2 / pi x - 2 * mu x + pi x := by
    intro x; have hne : pi x ≠ 0 := ne_of_gt (hpi x); field_simp; ring
  simp_rw [hsub]
  rw [show ∑ x : α, (mu x ^ 2 / pi x - 2 * mu x + pi x) =
      ∑ x, mu x ^ 2 / pi x - ∑ x, 2 * mu x + ∑ x, pi x from by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]]
  rw [show ∑ x : α, 2 * mu x = 2 * ∑ x, mu x from (Finset.mul_sum ..).symm]
  rw [hmu, hpis]; ring

private def ck (q : ℝ) : ℕ → Bool → Bool → ℝ
  | 0, a, b => if a = b then 1 else 0
  | t+1, a, c => ∑ b : Bool, ck q t a b *
    (match b, c with | false, false => 0 | false, true => 1
                     | true, false => q | true, true => 1-q)

private theorem pw_prod (t : ℕ) (x I : Fin n → Bool) :
    (MK.pw (boolK p hp) t).k x I = ∏ i, ck (p i) t (x i) (I i) := by
  induction t generalizing x I with
  | zero =>
    show (if x = I then 1 else 0) = ∏ i, (if x i = I i then 1 else 0)
    by_cases hxI : x = I
    · subst hxI; simp
    · simp only [hxI, ite_false]
      have : ∃ i, x i ≠ I i := by by_contra h; push_neg at h; exact hxI (funext h)
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (mem_univ i) (by simp [hi])).symm
  | succ t ih =>
    simp only [MK.pw, MK.comp]
    show ∑ J, (MK.pw (boolK p hp) t).k x J * (boolK p hp).k J I = _
    simp_rw [ih x, boolK]
    show ∑ J, (∏ i, ck (p i) t (x i) (J i)) * (∏ i, kf p J I i) = _
    simp_rw [← Finset.prod_mul_distrib]
    let g : Fin n → Bool → ℝ := fun i b =>
      ck (p i) t (x i) b * kf p (Function.update (fun _ => true) i b) I i
    have hg : ∀ J, ∏ i, ck (p i) t (x i) (J i) * kf p J I i =
        ∏ i, g i (J i) := by
      intro J; congr 1; ext i; simp only [g, kf, Function.update_self]
    simp_rw [hg, ← Fintype.prod_sum]
    congr 1; ext i
    simp only [Fintype.sum_bool, g, kf, Function.update_self, ck]

private theorem ck_explicit (q : ℝ) (hq0 : 0 < q) (_ : q < 1) (t : ℕ) :
    ck q t true true = (1 + q * (-q)^t) / (1+q) ∧
    ck q t true false = q * (1 - (-q)^t) / (1+q) ∧
    ck q t false false = (q + (-q)^t) / (1+q) ∧
    ck q t false true = (1 - (-q)^t) / (1+q) := by
  have hqne : (1:ℝ) + q ≠ 0 := ne_of_gt (by linarith)
  induction t with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ck] <;> field_simp <;> ring
  | succ t ih =>
    obtain ⟨htt, htf, hff, hft⟩ := ih
    have hpow : (-q)^(t+1) = (-q)^t * (-q) := pow_succ (-q) t
    exact ⟨by simp only [ck, Fintype.sum_bool]; rw [htt, htf, hpow]; field_simp; ring,
           by simp only [ck, Fintype.sum_bool]; rw [htt, htf, hpow]; field_simp; ring,
           by simp only [ck, Fintype.sum_bool]; rw [hff, hft, hpow]; field_simp; ring,
           by simp only [ck, Fintype.sum_bool]; rw [hff, hft, hpow]; field_simp; ring⟩

private theorem coord_ratio_eq (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (t : ℕ) (ht : 0 < t) (a : Bool) :
    ∑ b : Bool, (ck q t a b)^2 /
      (match b with | false => q/(1+q) | true => 1/(1+q)) =
    1 + (if a then q^(2*t+1) else q^(2*t-1)) := by
  obtain ⟨htt, htf, hff, hft⟩ := ck_explicit q hq0 hq1 t
  simp only [Fintype.sum_bool]
  have hqne : (1:ℝ) + q ≠ 0 := ne_of_gt (by linarith)
  have hqne2 : q ≠ 0 := ne_of_gt hq0
  set u := (-q)^t with hu_def
  have hsq : u * u = q^(2*t) := by
    show (-q)^t * (-q)^t = q^(2*t)
    rw [← pow_add, show t + t = 2 * t from by omega,
        Even.neg_pow (even_two_mul t) q]
  have hexp : q^(2*t+1) = q^(2*t) * q := by
    rw [show 2*t+1 = (2*t).succ from by omega, pow_succ]
  have hexp2 : q^(2*t-1) = q^(2*t) / q := by
    rw [eq_div_iff hqne2]
    rw [show q ^ (2 * t - 1) * q = q ^ (2 * t - 1 + 1) from (pow_succ ..).symm]
    congr 1; omega
  cases a <;> simp only [ite_false, ite_true, Bool.false_eq_true]
  · rw [hff, hft, hexp2, ← hsq]; field_simp; ring
  · rw [htt, htf, hexp, ← hsq]; field_simp; ring

theorem chiSq_formula (t : ℕ) (ht : 0 < t) (x : Fin n → Bool) :
    chiSq (fun I => (MK.pw (boolK p hp) t).k x I) (boolPi p) =
    (∏ i : Fin n, (1 + if x i then (p i) ^ (2*t+1) else (p i) ^ (2*t-1))) - 1 := by
  rw [chiSq_alt _ _ (boolPi_pos' p hp)
    ((MK.pw (boolK p hp) t).rs x) (boolPi_sum p hp)]
  congr 1
  simp_rw [pw_prod p hp t x]
  have hfact : ∀ I : Fin n → Bool,
      (∏ i, ck (p i) t (x i) (I i))^2 / (∏ i, pif p I i) =
      ∏ i, ((ck (p i) t (x i) (I i))^2 / pif p I i) := by
    intro I
    rw [← Finset.prod_pow, Finset.prod_div_distrib]
  simp_rw [show boolPi p = fun I => ∏ i, pif p I i from rfl, hfact]
  let g : Fin n → Bool → ℝ := fun i b =>
    (ck (p i) t (x i) b)^2 / pif p (Function.update (fun _ => true) i b) i
  have hg : ∀ I : Fin n → Bool,
      ∏ i, (ck (p i) t (x i) (I i))^2 / pif p I i = ∏ i, g i (I i) := by
    intro I; congr 1; ext i; simp only [g, pif, Function.update_self]
  simp_rw [hg, ← Fintype.prod_sum]
  congr 1; ext i
  have htmp : ∀ b : Bool, g i b = (ck (p i) t (x i) b)^2 /
      (match b with | false => p i / (1 + p i) | true => 1 / (1 + p i)) := by
    intro b; simp only [g, pif, Function.update_self]
  simp_rw [htmp]
  exact coord_ratio_eq (p i) (hp i).1 (hp i).2 t ht (x i)

theorem chiSq_max_empty (t : ℕ) (ht : 0 < t) (x : Fin n → Bool) :
    chiSq (fun I => (MK.pw (boolK p hp) t).k x I) (boolPi p) ≤
    chiSq (fun I => (MK.pw (boolK p hp) t).k (fun _ => false) I) (boolPi p) := by
  rw [chiSq_formula p hp t ht x, chiSq_formula p hp t ht (fun _ => false)]
  apply sub_le_sub_right
  apply Finset.prod_le_prod
  · intro i _
    have h1 := pow_nonneg (le_of_lt (hp i).1) (2*t-1)
    have h2 := pow_nonneg (le_of_lt (hp i).1) (2*t+1)
    cases x i <;> simp <;> linarith
  · intro i _
    have hle : (p i) ^ (2*t+1) ≤ (p i) ^ (2*t-1) :=
      pow_le_pow_of_le_one (le_of_lt (hp i).1) (le_of_lt (hp i).2) (by omega)
    cases x i <;> simp <;> linarith

def momentFn (p : Fin n → ℝ) (t : ℕ) : ℝ := ∑ i : Fin n, (p i) ^ (2*t-1)

private theorem tvd_le_half_sqrt_chiSq {α : Type*} [Fintype α] (μ pi : α → ℝ)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x : α, pi x = 1) :
    tvd μ pi ≤ (1/2) * sqrt (chiSq μ pi) := by
  unfold tvd chiSq
  have hnn : ∀ x, 0 ≤ pi x := fun x => le_of_lt (hpos x)
  suffices h : ∑ x : α, |μ x - pi x| ≤ sqrt (∑ x : α, (μ x - pi x) ^ 2 / pi x) by
    linarith
  have h1 : ∑ x : α, |μ x - pi x| =
      ∑ x : α, (|μ x - pi x| / sqrt (pi x)) * sqrt (pi x) := by
    congr 1; ext x
    rw [div_mul_cancel₀]
    exact Real.sqrt_ne_zero'.mpr (hpos x)
  rw [h1]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun x => |μ x - pi x| / sqrt (pi x)) (fun x => sqrt (pi x))
  have h3 : sqrt (∑ x : α, (fun x => sqrt (pi x)) x ^ 2) = 1 := by
    simp only [sq_sqrt (hnn _)]
    rw [hsum, Real.sqrt_one]
  rw [h3, mul_one] at h2
  calc ∑ x : α, |μ x - pi x| / sqrt (pi x) * sqrt (pi x) ≤
      sqrt (∑ x, (|μ x - pi x| / sqrt (pi x)) ^ 2) := h2
    _ = sqrt (∑ x, (μ x - pi x) ^ 2 / pi x) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        rw [div_pow, sq_abs, sq_sqrt (hnn x)]

private theorem prod_add_one_le_exp_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∏ i ∈ s, (1 + f i) ≤ exp (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' hna ih =>
    rw [Finset.prod_insert hna, Finset.sum_insert hna, Real.exp_add]
    apply mul_le_mul
    · linarith [Real.add_one_le_exp (f a)]
    · exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    · apply Finset.prod_nonneg
      intro i hi
      linarith [hf i (Finset.mem_insert_of_mem hi)]
    · exact le_of_lt (Real.exp_pos _)

theorem tvd_upper (t : ℕ) (ht : 0 < t) (x : Fin n → Bool) :
    tvd (fun I => (MK.pw (boolK p hp) t).k x I) (boolPi p) ≤
    (1/2) * sqrt (exp (momentFn p t) - 1) := by
  calc tvd (fun I => (MK.pw (boolK p hp) t).k x I) (boolPi p)
      ≤ (1/2) * sqrt (chiSq (fun I => (MK.pw (boolK p hp) t).k x I) (boolPi p)) :=
        tvd_le_half_sqrt_chiSq _ _ (boolPi_pos' p hp) (boolPi_sum p hp)
    _ ≤ (1/2) * sqrt (chiSq (fun I => (MK.pw (boolK p hp) t).k (fun _ => false) I) (boolPi p)) := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.sqrt_le_sqrt (chiSq_max_empty p hp t ht x)
        · norm_num
    _ = (1/2) * sqrt ((∏ i : Fin n, (1 + (p i) ^ (2*t-1))) - 1) := by
        congr 1; congr 1
        rw [chiSq_formula p hp t ht (fun _ => false)]
        simp
    _ ≤ (1/2) * sqrt (exp (momentFn p t) - 1) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.sqrt_le_sqrt
          apply sub_le_sub_right
          unfold momentFn
          exact prod_add_one_le_exp_sum Finset.univ _ (fun i _ =>
            pow_nonneg (le_of_lt (hp i).1) _)
        · norm_num

theorem tvd_lower (t : ℕ) (ht : 1 ≤ t) :
    0 ≤ tvd (fun I => (MK.pw (boolK p hp) t).k (fun _ => false) I) (boolPi p) :=
  tvd_nn _ _

end BooleanChain
end
