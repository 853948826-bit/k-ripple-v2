import Mathlib

/-!
# 涟漪场方程 V2：P1 全局有界

方程 `r(t+1) = D(t) r(t) + W(t) φ(r(t)) + s(t)`，`φ` 逐分量作用。
对应草案 `01_THEORY_CORE/K_RIPPLE_FIELD_EQUATION_V2_DRAFT.md` §2 P1。

形式化口径：
* 向量 `Fin n → ℝ` 上的范数是 Mathlib 的 Pi 上确界范数，即 ‖·‖∞。
* 矩阵的 ‖·‖∞ 诱导范数用"每行绝对值之和 ≤ a"表达（`RowSumLe`），不依赖算子范数库。
* `D(t)` 允许是任意矩阵（草案中为对角阵，见 `rowSumLe_diagonal`）；时变、任意切换。
* 饱和函数 `φ` 只要求 `|φ y| ≤ 1`；`tanh` 是推论 `P1_global_bound_tanh`。
-/

open Finset

namespace KRippleV2

variable {n : ℕ}

/-- 矩阵每行绝对值之和不超过 `a`，即 ‖A‖∞ ≤ a。 -/
def RowSumLe (A : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) : Prop :=
  ∀ i, ∑ j, |A i j| ≤ a

/-- ‖A x‖∞ ≤ a ‖x‖∞。 -/
lemma norm_mulVec_le {A : Matrix (Fin n) (Fin n) ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hA : RowSumLe A a) (x : Fin n → ℝ) : ‖A.mulVec x‖ ≤ a * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
  calc |∑ j, A i j * x j| ≤ ∑ j, |A i j * x j| := abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |x j| := by simp [abs_mul]
    _ ≤ ∑ j, |A i j| * ‖x‖ := by
        gcongr with j
        simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
    _ = (∑ j, |A i j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ a * ‖x‖ := by gcongr; exact hA i

/-- 对角阵：`|d_i| ≤ d` 对所有 i 成立时 ‖diag(d)‖∞ ≤ d。 -/
lemma rowSumLe_diagonal {dv : Fin n → ℝ} {d : ℝ} (h : ∀ i, |dv i| ≤ d) :
    RowSumLe (Matrix.diagonal dv) d := by
  intro i
  simpa [Matrix.diagonal_apply, apply_ite, Finset.sum_ite_eq] using h i

/-- 有界饱和：`|φ| ≤ 1` 时 ‖φ ∘ x‖∞ ≤ 1。 -/
lemma norm_comp_sat_le {φ : ℝ → ℝ} (hφ : ∀ y, |φ y| ≤ 1) (x : Fin n → ℝ) :
    ‖(fun i => φ (x i))‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simpa [Real.norm_eq_abs] using hφ (x i)

/-- 仿射递推不等式 `u(t+1) ≤ d u(t) + c` 的闭式上界。 -/
lemma affine_recurrence_bound {u : ℕ → ℝ} {d c : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (h : ∀ t, u (t + 1) ≤ d * u t + c) (t : ℕ) :
    u t ≤ d ^ t * u 0 + c * (1 - d ^ t) / (1 - d) := by
  have h1 : (0 : ℝ) < 1 - d := by linarith
  induction t with
  | zero => simp
  | succ k ih =>
    calc u (k + 1) ≤ d * u k + c := h k
      _ ≤ d * (d ^ k * u 0 + c * (1 - d ^ k) / (1 - d)) + c := by gcongr
      _ = d ^ (k + 1) * u 0 + c * (1 - d ^ (k + 1)) / (1 - d) := by
          field_simp
          ring

/-- **P1（全局有界，任意初值、任意切换）**。
若对所有 t，‖D(t)‖∞ ≤ d < 1，‖W(t)‖∞ ≤ w，‖s(t)‖∞ ≤ S，且 |φ| ≤ 1，则
`‖r(t)‖∞ ≤ dᵗ ‖r(0)‖∞ + (w + S)(1 − dᵗ)/(1 − d)`。界与 W 的谱无关。 -/
theorem P1_global_bound (D W : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → ℝ)
    (φ : ℝ → ℝ) (r : ℕ → Fin n → ℝ) {d w S : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hw : 0 ≤ w)
    (hD : ∀ t, RowSumLe (D t) d) (hW : ∀ t, RowSumLe (W t) w) (hs : ∀ t, ‖s t‖ ≤ S)
    (hφ : ∀ y, |φ y| ≤ 1)
    (hr : ∀ t, r (t + 1) = (D t).mulVec (r t) + (W t).mulVec (fun i => φ (r t i)) + s t)
    (t : ℕ) :
    ‖r t‖ ≤ d ^ t * ‖r 0‖ + (w + S) * (1 - d ^ t) / (1 - d) := by
  refine affine_recurrence_bound (u := fun t => ‖r t‖) hd0 hd1 (fun t => ?_) t
  have h1 := norm_mulVec_le hd0 (hD t) (r t)
  have h2 := norm_mulVec_le hw (hW t) (fun i => φ (r t i))
  have h3 := norm_comp_sat_le hφ (r t)
  have h4 : w * ‖(fun i => φ (r t i))‖ ≤ w := by nlinarith
  calc ‖r (t + 1)‖
      ≤ ‖(D t).mulVec (r t)‖ + ‖(W t).mulVec (fun i => φ (r t i))‖ + ‖s t‖ := by
        rw [hr t]; exact norm_add₃_le
    _ ≤ d * ‖r t‖ + (w + S) := by linarith [hs t]

/-- P1 的一致形式：对所有 t，`‖r(t)‖∞ ≤ ‖r(0)‖∞ + (w + S)/(1 − d)`，即轨迹永不爆炸。 -/
theorem P1_uniform_bound (D W : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → ℝ)
    (φ : ℝ → ℝ) (r : ℕ → Fin n → ℝ) {d w S : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hw : 0 ≤ w)
    (hD : ∀ t, RowSumLe (D t) d) (hW : ∀ t, RowSumLe (W t) w) (hs : ∀ t, ‖s t‖ ≤ S)
    (hφ : ∀ y, |φ y| ≤ 1)
    (hr : ∀ t, r (t + 1) = (D t).mulVec (r t) + (W t).mulVec (fun i => φ (r t i)) + s t)
    (t : ℕ) :
    ‖r t‖ ≤ ‖r 0‖ + (w + S) / (1 - d) := by
  have hb := P1_global_bound D W s φ r hd0 hd1 hw hD hW hs hφ hr t
  have h1 : (0 : ℝ) < 1 - d := by linarith
  have hS : 0 ≤ S := (norm_nonneg _).trans (hs 0)
  have hp0 : 0 ≤ d ^ t := pow_nonneg hd0 t
  have hp1 : d ^ t ≤ 1 := pow_le_one₀ hd0 hd1.le
  have hr0 : 0 ≤ ‖r 0‖ := norm_nonneg _
  have e1 : d ^ t * ‖r 0‖ ≤ ‖r 0‖ := by nlinarith
  have e2 : (w + S) * (1 - d ^ t) / (1 - d) ≤ (w + S) / (1 - d) := by
    apply div_le_div_of_nonneg_right _ h1.le
    nlinarith
  linarith

/-- P1 代入草案的具体饱和 `tanh`。 -/
theorem P1_global_bound_tanh (D W : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → ℝ)
    (r : ℕ → Fin n → ℝ) {d w S : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hw : 0 ≤ w)
    (hD : ∀ t, RowSumLe (D t) d) (hW : ∀ t, RowSumLe (W t) w) (hs : ∀ t, ‖s t‖ ≤ S)
    (hr : ∀ t, r (t + 1) = (D t).mulVec (r t) + (W t).mulVec (fun i => Real.tanh (r t i)) + s t)
    (t : ℕ) :
    ‖r t‖ ≤ d ^ t * ‖r 0‖ + (w + S) * (1 - d ^ t) / (1 - d) :=
  P1_global_bound D W s Real.tanh r hd0 hd1 hw hD hW hs (fun y => (Real.abs_tanh_lt_one y).le) hr t

/-! ## P2 全局收缩 -/

open Filter Topology

/-- `r` 是方程的一条轨迹（D、W、s 随时间变化，φ 逐分量作用）。 -/
def IsTraj (D W : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → ℝ) (φ : ℝ → ℝ)
    (r : ℕ → Fin n → ℝ) : Prop :=
  ∀ t, r (t + 1) = (D t).mulVec (r t) + (W t).mulVec (fun i => φ (r t i)) + s t

/-- 公共权重向量条件：对所有 t，`(|D(t)| + |W(t)|) v ≤ c v`（逐元素）。 -/
def CommonWeight (D W : ℕ → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ t i, ∑ j, (|D t i j| + |W t i j|) * v j ≤ c * v i

/-- 两条轨迹之差的单步逐分量界：`|Δ(t+1)| ≤ (|D| + |W|) |Δ(t)|`。 -/
lemma diff_step {D W : ℕ → Matrix (Fin n) (Fin n) ℝ} {s : ℕ → Fin n → ℝ} {φ : ℝ → ℝ}
    {r q : ℕ → Fin n → ℝ} (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|)
    (hr : IsTraj D W s φ r) (hq : IsTraj D W s φ q) (t : ℕ) (i : Fin n) :
    |r (t + 1) i - q (t + 1) i| ≤ ∑ j, (|D t i j| + |W t i j|) * |r t j - q t j| := by
  have key : r (t + 1) i - q (t + 1) i =
      ∑ j, (D t i j * (r t j - q t j) + W t i j * (φ (r t j) - φ (q t j))) := by
    rw [hr t, hq t]
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring
  rw [key]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  calc |D t i j * (r t j - q t j) + W t i j * (φ (r t j) - φ (q t j))|
      ≤ |D t i j * (r t j - q t j)| + |W t i j * (φ (r t j) - φ (q t j))| := abs_add_le _ _
    _ = |D t i j| * |r t j - q t j| + |W t i j| * |φ (r t j) - φ (q t j)| := by
        rw [abs_mul, abs_mul]
    _ ≤ |D t i j| * |r t j - q t j| + |W t i j| * |r t j - q t j| :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hφ _ _) (abs_nonneg _)) _
    _ = (|D t i j| + |W t i j|) * |r t j - q t j| := by ring

/-- **P2（时变收缩）**。φ 为 1-Lipschitz，存在公共权重 v、`0 ≤ c`，使所有 t 都有
`(|D(t)| + |W(t)|) v ≤ c v`。若初始差满足 `|Δ_i(0)| ≤ K v_i`，则 `|Δ_i(t)| ≤ K cᵗ v_i`，
即两条轨迹在加权范数 `max_i |x_i| / v_i` 下以速率 cᵗ 互相收敛。 -/
theorem P2_contraction {D W : ℕ → Matrix (Fin n) (Fin n) ℝ} {s : ℕ → Fin n → ℝ}
    {φ : ℝ → ℝ} {r q : ℕ → Fin n → ℝ} {v : Fin n → ℝ} {c K : ℝ}
    (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) (hr : IsTraj D W s φ r) (hq : IsTraj D W s φ q)
    (hc0 : 0 ≤ c) (hM : CommonWeight D W v c) (hK0 : 0 ≤ K)
    (hK : ∀ i, |r 0 i - q 0 i| ≤ K * v i) :
    ∀ t i, |r t i - q t i| ≤ K * c ^ t * v i := by
  intro t
  induction t with
  | zero => intro i; simpa using hK i
  | succ k ih =>
    intro i
    have hKc : 0 ≤ K * c ^ k := mul_nonneg hK0 (pow_nonneg hc0 k)
    calc |r (k + 1) i - q (k + 1) i|
        ≤ ∑ j, (|D k i j| + |W k i j|) * |r k j - q k j| := diff_step hφ hr hq k i
      _ ≤ ∑ j, (|D k i j| + |W k i j|) * (K * c ^ k * v j) := by
          gcongr with j; exact ih j
      _ = K * c ^ k * ∑ j, (|D k i j| + |W k i j|) * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ K * c ^ k * (c * v i) := mul_le_mul_of_nonneg_left (hM k i) hKc
      _ = K * c ^ (k + 1) * v i := by ring

/-- 任何初始差都有加权界：`|e_i| ≤ (Σ_j |e_j| / v_j) v_i`。 -/
lemma weight_bound {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) (e : Fin n → ℝ) :
    ∀ i, |e i| ≤ (∑ j, |e j| / v j) * v i := by
  intro i
  have h : |e i| / v i ≤ ∑ j, |e j| / v j :=
    Finset.single_le_sum (f := fun j => |e j| / v j)
      (fun j _ => div_nonneg (abs_nonneg _) (hv j).le) (Finset.mem_univ i)
  calc |e i| = |e i| / v i * v i := (div_mul_cancel₀ _ (hv i).ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h (hv i).le

lemma weight_bound_nonneg {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) (e : Fin n → ℝ) :
    0 ≤ ∑ j, |e j| / v j :=
  Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (hv j).le

/-- 时不变的一步映射 `F x = D x + W φ(x) + s`。 -/
def stepMap (D W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) (φ : ℝ → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  D.mulVec x + W.mulVec (fun i => φ (x i)) + s

lemma const_traj {D W : Matrix (Fin n) (Fin n) ℝ} {s : Fin n → ℝ} {φ : ℝ → ℝ}
    {x : Fin n → ℝ} (hx : x = stepMap D W s φ x) :
    IsTraj (fun _ => D) (fun _ => W) (fun _ => s) φ (fun _ => x) := fun _ => hx

lemma tendsto_weight_zero {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (K a : ℝ) :
    Tendsto (fun t : ℕ => K * c ^ t * a) atTop (𝓝 0) := by
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul K).mul_const a

/-- **P2（唯一平衡点）**：s 恒定时至多一个平衡点。 -/
theorem P2_unique_equilibrium {D W : Matrix (Fin n) (Fin n) ℝ} {s : Fin n → ℝ} {φ : ℝ → ℝ}
    {v : Fin n → ℝ} {c : ℝ} (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) (hv : ∀ i, 0 < v i)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : CommonWeight (fun _ => D) (fun _ => W) v c)
    {x y : Fin n → ℝ} (hx : x = stepMap D W s φ x) (hy : y = stepMap D W s φ y) : x = y := by
  funext i
  have hb := P2_contraction hφ (const_traj hx) (const_traj hy) hc0 hM
    (weight_bound_nonneg hv (fun j => x j - y j)) (weight_bound hv (fun j => x j - y j))
  have h0 : |x i - y i| ≤ 0 :=
    ge_of_tendsto' (tendsto_weight_zero hc0 hc1 _ (v i)) fun t => hb t i
  have := abs_nonpos_iff.1 h0
  linarith

/-- **P2（全局吸引）**：任意初值出发的轨迹都收敛到平衡点。 -/
theorem P2_global_attraction {D W : Matrix (Fin n) (Fin n) ℝ} {s : Fin n → ℝ} {φ : ℝ → ℝ}
    {v : Fin n → ℝ} {c : ℝ} (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) (hv : ∀ i, 0 < v i)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : CommonWeight (fun _ => D) (fun _ => W) v c)
    {x : Fin n → ℝ} (hx : x = stepMap D W s φ x)
    {r : ℕ → Fin n → ℝ} (hr : IsTraj (fun _ => D) (fun _ => W) (fun _ => s) φ r) :
    Tendsto r atTop (𝓝 x) := by
  rw [tendsto_pi_nhds]
  intro i
  have hb := P2_contraction hφ hr (const_traj hx) hc0 hM
    (weight_bound_nonneg hv (fun j => r 0 j - x j)) (weight_bound hv (fun j => r 0 j - x j))
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun t => dist_nonneg) (fun t => by rw [Real.dist_eq]; exact hb t i)
    (tendsto_weight_zero hc0 hc1 (∑ j, |r 0 j - x j| / v j) (v i))

lemma continuous_of_one_lipschitz {φ : ℝ → ℝ} (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) :
    Continuous φ :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun a b => by
    simpa [Real.dist_eq] using hφ a b).continuous

/-- **P2（平衡点存在）**：s 恒定时存在平衡点（从 0 出发的迭代是 Cauchy 列）。 -/
theorem P2_exists_equilibrium {D W : Matrix (Fin n) (Fin n) ℝ} {s : Fin n → ℝ} {φ : ℝ → ℝ}
    {v : Fin n → ℝ} {c : ℝ} (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) (hv : ∀ i, 0 < v i)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : CommonWeight (fun _ => D) (fun _ => W) v c) :
    ∃ x, x = stepMap D W s φ x := by
  set F := stepMap D W s φ with hFdef
  let r : ℕ → Fin n → ℝ := fun t => F^[t] 0
  have hr : IsTraj (fun _ => D) (fun _ => W) (fun _ => s) φ r := fun t => by
    show F^[t + 1] 0 = F (F^[t] 0)
    rw [Function.iterate_succ_apply']
  have hq : IsTraj (fun _ => D) (fun _ => W) (fun _ => s) φ (fun t => r (t + 1)) :=
    fun t => hr (t + 1)
  have hK0 := weight_bound_nonneg hv (fun j => r 0 j - r 1 j)
  have hb := P2_contraction hφ hr hq hc0 hM hK0 (weight_bound hv (fun j => r 0 j - r 1 j))
  set K := ∑ j, |r 0 j - r 1 j| / v j
  set V := ∑ j, v j
  have hvV : ∀ i, v i ≤ V := fun i =>
    Finset.single_le_sum (f := v) (fun j _ => (hv j).le) (Finset.mem_univ i)
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => (hv j).le
  have hcs : CauchySeq r := by
    refine cauchySeq_of_le_geometric c (K * V) hc1 fun t => ?_
    rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq]
    calc |r t i - r (t + 1) i| ≤ K * c ^ t * v i := hb t i
      _ ≤ K * c ^ t * V := mul_le_mul_of_nonneg_left (hvV i) (by positivity)
      _ = K * V * c ^ t := by ring
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨x, ?_⟩
  have hφc := continuous_of_one_lipschitz hφ
  have hFc : Continuous F := by
    have hpv : Continuous fun y : Fin n → ℝ => fun i => φ (y i) :=
      continuous_pi fun i => hφc.comp (continuous_apply i)
    exact ((continuous_const.matrix_mulVec continuous_id).add
      (continuous_const.matrix_mulVec hpv)).add continuous_const
  have h1 : Tendsto (fun t => r (t + 1)) atTop (𝓝 x) := hx.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => r (t + 1)) atTop (𝓝 (F x)) :=
    ((hFc.tendsto x).comp hx).congr fun t => (hr t).symm
  exact tendsto_nhds_unique h1 h2

/-! ## tanh 是 1-Lipschitz，并代入 P2 -/

lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have e : Real.tanh = fun y => Real.sinh y / Real.cosh y := by
    funext y; exact Real.tanh_eq_sinh_div_cosh y
  rw [e]
  convert h using 1
  rw [← Real.cosh_sq_sub_sinh_sq x]
  ring

lemma tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_tanh x).differentiableAt)
    fun x => ?_
  rw [(hasDerivAt_tanh x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
    Real.norm_eq_abs]
  have h1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
  rw [abs_of_pos (by positivity), div_le_one (by positivity)]
  nlinarith

lemma abs_tanh_sub_le (a b : ℝ) : |Real.tanh a - Real.tanh b| ≤ |a - b| := by
  simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul a b

/-- P2 代入 tanh：存在唯一平衡点，且任意轨迹收敛到它。 -/
theorem P2_tanh {D W : Matrix (Fin n) (Fin n) ℝ} {s : Fin n → ℝ} {v : Fin n → ℝ} {c : ℝ}
    (hv : ∀ i, 0 < v i) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hM : CommonWeight (fun _ => D) (fun _ => W) v c) :
    ∃ x, x = stepMap D W s Real.tanh x ∧
      (∀ y, y = stepMap D W s Real.tanh y → y = x) ∧
      ∀ r : ℕ → Fin n → ℝ, IsTraj (fun _ => D) (fun _ => W) (fun _ => s) Real.tanh r →
        Tendsto r atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := P2_exists_equilibrium abs_tanh_sub_le hv hc0 hc1 hM (s := s)
  exact ⟨x, hx, fun y hy => P2_unique_equilibrium abs_tanh_sub_le hv hc0 hc1 hM hy hx,
    fun r hr => P2_global_attraction abs_tanh_sub_le hv hc0 hc1 hM hx hr⟩

/-! ## 时不变情形：公共权重条件 ⇔ ρ(M) < 1 -/

section SpectralRadius

open scoped Matrix.Norms.Operator ENNReal NNReal

/-- 实矩阵在复数域上的谱半径：复特征值模的最大值。定义只依赖矩阵代数，与所选范数无关。 -/
noncomputable def rho (M : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  spectralRadius ℂ (M.map (algebraMap ℝ ℂ))

lemma pow_entry_nonneg {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) :
    ∀ i j, 0 ≤ (M ^ k) i j := by
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hM l j)

/-- 行绝对值和 ≤ B 时，复化后的 ∞-诱导范数 ≤ B。 -/
lemma norm_map_le {A : Matrix (Fin n) (Fin n) ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i, ∑ j, |A i j| ≤ B) : ‖A.map (algebraMap ℝ ℂ)‖ ≤ B := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i => ∑ j, ‖(A.map (algebraMap ℝ ℂ)) i j‖₊) ≤ ⟨B, hB⟩ := by
    refine Finset.sup_le fun i _ => NNReal.coe_le_coe.1 ?_
    exact Eq.trans_le (by simp [Matrix.map_apply, Real.norm_eq_abs]) (h i)
  exact NNReal.coe_le_coe.2 this

/-- 每一行的绝对值和不超过复化后的 ∞-诱导范数。 -/
lemma rowsum_le_norm (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∑ j, |A i j| ≤ ‖A.map (algebraMap ℝ ℂ)‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := NNReal.coe_le_coe.2 <| Finset.le_sup
    (f := fun i => ∑ j, ‖(A.map (algebraMap ℝ ℂ)) i j‖₊) (Finset.mem_univ i)
  simpa [NNReal.coe_sum, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using h

lemma mulVec_pow_le {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {v : Fin n → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hMv : ∀ i, ∑ j, M i j * v j ≤ c * v i) (k : ℕ) :
    ∀ i, ((M ^ k).mulVec v) i ≤ c ^ k * v i := by
  induction k with
  | zero => intro i; simp
  | succ k ih =>
    intro i
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    calc (M.mulVec ((M ^ k).mulVec v)) i = ∑ j, M i j * ((M ^ k).mulVec v) j := rfl
      _ ≤ ∑ j, M i j * (c ^ k * v j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hM i j)
      _ = c ^ k * ∑ j, M i j * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ c ^ k * (c * v i) := mul_le_mul_of_nonneg_left (hMv i) (pow_nonneg hc0 k)
      _ = c ^ (k + 1) * v i := by ring

/-- **⇒**：非负矩阵 M 若有正权重 v、`c < 1` 使 `M v ≤ c v`，则 `ρ(M) < 1`。 -/
theorem rho_lt_one_of_weight [NeZero n] {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hMv : ∀ i, ∑ j, M i j * v j ≤ c * v i) : rho M < 1 := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hm0 : 0 < v i0 := hv i0
  have hvV : ∀ i, v i ≤ ∑ j, v j := fun i =>
    Finset.single_le_sum (f := v) (fun j _ => (hv j).le) (Finset.mem_univ i)
  have hκ : 0 < (∑ j, v j) / v i0 := div_pos (hm0.trans_le (hvV i0)) hm0
  have hrow : ∀ k i, ∑ j, |(M ^ k) i j| ≤ c ^ k * ((∑ j, v j) / v i0) := by
    intro k i
    have hk := mulVec_pow_le hM hc0 hMv k i
    have hnn := pow_entry_nonneg hM k i
    have h1 : v i0 * ∑ j, |(M ^ k) i j| ≤ ((M ^ k).mulVec v) i := by
      show _ ≤ ∑ j, (M ^ k) i j * v j
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_of_nonneg (hnn j)]
      nlinarith [hi0 j (Finset.mem_univ j), hnn j]
    have h2 : ∑ j, |(M ^ k) i j| ≤ c ^ k * v i / v i0 := by
      rw [le_div_iff₀ hm0]; linarith
    calc ∑ j, |(M ^ k) i j| ≤ c ^ k * v i / v i0 := h2
      _ ≤ c ^ k * (∑ j, v j) / v i0 := by
          gcongr
          exact hvV i
      _ = _ := by ring
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (one_div_pos.2 hκ) hc1
  set A := M.map (algebraMap ℝ ℂ)
  have hnorm : ‖A ^ (N + 1)‖ < 1 := by
    rw [← Matrix.map_pow]
    have hcN : c ^ (N + 1) ≤ c ^ N := by
      rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hc0 N) hc1.le
    calc ‖(M ^ (N + 1)).map (algebraMap ℝ ℂ)‖ ≤ c ^ (N + 1) * ((∑ j, v j) / v i0) :=
          norm_map_le (by positivity) (hrow (N + 1))
      _ ≤ c ^ N * ((∑ j, v j) / v i0) := by gcongr
      _ < 1 := (lt_div_iff₀ hκ).1 (by simpa using hN)
  have hlt : (‖A ^ (N + 1)‖₊ : ℝ≥0∞) < 1 := by
    rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe]
    simpa using hnorm
  calc rho M ≤ (‖A ^ (N + 1)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) *
        (‖(1 : Matrix (Fin n) (Fin n) ℂ)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) :=
        spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ A N
    _ = (‖A ^ (N + 1)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) := by simp
    _ < 1 := ENNReal.rpow_lt_one hlt (by positivity)

/-- **⇐**：非负矩阵 M 若 `ρ(M) < 1`，则存在正权重 v 与 `c < 1` 使 `M v ≤ c v`。
构造：取 ρ < r < 1，由 Gelfand 公式得 N ≥ 1 使 ‖Mᴺ‖ < rᴺ；令 B = M/r，
`v = Σ_{k<N} Bᵏ 𝟙`，错位相消得 `B v = v − 𝟙 + Bᴺ 𝟙 ≤ v`。 -/
theorem weight_of_rho_lt_one [NeZero n] {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hρ : rho M < 1) :
    ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧
      ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ i, ∑ j, M i j * v j ≤ c * v i := by
  obtain ⟨r, hρr, hr1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hρ
  have hr0 : 0 < (r : ℝ) := by
    have : (0 : ℝ≥0∞) < r := zero_le.trans_lt hρr
    exact_mod_cast ENNReal.coe_pos.1 this
  have hr1' : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.1 hr1
  set A := M.map (algebraMap ℝ ℂ)
  have hev : ∀ᶠ k : ℕ in atTop, (‖A ^ k‖₊ : ℝ≥0∞) ^ (1 / k : ℝ) < r :=
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius A).eventually (gt_mem_nhds hρr)
  obtain ⟨N, hN, hN1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpow : (‖A ^ N‖₊ : ℝ≥0∞) < (r : ℝ≥0∞) ^ N := by
    have h := ENNReal.rpow_lt_rpow hN hNpos
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hNpos.ne', ENNReal.rpow_one,
      ENNReal.rpow_natCast] at h
  have hpowR : ‖A ^ N‖ < (r : ℝ) ^ N := by
    rw [← ENNReal.coe_pow] at hpow
    have h := ENNReal.coe_lt_coe.1 hpow
    rw [← NNReal.coe_lt_coe] at h
    simpa using h
  set B : Matrix (Fin n) (Fin n) ℝ := (r : ℝ)⁻¹ • M with hBdef
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => by
    simp only [B, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hr0.le) (hM i j)
  have hBN : ∀ i, ∑ j, (B ^ N) i j ≤ 1 := by
    intro i
    have h1 := rowsum_le_norm (M ^ N) i
    rw [Matrix.map_pow] at h1
    have hMN := pow_entry_nonneg hM N i
    have h2 : ∑ j, (M ^ N) i j ≤ (r : ℝ) ^ N := by
      calc ∑ j, (M ^ N) i j = ∑ j, |(M ^ N) i j| :=
            Finset.sum_congr rfl fun j _ => (abs_of_nonneg (hMN j)).symm
        _ ≤ ‖A ^ N‖ := h1
        _ ≤ _ := hpowR.le
    calc ∑ j, (B ^ N) i j = ((r : ℝ)⁻¹) ^ N * ∑ j, (M ^ N) i j := by
          rw [hBdef, smul_pow, Finset.mul_sum]
          simp [Matrix.smul_apply]
      _ ≤ ((r : ℝ)⁻¹) ^ N * (r : ℝ) ^ N := by gcongr
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr0.ne', one_pow]
  set v : Fin n → ℝ := ∑ k ∈ Finset.range N, (B ^ k).mulVec 1 with hvdef
  have hterm : ∀ k i, 0 ≤ ((B ^ k).mulVec 1) i := fun k i => by
    simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one]
    exact Finset.sum_nonneg fun j _ => pow_entry_nonneg hB0 k i j
  have hv1 : ∀ i, 1 ≤ v i := by
    intro i
    rw [hvdef, Finset.sum_apply]
    have h0 : (0 : ℕ) ∈ Finset.range N := Finset.mem_range.2 (by omega)
    have := Finset.single_le_sum (f := fun k => ((B ^ k).mulVec 1) i)
      (fun k _ => hterm k i) h0
    simpa using this
  have hBv : ∀ i, (B.mulVec v) i ≤ v i := by
    have hg : B.mulVec v = ∑ k ∈ Finset.range N, (B ^ (k + 1)).mulVec 1 := by
      rw [hvdef, Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mulVec_mulVec, ← pow_succ']
    have htel : ∑ k ∈ Finset.range N, (B ^ (k + 1)).mulVec 1 + (B ^ 0).mulVec 1 =
        v + (B ^ N).mulVec 1 := by
      rw [← Finset.sum_range_succ' (fun k => (B ^ k).mulVec 1), Finset.sum_range_succ]
    intro i
    have h := congrFun htel i
    simp only [Pi.add_apply, pow_zero, Matrix.one_mulVec, Pi.one_apply] at h
    have hgN : ((B ^ N).mulVec 1) i ≤ 1 := by simpa [Matrix.mulVec, dotProduct] using hBN i
    rw [hg]
    linarith
  refine ⟨v, fun i => one_pos.trans_le (hv1 i), r, r.2, hr1', fun i => ?_⟩
  have hMB : M = (r : ℝ) • B := by
    rw [hBdef, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  calc ∑ j, M i j * v j = (M.mulVec v) i := rfl
    _ = (r : ℝ) * (B.mulVec v) i := by
        rw [hMB, Matrix.smul_mulVec]; rfl
    _ ≤ (r : ℝ) * v i := mul_le_mul_of_nonneg_left (hBv i) hr0.le

/-- **P2 补全（时不变）**：对非负矩阵，公共权重条件等价于 `ρ(M) < 1`。 -/
theorem weight_iff_rho_lt_one [NeZero n] {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, 0 ≤ M i j) :
    (∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧
      ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ i, ∑ j, M i j * v j ≤ c * v i) ↔ rho M < 1 :=
  ⟨fun ⟨_, hv, _, hc0, hc1, hMv⟩ => rho_lt_one_of_weight hM hv hc0 hc1 hMv,
    weight_of_rho_lt_one hM⟩

/-- P2 的谱判据形式：`ρ(|D| + |W|) < 1` 时，tanh 涟漪方程有唯一、全局吸引的平衡点。 -/
theorem P2_tanh_of_rho [NeZero n] {D W : Matrix (Fin n) (Fin n) ℝ} {s : Fin n → ℝ}
    (hρ : rho (Matrix.of fun i j => |D i j| + |W i j|) < 1) :
    ∃ x, x = stepMap D W s Real.tanh x ∧
      (∀ y, y = stepMap D W s Real.tanh y → y = x) ∧
      ∀ r : ℕ → Fin n → ℝ, IsTraj (fun _ => D) (fun _ => W) (fun _ => s) Real.tanh r →
        Tendsto r atTop (𝓝 x) := by
  obtain ⟨v, hv, c, hc0, hc1, hMv⟩ :=
    weight_of_rho_lt_one (fun i j => by simp only [Matrix.of_apply]; positivity) hρ
  exact P2_tanh hv hc0 hc1 fun _ i => by simpa using hMv i

end SpectralRadius

/-! ## P3 标量形态：f(r) = d r + w tanh r，K = d + w -/

section Scalar

/-- 标量涟漪映射。 -/
noncomputable def scalarMap (d w : ℝ) (x : ℝ) : ℝ := d * x + w * Real.tanh x

lemma abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  simpa [Real.tanh_zero] using abs_tanh_sub_le x 0

lemma one_div_cosh_sq (x : ℝ) : 1 / Real.cosh x ^ 2 = 1 - Real.tanh x ^ 2 := by
  have hc : Real.cosh x ^ 2 ≠ 0 := pow_ne_zero 2 (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, one_sub_div hc, Real.cosh_sq_sub_sinh_sq]

/-- tanh 在正半轴严格凹的点态形式：`x sech² x < tanh x`（x > 0）。 -/
lemma div_cosh_sq_lt_tanh {x : ℝ} (hx : 0 < x) : x / Real.cosh x ^ 2 < Real.tanh x := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have h2 : 2 * x < Real.sinh (2 * x) := Real.self_lt_sinh_iff.2 (by linarith)
  rw [Real.sinh_two_mul] at h2
  have h3 := mul_lt_mul_of_pos_right (show x < Real.sinh x * Real.cosh x by linarith) hc
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_div_iff₀ (by positivity) hc]
  nlinarith

lemma tanh_bounds_pos {x : ℝ} (hx : 0 < x) : x - x ^ 3 ≤ Real.tanh x ∧ Real.tanh x ≤ x := by
  have h1 := abs_tanh_le_abs x
  rw [abs_of_pos hx] at h1
  have hup : Real.tanh x ≤ x := (le_abs_self _).trans h1
  have hlow := div_cosh_sq_lt_tanh hx
  have e : x / Real.cosh x ^ 2 = x * (1 - Real.tanh x ^ 2) := by
    rw [div_eq_mul_one_div, one_div_cosh_sq]
  have ht2 : Real.tanh x ^ 2 ≤ x ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at this
  refine ⟨?_, hup⟩
  nlinarith

/-- 三阶余项：`|tanh x − x| ≤ |x|³`。 -/
lemma abs_tanh_sub_self_le (x : ℝ) : |Real.tanh x - x| ≤ |x| ^ 3 := by
  rcases lt_trichotomy x 0 with h | h | h
  · obtain ⟨h1, h2⟩ := tanh_bounds_pos (neg_pos.2 h)
    rw [Real.tanh_neg] at h1 h2
    rw [abs_of_neg h, abs_le]
    have : 0 ≤ (-x) ^ 3 := pow_nonneg (by linarith) 3
    constructor <;> nlinarith
  · simp [h, Real.tanh_zero]
  · obtain ⟨h1, h2⟩ := tanh_bounds_pos h
    rw [abs_of_pos h, abs_le]
    have : 0 ≤ x ^ 3 := pow_nonneg h.le 3
    constructor <;> nlinarith

lemma hasDerivAt_scalarMap (d w x : ℝ) :
    HasDerivAt (scalarMap d w) (d + w / Real.cosh x ^ 2) x := by
  have h1 : HasDerivAt (fun y => d * y) d x := by
    simpa using (hasDerivAt_id x).const_mul d
  have h2 : HasDerivAt (fun y => w * Real.tanh y) (w / Real.cosh x ^ 2) x := by
    convert (hasDerivAt_tanh x).const_mul w using 1; ring
  exact h1.add h2

/-- 原点处的线性增益就是 K = d + w。 -/
theorem P3_deriv_zero (d w : ℝ) : HasDerivAt (scalarMap d w) (d + w) 0 := by
  simpa [Real.cosh_zero] using hasDerivAt_scalarMap d w 0

/-- 局部余项：`|f(x) − K x| ≤ |w| |x|³`。 -/
lemma scalar_residual (d w x : ℝ) : |scalarMap d w x - (d + w) * x| ≤ |w| * |x| ^ 3 := by
  have e : scalarMap d w x - (d + w) * x = w * (Real.tanh x - x) := by
    simp only [scalarMap]; ring
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_tanh_sub_self_le x) (abs_nonneg w)

lemma scalar_local (d w : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ x, |x| < ε → |scalarMap d w x - (d + w) * x| ≤ δ * |x| := by
  refine ⟨min 1 (δ / (|w| + 1)), by positivity, fun x hx => ?_⟩
  have hx1 : |x| < 1 := hx.trans_le (min_le_left _ _)
  have hx2 : |x| < δ / (|w| + 1) := hx.trans_le (min_le_right _ _)
  have ha := abs_nonneg x
  have hw := abs_nonneg w
  have hsq : |x| ^ 2 ≤ δ / (|w| + 1) := by nlinarith
  have hq : |w| * |x| ^ 2 ≤ δ := by
    calc |w| * |x| ^ 2 ≤ |w| * (δ / (|w| + 1)) := mul_le_mul_of_nonneg_left hsq hw
      _ = |w| * δ / (|w| + 1) := (mul_div_assoc _ _ _).symm
      _ ≤ δ := by rw [div_le_iff₀ (by positivity)]; nlinarith
  calc |scalarMap d w x - (d + w) * x| ≤ |w| * |x| ^ 3 := scalar_residual d w x
    _ = (|w| * |x| ^ 2) * |x| := by ring
    _ ≤ δ * |x| := mul_le_mul_of_nonneg_right hq ha

/-- **P3（|K| < 1：局部耗散）**：原点附近一步收缩。 -/
theorem P3_local_contraction {d w : ℝ} (hK : |d + w| < 1) :
    ∃ ε > 0, ∃ q, 0 ≤ q ∧ q < 1 ∧ ∀ x, |x| < ε → |scalarMap d w x| ≤ q * |x| := by
  obtain ⟨ε, hε, h⟩ := scalar_local d w (δ := (1 - |d + w|) / 2) (by linarith)
  refine ⟨ε, hε, |d + w| + (1 - |d + w|) / 2, by positivity, by linarith, fun x hx => ?_⟩
  have h1 := h x hx
  calc |scalarMap d w x| ≤ |(d + w) * x| + |scalarMap d w x - (d + w) * x| := by
        have := abs_add_le ((d + w) * x) (scalarMap d w x - (d + w) * x)
        simpa using this
    _ ≤ |d + w| * |x| + (1 - |d + w|) / 2 * |x| := by rw [abs_mul]; linarith
    _ = _ := by ring

/-- 一步收缩可迭代：轨迹留在 ε 球内并以 qᵗ 衰减。 -/
lemma iterate_contraction {f : ℝ → ℝ} {ε q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ x, |x| < ε → |f x| ≤ q * |x|) {x0 : ℝ} (hx0 : |x0| < ε) :
    ∀ t, |f^[t] x0| ≤ q ^ t * |x0| ∧ |f^[t] x0| < ε := by
  intro t
  induction t with
  | zero => simpa using hx0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h1 := h _ ih.2
    have hqk : q ^ k * |x0| ≤ |x0| := by
      have := pow_le_one₀ hq0 hq1.le (n := k)
      nlinarith [abs_nonneg x0, pow_nonneg hq0 k]
    refine ⟨?_, ?_⟩
    · calc |f (f^[k] x0)| ≤ q * |f^[k] x0| := h1
        _ ≤ q * (q ^ k * |x0|) := mul_le_mul_of_nonneg_left ih.1 hq0
        _ = q ^ (k + 1) * |x0| := by ring
    · calc |f (f^[k] x0)| ≤ q * |f^[k] x0| := h1
        _ ≤ |f^[k] x0| := by nlinarith [abs_nonneg (f^[k] x0)]
        _ < ε := ih.2

/-- 原点附近 `f(x)·x` 的符号与 K 相同（K ≠ 0）。 -/
theorem P3_local_sign {d w : ℝ} (hK : d + w ≠ 0) :
    ∃ ε > 0, ∀ x, x ≠ 0 → |x| < ε →
      (0 < d + w → 0 < scalarMap d w x * x) ∧ (d + w < 0 → scalarMap d w x * x < 0) := by
  have hKa : 0 < |d + w| := abs_pos.2 hK
  obtain ⟨ε, hε, h⟩ := scalar_local d w (δ := |d + w| / 2) (by linarith)
  refine ⟨ε, hε, fun x hx0 hx => ?_⟩
  have h1 := h x hx
  have hx2 : 0 < x ^ 2 := by positivity
  have e : scalarMap d w x * x = (d + w) * x ^ 2 + (scalarMap d w x - (d + w) * x) * x := by ring
  have hb : |(scalarMap d w x - (d + w) * x) * x| ≤ |d + w| / 2 * x ^ 2 := by
    rw [abs_mul]
    calc |scalarMap d w x - (d + w) * x| * |x| ≤ |d + w| / 2 * |x| * |x| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg x)
      _ = |d + w| / 2 * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  have hb' := abs_le.1 hb
  constructor
  · intro hpos
    rw [abs_of_pos hpos] at hb'
    nlinarith
  · intro hneg
    rw [abs_of_neg hneg] at hb'
    nlinarith

/-- **P3（−1 < K < 0：正负交替衰减）**。 -/
theorem P3_alternating_decay {d w : ℝ} (hK1 : -1 < d + w) (hK0 : d + w < 0) :
    ∃ ε > 0, ∃ q, 0 ≤ q ∧ q < 1 ∧ ∀ x0, x0 ≠ 0 → |x0| < ε → ∀ t,
      |(scalarMap d w)^[t] x0| ≤ q ^ t * |x0| ∧
        (scalarMap d w)^[t + 1] x0 * (scalarMap d w)^[t] x0 < 0 := by
  obtain ⟨ε1, hε1, q, hq0, hq1, hc⟩ := P3_local_contraction (d := d) (w := w)
    (by rw [abs_lt]; constructor <;> linarith)
  obtain ⟨ε2, hε2, hs⟩ := P3_local_sign (d := d) (w := w) hK0.ne
  refine ⟨min ε1 ε2, lt_min hε1 hε2, q, hq0, hq1, fun x0 hx0 hx t => ?_⟩
  have hc' : ∀ x, |x| < min ε1 ε2 → |scalarMap d w x| ≤ q * |x| :=
    fun x hx => hc x (hx.trans_le (min_le_left _ _))
  have hit := iterate_contraction hq0 hq1 hc' hx
  have hne : ∀ t, (scalarMap d w)^[t] x0 ≠ 0 := by
    intro t
    induction t with
    | zero => simpa using hx0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      intro h0
      have := (hs _ ih ((hit k).2.trans_le (min_le_right _ _))).2 hK0
      rw [h0, zero_mul] at this
      exact lt_irrefl _ this
  refine ⟨(hit t).1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact (hs _ (hne t) ((hit t).2.trans_le (min_le_right _ _))).2 hK0

/-- **P3（0 < K < 1：单调衰减，不变号）**。 -/
theorem P3_monotone_decay {d w : ℝ} (hK0 : 0 < d + w) (hK1 : d + w < 1) :
    ∃ ε > 0, ∃ q, 0 ≤ q ∧ q < 1 ∧ ∀ x0, x0 ≠ 0 → |x0| < ε → ∀ t,
      |(scalarMap d w)^[t] x0| ≤ q ^ t * |x0| ∧
        0 < (scalarMap d w)^[t + 1] x0 * (scalarMap d w)^[t] x0 := by
  obtain ⟨ε1, hε1, q, hq0, hq1, hc⟩ := P3_local_contraction (d := d) (w := w)
    (by rw [abs_lt]; constructor <;> linarith)
  obtain ⟨ε2, hε2, hs⟩ := P3_local_sign (d := d) (w := w) hK0.ne'
  refine ⟨min ε1 ε2, lt_min hε1 hε2, q, hq0, hq1, fun x0 hx0 hx t => ?_⟩
  have hc' : ∀ x, |x| < min ε1 ε2 → |scalarMap d w x| ≤ q * |x| :=
    fun x hx => hc x (hx.trans_le (min_le_left _ _))
  have hit := iterate_contraction hq0 hq1 hc' hx
  have hne : ∀ t, (scalarMap d w)^[t] x0 ≠ 0 := by
    intro t
    induction t with
    | zero => simpa using hx0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      intro h0
      have := (hs _ ih ((hit k).2.trans_le (min_le_right _ _))).1 hK0
      rw [h0, zero_mul] at this
      exact lt_irrefl _ this
  refine ⟨(hit t).1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact (hs _ (hne t) ((hit t).2.trans_le (min_le_right _ _))).1 hK0

/-- **P3（K = 0：解耦）**：线性响应为零，只剩三阶余项。 -/
theorem P3_decoupled {d w : ℝ} (hK : d + w = 0) (x : ℝ) :
    |scalarMap d w x| ≤ |w| * |x| ^ 3 := by
  simpa [hK] using scalar_residual d w x

/-- **P3（|K| > 1：原点不稳定）**：原点附近一步放大。 -/
theorem P3_origin_unstable {d w : ℝ} (hK : 1 < |d + w|) :
    ∃ ε > 0, ∃ q, 1 < q ∧ ∀ x, |x| < ε → q * |x| ≤ |scalarMap d w x| := by
  obtain ⟨ε, hε, h⟩ := scalar_local d w (δ := (|d + w| - 1) / 2) (by linarith)
  refine ⟨ε, hε, |d + w| - (|d + w| - 1) / 2, by linarith, fun x hx => ?_⟩
  have h1 := h x hx
  have h2 := abs_sub_abs_le_abs_sub ((d + w) * x) (scalarMap d w x)
  rw [abs_sub_comm, abs_mul] at h2
  calc (|d + w| - (|d + w| - 1) / 2) * |x| = |d + w| * |x| - (|d + w| - 1) / 2 * |x| := by ring
    _ ≤ |scalarMap d w x| := by linarith

/-- 求根引理：`0 < α < u` 时 `α p = u tanh p` 有正解，且 `u sech² p < α`（凹性）。 -/
lemma exists_pos_root {α u : ℝ} (hα : 0 < α) (hu : α < u) :
    ∃ p, 0 < p ∧ α * p = u * Real.tanh p ∧ u / Real.cosh p ^ 2 < α := by
  have hu0 : 0 < u := by linarith
  set g : ℝ → ℝ := fun r => α * r - u * Real.tanh r with hg
  set a := min 1 ((u - α) / (2 * u)) with ha_def
  have ha0 : 0 < a := lt_min one_pos (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have ha2 : a ≤ (u - α) / (2 * u) := min_le_right _ _
  have hua : u * a ≤ (u - α) / 2 := by
    calc u * a ≤ u * ((u - α) / (2 * u)) := mul_le_mul_of_nonneg_left ha2 hu0.le
      _ = (u - α) / 2 := by field_simp
  have hga : g a < 0 := by
    have hb := (tanh_bounds_pos ha0).1
    have : u * (a - a ^ 3) ≤ u * Real.tanh a := mul_le_mul_of_nonneg_left hb hu0.le
    have ha3 : a ^ 3 ≤ a ^ 2 := by nlinarith
    have ha4 : a ^ 2 ≤ a := by nlinarith
    simp only [hg]
    nlinarith
  set b := a + (u + 1) / α
  have hab : a ≤ b := by have : 0 < (u + 1) / α := by positivity
                         linarith
  have hgb : 0 < g b := by
    have ht : Real.tanh b ≤ 1 := (le_abs_self _).trans (Real.abs_tanh_lt_one b).le
    have e : α * b = α * a + (u + 1) := by
      simp only [b]; field_simp
    simp only [hg]
    nlinarith
  have hcont : ContinuousOn g (Set.Icc a b) :=
    ((continuous_const.mul continuous_id).sub
      (continuous_const.mul tanh_lipschitz.continuous)).continuousOn
  obtain ⟨p, hp, hgp⟩ := intermediate_value_Icc hab hcont ⟨hga.le, hgb.le⟩
  have hp0 : 0 < p := ha0.trans_le hp.1
  have hroot : α * p = u * Real.tanh p := by simp only [hg] at hgp; linarith
  refine ⟨p, hp0, hroot, ?_⟩
  have h1 := mul_lt_mul_of_pos_left (div_cosh_sq_lt_tanh hp0) hu0
  have h2 : u / Real.cosh p ^ 2 * p < α * p := by
    rw [hroot]; calc u / Real.cosh p ^ 2 * p = u * (p / Real.cosh p ^ 2) := by ring
      _ < _ := h1
  exact lt_of_mul_lt_mul_right h2 hp0.le

/-- **P3（K > 1：双稳态饱和增益）**：存在对称的非零不动点 ±p，且两者都局部稳定
（导数绝对值 < 1）。 -/
theorem P3_bistable {d w : ℝ} (hd : |d| < 1) (hK : 1 < d + w) :
    ∃ p, 0 < p ∧ scalarMap d w p = p ∧ scalarMap d w (-p) = -p ∧
      |d + w / Real.cosh p ^ 2| < 1 ∧ |d + w / Real.cosh (-p) ^ 2| < 1 := by
  obtain ⟨hd1, hd2⟩ := abs_lt.1 hd
  obtain ⟨p, hp0, hroot, hst⟩ := exists_pos_root (α := 1 - d) (u := w) (by linarith) (by linarith)
  have hw : 0 < w := by linarith
  have hpos : 0 < w / Real.cosh p ^ 2 := by positivity
  have habs : |d + w / Real.cosh p ^ 2| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  refine ⟨p, hp0, ?_, ?_, habs, by rwa [Real.cosh_neg]⟩
  · simp only [scalarMap]; linarith
  · simp only [scalarMap, Real.tanh_neg]; linarith

/-- **P3（K < −1：稳定 2-周期）**：存在 p > 0 使 f(p) = −p、f(−p) = p，且周期轨道的乘子
`f′(p)·f′(−p) = f′(p)²` 小于 1。 -/
theorem P3_period_two {d w : ℝ} (hd : |d| < 1) (hK : d + w < -1) :
    ∃ p, 0 < p ∧ scalarMap d w p = -p ∧ scalarMap d w (-p) = p ∧
      |d + w / Real.cosh p ^ 2| < 1 ∧
      (d + w / Real.cosh p ^ 2) * (d + w / Real.cosh (-p) ^ 2) < 1 := by
  obtain ⟨hd1, hd2⟩ := abs_lt.1 hd
  obtain ⟨p, hp0, hroot, hst⟩ :=
    exists_pos_root (α := 1 + d) (u := -w) (by linarith) (by linarith)
  have hu : 0 < -w := by linarith
  have hpos : 0 < -w / Real.cosh p ^ 2 := by positivity
  have e : w / Real.cosh p ^ 2 = -(-w / Real.cosh p ^ 2) := by ring
  have hm : -1 < d + w / Real.cosh p ^ 2 ∧ d + w / Real.cosh p ^ 2 < 1 := by
    rw [e]; constructor <;> linarith
  refine ⟨p, hp0, ?_, ?_, abs_lt.2 hm, ?_⟩
  · simp only [scalarMap]; linarith
  · simp only [scalarMap, Real.tanh_neg]; linarith
  · rw [Real.cosh_neg]; nlinarith [hm.1, hm.2]

end Scalar

/-! ## P4 挫败使传播衰减（Wielandt 定理中不依赖 Perron–Frobenius 的部分） -/

section Frustration

open scoped Matrix.Norms.Operator ENNReal NNReal

/-- 逐元素绝对值矩阵 |W|（去掉符号的影响强度）。 -/
def absMat (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => |W i j|

@[simp] lemma absMat_apply (W : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    absMat W i j = |W i j| := rfl

lemma absMat_nonneg (W : Matrix (Fin n) (Fin n) ℝ) : ∀ i j, 0 ≤ absMat W i j :=
  fun _ _ => abs_nonneg _

/-- 逐元素：`|Wᵏ| ≤ |W|ᵏ`。 -/
lemma abs_pow_le (W : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    ∀ i j, |(W ^ k) i j| ≤ ((absMat W) ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    rcases eq_or_ne i j with rfl | h
    · simp
    · rw [pow_zero, pow_zero, Matrix.one_apply_ne h, abs_zero]
  | succ k ih =>
    intro i j
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, absMat_apply]
    exact mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg _)

lemma norm_pow_map_le (W : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    ‖(W ^ k).map (algebraMap ℝ ℂ)‖ ≤ ‖((absMat W) ^ k).map (algebraMap ℝ ℂ)‖ := by
  refine norm_map_le (norm_nonneg _) fun i => ?_
  calc ∑ j, |(W ^ k) i j| ≤ ∑ j, ((absMat W) ^ k) i j :=
        Finset.sum_le_sum fun j _ => abs_pow_le W k i j
    _ = ∑ j, |((absMat W) ^ k) i j| := Finset.sum_congr rfl fun j _ =>
        (abs_of_nonneg (pow_entry_nonneg (absMat_nonneg W) k i j)).symm
    _ ≤ _ := rowsum_le_norm _ i

/-- **P4（第一部分）**：任意实矩阵 `ρ(W) ≤ ρ(|W|)`——符号只能削弱、不能增强线性传播增益。 -/
theorem P4_rho_le_rho_abs (W : Matrix (Fin n) (Fin n) ℝ) : rho W ≤ rho (absMat W) := by
  unfold rho
  refine le_of_tendsto_of_tendsto'
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (W.map (algebraMap ℝ ℂ)))
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius
      ((absMat W).map (algebraMap ℝ ℂ))) fun k => ?_
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  rw [← Matrix.map_pow, ← Matrix.map_pow]
  exact ENNReal.coe_le_coe.2 (NNReal.coe_le_coe.1 (by simpa using norm_pow_map_le W k))

lemma abs_eq_one_of_sq {x : ℝ} (h : x ^ 2 = 1) : |x| = 1 := by
  have h2 : |x| ^ 2 = 1 := by rw [sq_abs]; exact h
  have h0 := abs_nonneg x
  nlinarith [sq_nonneg (|x| - 1)]

/-- 平衡（θ = 1）/反平衡（θ = −1）网络的幂：`(Wᵏ)ᵢⱼ = θᵏ σᵢ (|W|ᵏ)ᵢⱼ σⱼ`。 -/
lemma balanced_pow_entry {W : Matrix (Fin n) (Fin n) ℝ} {σ : Fin n → ℝ} {θ : ℝ}
    (hσ : ∀ i, σ i ^ 2 = 1) (hW : ∀ i j, W i j = θ * σ i * |W i j| * σ j) (k : ℕ) :
    ∀ i j, (W ^ k) i j = θ ^ k * σ i * ((absMat W) ^ k) i j * σ j := by
  induction k with
  | zero =>
    intro i j
    rcases eq_or_ne i j with rfl | h
    · rw [pow_zero W, pow_zero (absMat W), Matrix.one_apply_eq]
      linear_combination -(hσ i)
    · rw [pow_zero W, pow_zero (absMat W), Matrix.one_apply_ne h]; ring
  | succ k ih =>
    intro i j
    rw [pow_succ W k, pow_succ (absMat W) k, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ih i l, absMat_apply]
    conv_lhs => rw [hW l j]
    linear_combination (θ ^ (k + 1) * σ i * ((absMat W) ^ k) i l * |W l j| * σ j) * hσ l

/-- **P4（第二部分）**：结构平衡（存在符号切换 σ 使每条边的符号 = σᵢσⱼ，θ = 1）或
反平衡（θ = −1）的网络没有挫败衰减：`ρ(W) = ρ(|W|)`。 -/
theorem P4_balanced_eq {W : Matrix (Fin n) (Fin n) ℝ} {σ : Fin n → ℝ} {θ : ℝ}
    (hσ : ∀ i, σ i ^ 2 = 1) (hθ : θ ^ 2 = 1) (hW : ∀ i j, W i j = θ * σ i * |W i j| * σ j) :
    rho W = rho (absMat W) := by
  have habs : ∀ k i j, |(W ^ k) i j| = ((absMat W) ^ k) i j := by
    intro k i j
    rw [balanced_pow_entry hσ hW k i j, abs_mul, abs_mul, abs_mul, abs_pow,
      abs_eq_one_of_sq hθ, abs_eq_one_of_sq (hσ i), abs_eq_one_of_sq (hσ j),
      abs_of_nonneg (pow_entry_nonneg (absMat_nonneg W) k i j)]
    ring
  have hnorm : ∀ k : ℕ, ‖(W.map (algebraMap ℝ ℂ)) ^ k‖₊ =
      ‖((absMat W).map (algebraMap ℝ ℂ)) ^ k‖₊ := by
    intro k
    rw [← Matrix.map_pow, ← Matrix.map_pow, Matrix.linfty_opNNNorm_def,
      Matrix.linfty_opNNNorm_def]
    refine Finset.sup_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ext
    simp [Matrix.map_apply, Real.norm_eq_abs, habs k i j,
      abs_of_nonneg (pow_entry_nonneg (absMat_nonneg W) k i j)]
  have hf := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (W.map (algebraMap ℝ ℂ))
  have hg := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius
    ((absMat W).map (algebraMap ℝ ℂ))
  simp_rw [hnorm] at hf
  exact tendsto_nhds_unique hf hg

/-- 挫败衰减因子 `η = ρ(W) / ρ(|W|)`。 -/
noncomputable def eta (W : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ := rho W / rho (absMat W)

/-- **P4 推论**：`η ≤ 1`。 -/
theorem P4_eta_le_one (W : Matrix (Fin n) (Fin n) ℝ) : eta W ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact P4_rho_le_rho_abs W)

/-- **P4 推论**：平衡或反平衡且 `ρ(|W|) > 0` 时 `η = 1`。 -/
theorem P4_eta_balanced [NeZero n] {W : Matrix (Fin n) (Fin n) ℝ} {σ : Fin n → ℝ} {θ : ℝ}
    (hσ : ∀ i, σ i ^ 2 = 1) (hθ : θ ^ 2 = 1) (hW : ∀ i j, W i j = θ * σ i * |W i j| * σ j)
    (hpos : rho (absMat W) ≠ 0) : eta W = 1 := by
  have hfin : rho (absMat W) ≠ ⊤ :=
    ((spectralRadius_le_nnnorm (𝕜 := ℂ) _).trans_lt ENNReal.coe_lt_top).ne
  rw [eta, P4_balanced_eq hσ hθ hW, ENNReal.div_self hpos hfin]

end Frustration

/-! ## P5 可辨识性

单节点回归 `y(t) = θ · z(t)`（z 为 `[r_i, tanh r_1..n, s_i]` 等回归量）。数据矩阵 Z 的行是 z(t)。
* 一般判据：参数由无噪数据唯一确定 ⇔ Gram 矩阵 ZᵀZ 非奇异；此时最小二乘精确复原。
* 对角对 (d, W_ii)：两样本可分 ⇔ 两者非零且幅度不同；方向 (1, −1) 上预测差 ≤ |c||x|³。
* β 与 λ：κ 恒定时不可分，κ 取两个不同值即可分。
-/


section Identifiability

open Matrix

variable {T p : Type*} [Fintype T] [Fintype p] [DecidableEq p]

omit [DecidableEq p] in
lemma gram_quad (Z : Matrix T p ℝ) (v : p → ℝ) :
    v ⬝ᵥ ((Zᵀ * Z) *ᵥ v) = (Z *ᵥ v) ⬝ᵥ (Z *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem P5_identifiable_iff (Z : Matrix T p ℝ) :
    Function.Injective Z.mulVec ↔ (Zᵀ * Z).det ≠ 0 := by
  constructor
  · intro hinj hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hq := gram_quad Z v
    rw [hv, dotProduct_zero, eq_comm, dotProduct_self_eq_zero] at hq
    exact hv0 (hinj (hq.trans (Matrix.mulVec_zero Z).symm))
  · intro hdet θ θ' h
    by_contra hne
    apply hdet
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨θ - θ', sub_ne_zero.2 hne, ?_⟩
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, h, sub_self, Matrix.mulVec_zero]

theorem P5_ols_exact (Z : Matrix T p ℝ) (hdet : (Zᵀ * Z).det ≠ 0) (θ : p → ℝ) :
    (Zᵀ * Z)⁻¹ *ᵥ (Zᵀ *ᵥ (Z *ᵥ θ)) = θ := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]

end Identifiability

section DiagSeparation

open Set

lemma tanh_div_strictAnti : StrictAntiOn (fun x => Real.tanh x / x) (Ioi 0) := by
  have hd : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun y => Real.tanh y / y)
      ((1 / Real.cosh x ^ 2 * x - Real.tanh x * 1) / x ^ 2) x :=
    fun x hx => (hasDerivAt_tanh x).div (hasDerivAt_id x) (ne_of_gt hx)
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [(hd x hx).deriv]
  have hx' : (0:ℝ) < x := hx
  have h := div_cosh_sq_lt_tanh hx'
  apply div_neg_of_neg_of_pos _ (by positivity)
  have : 1 / Real.cosh x ^ 2 * x = x / Real.cosh x ^ 2 := by ring
  linarith

lemma tanh_div_abs (x : ℝ) : Real.tanh x / x = Real.tanh |x| / |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Real.tanh_neg, neg_div_neg_eq]

lemma det_factor {x₁ x₂ : ℝ} (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) :
    x₁ * Real.tanh x₂ - x₂ * Real.tanh x₁ =
      x₁ * x₂ * (Real.tanh x₂ / x₂ - Real.tanh x₁ / x₁) := by
  field_simp

theorem P5_diag_separable (x₁ x₂ : ℝ) :
    x₁ * Real.tanh x₂ - x₂ * Real.tanh x₁ ≠ 0 ↔ x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ |x₁| ≠ |x₂| := by
  constructor
  · intro h
    refine ⟨fun h0 => h (by simp [h0]), fun h0 => h (by simp [h0]), fun he => h ?_⟩
    have h₁ : x₁ ≠ 0 := fun h0 => h (by simp [h0])
    have h₂ : x₂ ≠ 0 := fun h0 => h (by simp [h0])
    rw [det_factor h₁ h₂, tanh_div_abs x₁, tanh_div_abs x₂, he, sub_self, mul_zero]
  · rintro ⟨h₁, h₂, he⟩ h
    rw [det_factor h₁ h₂, mul_eq_zero, mul_eq_zero, sub_eq_zero,
      tanh_div_abs x₁, tanh_div_abs x₂] at h
    rcases h with (h | h) | h
    · exact h₁ h
    · exact h₂ h
    · exact he (tanh_div_strictAnti.injOn (abs_pos.2 h₁) (abs_pos.2 h₂) h.symm)

theorem P5_diag_identify {d w d' w' x₁ x₂ : ℝ}
    (hx : x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ |x₁| ≠ |x₂|)
    (e₁ : scalarMap d w x₁ = scalarMap d' w' x₁)
    (e₂ : scalarMap d w x₂ = scalarMap d' w' x₂) : d = d' ∧ w = w' := by
  have hdet := (P5_diag_separable x₁ x₂).2 hx
  unfold scalarMap at e₁ e₂
  have ha : (d - d') * (x₁ * Real.tanh x₂ - x₂ * Real.tanh x₁) = 0 := by
    linear_combination Real.tanh x₂ * e₁ - Real.tanh x₁ * e₂
  have hb : (w - w') * (x₁ * Real.tanh x₂ - x₂ * Real.tanh x₁) = 0 := by
    linear_combination x₁ * e₂ - x₂ * e₁
  exact ⟨sub_eq_zero.1 ((mul_eq_zero.1 ha).resolve_right hdet),
    sub_eq_zero.1 ((mul_eq_zero.1 hb).resolve_right hdet)⟩

theorem P5_diag_weak (d w c x : ℝ) :
    |scalarMap (d + c) (w - c) x - scalarMap d w x| ≤ |c| * |x| ^ 3 := by
  have : scalarMap (d + c) (w - c) x - scalarMap d w x = -c * (Real.tanh x - x) := by
    unfold scalarMap; ring
  rw [this, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (abs_tanh_sub_self_le x) (abs_nonneg c)

end DiagSeparation

theorem P5_kappa_const (b l c κ : ℝ) : (b + c * κ) - (l + c) * κ = b - l * κ := by ring

theorem P5_kappa_identify {b l b' l' κ₁ κ₂ : ℝ} (hκ : κ₁ ≠ κ₂)
    (h₁ : b - l * κ₁ = b' - l' * κ₁) (h₂ : b - l * κ₂ = b' - l' * κ₂) :
    b = b' ∧ l = l' := by
  have hl : (l - l') * (κ₁ - κ₂) = 0 := by linear_combination h₂ - h₁
  have hl' := sub_eq_zero.1 ((mul_eq_zero.1 hl).resolve_right (sub_ne_zero.2 hκ))
  exact ⟨by subst hl'; linarith, hl'⟩

/-! ## P6 输入-响应增益

P2 条件（公共权重 v、c < 1）下：
* `I − J` 在任意点可逆，`J = D + W diag(sech² x)`；
* 平衡点映射 `s ↦ r*(s)` Lipschitz；
* 该映射可微，导数 `G = (I − J(r*))⁻¹`（不调用隐函数定理，直接由 tanh 二阶余项 ≤ 2δ² 得 o(‖h‖)）。
-/

section Gain

open Filter Topology Asymptotics Matrix

variable {n : ℕ}

/-- tanh 的导数 sech²，记为 `sech2`。 -/
noncomputable def sech2 (x : ℝ) : ℝ := 1 / Real.cosh x ^ 2

lemma sech2_nonneg (x : ℝ) : 0 ≤ sech2 x := by unfold sech2; positivity

lemma sech2_le_one (x : ℝ) : sech2 x ≤ 1 := by
  unfold sech2
  rw [div_le_one (by positivity)]
  nlinarith [Real.one_le_cosh x]

/-- tanh 的二阶余项：`|tanh(a+δ) − tanh a − sech²a · δ| ≤ 2δ²`。 -/
lemma tanh_taylor2 (a δ : ℝ) :
    |Real.tanh (a + δ) - Real.tanh a - sech2 a * δ| ≤ 2 * δ ^ 2 := by
  set g : ℝ → ℝ := fun t => Real.tanh t - sech2 a * t
  have hg : ∀ t, HasDerivAt g (sech2 t - sech2 a) t := fun t =>
    (hasDerivAt_tanh t).sub ((hasDerivAt_id t).const_mul (sech2 a)) |>.congr_deriv
      (by unfold sech2; simp)
  have hb : ∀ t ∈ Metric.closedBall a |δ|, ‖sech2 t - sech2 a‖ ≤ 2 * |δ| := by
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq] at ht
    unfold sech2
    rw [one_div_cosh_sq, one_div_cosh_sq, Real.norm_eq_abs,
      show 1 - Real.tanh t ^ 2 - (1 - Real.tanh a ^ 2) =
        (Real.tanh a - Real.tanh t) * (Real.tanh a + Real.tanh t) by ring, abs_mul]
    have h1 : |Real.tanh a - Real.tanh t| ≤ |δ| :=
      (abs_tanh_sub_le a t).trans (by rw [abs_sub_comm]; exact ht)
    have h2 : |Real.tanh a + Real.tanh t| ≤ 2 :=
      (abs_add_le _ _).trans (by linarith [(Real.abs_tanh_lt_one a).le, (Real.abs_tanh_lt_one t).le])
    calc _ ≤ |δ| * 2 := mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |δ| := by ring
  have hmv := (convex_closedBall a |δ|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hg t).hasDerivWithinAt) hb (Metric.mem_closedBall_self (abs_nonneg δ))
    (by rw [Metric.mem_closedBall, Real.dist_eq, add_sub_cancel_left])
  have e : g (a + δ) - g a = Real.tanh (a + δ) - Real.tanh a - sech2 a * δ := by
    simp only [g]; ring
  rw [e, Real.norm_eq_abs, add_sub_cancel_left, Real.norm_eq_abs] at hmv
  calc _ ≤ 2 * |δ| * |δ| := hmv
    _ = 2 * δ ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- 加权极大值原理：`|x| ≤ M|x| + β v` 且 `Mv ≤ cv`（c < 1）⇒ `|x| ≤ β/(1−c) · v`。 -/
lemma weighted_resolvent {M : Matrix (Fin n) (Fin n) ℝ} {v x : Fin n → ℝ} {c β : ℝ}
    (hMn : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hM : ∀ i, ∑ j, M i j * v j ≤ c * v i)
    (hx : ∀ i, |x i| ≤ ∑ j, M i j * |x j| + β * v i) :
    ∀ i, |x i| ≤ β / (1 - c) * v i := by
  intro i
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => |x j| / v j)
    ⟨i, Finset.mem_univ i⟩
  set m := |x k| / v k
  have hxj : ∀ j, |x j| ≤ m * v j := fun j => by
    have := hk j (Finset.mem_univ j)
    rwa [div_le_iff₀ (hv j)] at this
  have hkk : |x k| = m * v k := (div_mul_cancel₀ _ (hv k).ne').symm
  have h1 : m * v k ≤ m * (c * v k) + β * v k := by
    calc m * v k = |x k| := hkk.symm
      _ ≤ ∑ j, M k j * |x j| + β * v k := hx k
      _ ≤ ∑ j, M k j * (m * v j) + β * v k := by
          gcongr with j; exact hMn k j; exact hxj j
      _ = m * ∑ j, M k j * v j + β * v k := by
          rw [Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ m * (c * v k) + β * v k := by
          gcongr; exact div_nonneg (abs_nonneg _) (hv k).le; exact hM k
  have h2 : m * (1 - c) ≤ β := by nlinarith [hv k]
  have hm : m ≤ β / (1 - c) := by rw [le_div_iff₀ (by linarith)]; exact h2
  exact (hxj i).trans (mul_le_mul_of_nonneg_right hm (hv i).le)

/-- 平衡点 x 处的线性化矩阵 `J = D + W diag(sech² x)`。 -/
noncomputable def linJ (D W : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  D + W * Matrix.diagonal (fun j => sech2 (x j))

lemma linJ_mulVec (D W : Matrix (Fin n) (Fin n) ℝ) (x z : Fin n → ℝ) :
    linJ D W x *ᵥ z = D *ᵥ z + W *ᵥ (fun j => sech2 (x j) * z j) := by
  unfold linJ
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  congr 2
  funext j
  exact Matrix.mulVec_diagonal _ _ _

lemma abs_linJ_le (D W : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    |linJ D W x i j| ≤ |D i j| + |W i j| := by
  have e : linJ D W x i j = D i j + W i j * sech2 (x j) := by
    simp [linJ, Matrix.mul_diagonal]
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_nonneg (sech2_nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (sech2_le_one _)

lemma abs_mulVec_le (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) (i : Fin n) :
    |(A *ᵥ z) i| ≤ ∑ j, |A i j| * |z j| := by
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  simp [abs_mul]

variable {D W : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {c : ℝ}

/-- **P6（可逆性）**：P2 条件下，任意点处 `I − J` 可逆。 -/
theorem P6_invertible (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hM : CommonWeight (fun _ => D) (fun _ => W) v c) (x : Fin n → ℝ) :
    (1 - linJ D W x).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
  have hb := weighted_resolvent (M := Matrix.of fun i j => |D i j| + |W i j|) (x := z) (β := 0)
    (fun i j => by simp; positivity) hv hc1 (fun i => by simpa using hM 0 i) fun i => by
      simp only [Matrix.of_apply, zero_mul, add_zero]
      calc |z i| = |(linJ D W x *ᵥ z) i| := by rw [← hz]
        _ ≤ ∑ j, |linJ D W x i j| * |z j| := abs_mulVec_le _ _ i
        _ ≤ _ := by gcongr with j; exact abs_linJ_le D W x i j
  exact hz0 (funext fun i => abs_nonpos_iff.1 (by simpa using hb i))

/-- Lipschitz 常数 `(Σ 1/v_j)(Σ v_j)/(1−c)`。 -/
noncomputable def lipC (v : Fin n → ℝ) (c : ℝ) : ℝ := (∑ j, 1 / v j) * (∑ j, v j) / (1 - c)

lemma lipC_nonneg (hv : ∀ i, 0 < v i) (hc1 : c < 1) : 0 ≤ lipC v c := by
  unfold lipC
  have : 0 ≤ ∑ j, 1 / v j := Finset.sum_nonneg fun j _ => by have := hv j; positivity
  have : 0 ≤ ∑ j, v j := Finset.sum_nonneg fun j _ => (hv j).le
  have : 0 < 1 - c := by linarith
  positivity

/-- 若 `|e| ≤ (|D|+|W|)|e| + |b|` 逐分量成立，则 `‖e‖ ≤ lipC · ‖b‖`。 -/
lemma norm_le_of_resolvent (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hM : CommonWeight (fun _ => D) (fun _ => W) v c) {e b : Fin n → ℝ}
    (he : ∀ i, |e i| ≤ ∑ j, (|D i j| + |W i j|) * |e j| + |b i|) :
    ‖e‖ ≤ lipC v c * ‖b‖ := by
  set β := ∑ j, |b j| / v j
  have hres := weighted_resolvent (M := Matrix.of fun i j => |D i j| + |W i j|) (x := e) (β := β)
    (fun i j => by simp; positivity) hv hc1 (fun i => by simpa using hM 0 i) fun i => by
      simp only [Matrix.of_apply]
      exact (he i).trans (add_le_add le_rfl (weight_bound hv b i))
  have hβ : β ≤ (∑ j, 1 / v j) * ‖b‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm b j)
      (by have := hv j; positivity)
  have h1c : 0 < 1 - c := by linarith
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (lipC_nonneg hv hc1) (norm_nonneg b))).2
    fun i => ?_
  rw [Real.norm_eq_abs]
  have hvi : v i ≤ ∑ j, v j :=
    Finset.single_le_sum (f := v) (fun j _ => (hv j).le) (Finset.mem_univ i)
  calc |e i| ≤ β / (1 - c) * v i := hres i
    _ ≤ β / (1 - c) * ∑ j, v j :=
        mul_le_mul_of_nonneg_left hvi (div_nonneg (weight_bound_nonneg hv b) h1c.le)
    _ ≤ (∑ j, 1 / v j) * ‖b‖ / (1 - c) * ∑ j, v j :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hβ h1c.le)
          (Finset.sum_nonneg fun j _ => (hv j).le)
    _ = lipC v c * ‖b‖ := by unfold lipC; ring

/-- 平衡点方程的差分形式。 -/
lemma eq_diff {s s' x y : Fin n → ℝ} (hx : x = stepMap D W s Real.tanh x)
    (hy : y = stepMap D W s' Real.tanh y) :
    y - x = D *ᵥ (y - x) + W *ᵥ (fun j => Real.tanh (y j) - Real.tanh (x j)) + (s' - s) := by
  have e : (fun j => Real.tanh (y j) - Real.tanh (x j)) =
      (fun j => Real.tanh (y j)) - fun j => Real.tanh (x j) := rfl
  rw [e, Matrix.mulVec_sub, Matrix.mulVec_sub]
  conv_lhs => rw [hx, hy]
  unfold stepMap
  abel

/-- **P6（平衡点对激发 Lipschitz）**：`‖r*(s') − r*(s)‖ ≤ lipC · ‖s' − s‖`。 -/
theorem P6_lipschitz (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hM : CommonWeight (fun _ => D) (fun _ => W) v c) {s s' x y : Fin n → ℝ}
    (hx : x = stepMap D W s Real.tanh x) (hy : y = stepMap D W s' Real.tanh y) :
    ‖y - x‖ ≤ lipC v c * ‖s' - s‖ := by
  refine norm_le_of_resolvent hv hc1 hM fun i => ?_
  have hi := congrFun (eq_diff hx hy) i
  simp only [Pi.add_apply, Pi.sub_apply] at hi ⊢
  rw [hi]
  refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (abs_add_le _ _).trans ?_
  rw [← Finset.sum_add_distrib.symm.trans (Finset.sum_congr rfl fun j _ => (add_mul _ _ _).symm)]
  refine add_le_add ((abs_mulVec_le D _ i)) ((abs_mulVec_le W _ i).trans
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_tanh_sub_le _ _)
      (abs_nonneg _))) |>.trans (le_of_eq ?_)
  simp [Pi.sub_apply]

lemma rowSumLe_total (A : Matrix (Fin n) (Fin n) ℝ) : RowSumLe A (∑ i, ∑ j, |A i j|) :=
  fun i => Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

lemma total_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ ∑ i, ∑ j, |A i j| :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **P6（输入-响应增益）**。P2 条件下，平衡点映射 `s ↦ r*(s)` 在每一点可微，
导数为 `G = (I − D − W diag(sech² r*))⁻¹`。 -/
theorem P6_gain (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hM : CommonWeight (fun _ => D) (fun _ => W) v c)
    (rs : (Fin n → ℝ) → Fin n → ℝ) (hrs : ∀ s, rs s = stepMap D W s Real.tanh (rs s))
    (s : Fin n → ℝ) :
    HasFDerivAt rs (Matrix.toLin' (1 - linJ D W (rs s))⁻¹).toContinuousLinearMap s := by
  set x := rs s with hxdef
  set J := linJ D W x
  set G := (1 - J)⁻¹
  have hdet := P6_invertible hv hc1 hM x
  set L := lipC v c
  set aG := ∑ i, ∑ j, |G i j|
  set aW := ∑ i, ∑ j, |W i j|
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun h : Fin n → ℝ => ‖h‖ ^ 2) ?_
    (isLittleO_norm_pow_id (by norm_num : 1 < 2))
  refine IsBigO.of_bound (aG * (aW * (2 * L ^ 2))) (Eventually.of_forall fun h => ?_)
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, norm_pow, norm_norm]
  set y := rs (s + h)
  have hlip : ‖y - x‖ ≤ L * ‖h‖ := by
    simpa using P6_lipschitz hv hc1 hM (hrs s) (hrs (s + h))
  set Δ := y - x with hΔ
  set e : Fin n → ℝ := fun j => Real.tanh (y j) - Real.tanh (x j) - sech2 (x j) * Δ j
  have he : ‖e‖ ≤ 2 * ‖Δ‖ ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    have := tanh_taylor2 (x j) (Δ j)
    rw [show x j + Δ j = y j by simp [Δ]] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have hj : |Δ j| ≤ ‖Δ‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm Δ j
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hj 2
  have hd := eq_diff (hrs s) (hrs (s + h))
  rw [← hxdef] at hd
  have hsplit : (fun j => Real.tanh (y j) - Real.tanh (x j)) =
      (fun j => sech2 (x j) * Δ j) + e := by
    funext j; simp only [Pi.add_apply, e]; ring
  rw [hsplit, Matrix.mulVec_add, add_sub_cancel_left] at hd
  have hJ : (1 - J) *ᵥ Δ = W *ᵥ e + h := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, linJ_mulVec]
    calc Δ - (D *ᵥ Δ + W *ᵥ fun j => sech2 (x j) * Δ j)
        = D *ᵥ Δ + ((W *ᵥ fun j => sech2 (x j) * Δ j) + W *ᵥ e) + h -
            (D *ᵥ Δ + W *ᵥ fun j => sech2 (x j) * Δ j) := by rw [← hd]
      _ = W *ᵥ e + h := by abel
  have hG : Δ = G *ᵥ (W *ᵥ e) + G *ᵥ h := by
    have := congrArg (G *ᵥ ·) hJ
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec, Matrix.mulVec_add] at this
  rw [hG, add_sub_cancel_right]
  calc ‖G *ᵥ (W *ᵥ e)‖ ≤ aG * ‖W *ᵥ e‖ := norm_mulVec_le (total_nonneg G) (rowSumLe_total G) _
    _ ≤ aG * (aW * ‖e‖) := mul_le_mul_of_nonneg_left
        (norm_mulVec_le (total_nonneg W) (rowSumLe_total W) _) (total_nonneg G)
    _ ≤ aG * (aW * (2 * (L * ‖h‖) ^ 2)) := by
        gcongr
        exact he.trans (by gcongr)
    _ = aG * (aW * (2 * L ^ 2)) * ‖h‖ ^ 2 := by ring

/-- 选择函数存在：P2 条件下 `s ↦ r*(s)` 良定义。 -/
theorem P6_equilibrium_map (hv : ∀ i, 0 < v i) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hM : CommonWeight (fun _ => D) (fun _ => W) v c) :
    ∃ rs : (Fin n → ℝ) → Fin n → ℝ, ∀ s, rs s = stepMap D W s Real.tanh (rs s) :=
  ⟨fun s => (P2_exists_equilibrium abs_tanh_sub_le hv hc0 hc1 hM (s := s)).choose,
    fun s => (P2_exists_equilibrium abs_tanh_sub_le hv hc0 hc1 hM (s := s)).choose_spec⟩

end Gain

/-! ## 切换反例（实验报告 P6；草案 P1/P2 的配套）

两个矩阵单独都只有特征值 0.3，交替切换下线性方程发散；P2 的公共权重判据拒绝认证（需要 c ≥ 3.3）；
饱和方程在任意切换下有界（P1）。
-/

section Switching

open Filter Matrix

/-- 切换反例的两个矩阵（报告 `k_ripple_field_revision_20261118` 的 P6 切换）。 -/
noncomputable def swA1 : Matrix (Fin 2) (Fin 2) ℝ := !![3/10, 3; 0, 3/10]
noncomputable def swA2 : Matrix (Fin 2) (Fin 2) ℝ := !![3/10, 0; 3, 3/10]
/-- 拆成 `A = D + W`，`D = 0.3 I`。 -/
noncomputable def swD : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal fun _ => 3/10
def swW1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 3; 0, 0]
def swW2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 3, 0]

lemma sw_split : swA1 = swD + swW1 ∧ swA2 = swD + swW2 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [swA1, swA2, swD, swW1, swW2]

/-- 每个矩阵单独看都稳定：唯一特征值 0.3（`A − 0.3 I` 幂零）。 -/
theorem SW_single_eigen :
    (swA1 - (3/10 : ℝ) • 1) ^ 2 = 0 ∧ (swA2 - (3/10 : ℝ) • 1) ^ 2 = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [swA1, swA2, sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- 线性交替切换发散：从 (1,1) 出发，`r(2k)` 第二分量 ≥ 9ᵏ。 -/
theorem SW_linear_diverges (r : ℕ → Fin 2 → ℝ)
    (hr : ∀ t, r (t + 1) = (if t % 2 = 0 then swA1 else swA2) *ᵥ r t)
    (h0 : r 0 = ![1, 1]) :
    (∀ k, 0 ≤ r (2 * k) 0 ∧ 9 ^ k ≤ r (2 * k) 1) ∧ ∀ B : ℝ, ∃ t, B < ‖r t‖ := by
  have hstep : ∀ k, r (2 * k + 2) = swA2 *ᵥ (swA1 *ᵥ r (2 * k)) := by
    intro k
    rw [hr (2 * k + 1), hr (2 * k)]
    simp [Nat.mul_mod_right, Nat.add_mod]
  have hk : ∀ k, 0 ≤ r (2 * k) 0 ∧ 9 ^ k ≤ r (2 * k) 1 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have e := hstep k
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, e]
      simp only [swA1, swA2, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      have : (0:ℝ) ≤ 9 ^ k := by positivity
      constructor
      · nlinarith
      · rw [pow_succ]; nlinarith
  refine ⟨hk, fun B => ?_⟩
  obtain ⟨k, hk9⟩ := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 9)).eventually_gt_atTop B
    |>.exists
  refine ⟨2 * k, hk9.trans_le ((hk k).2.trans ?_)⟩
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (r (2 * k)) 1)

/-- P2 的公共权重判据正确地拒绝认证：任何公共权重都要求 c ≥ 3.3。 -/
theorem SW_no_common_weight {v : Fin 2 → ℝ} {c : ℝ} (hv : ∀ i, 0 < v i)
    (hM : CommonWeight (fun _ => swD) (fun t => if t % 2 = 0 then swW1 else swW2) v c) :
    33 / 10 ≤ c := by
  have h1 := hM 0 0
  have h2 := hM 1 1
  simp [swD, swW1, swW2, Fin.sum_univ_two, Matrix.diagonal] at h1 h2
  have := hv 0
  have := hv 1
  nlinarith

/-- 饱和版在任意切换下有界（P1）：`‖r t‖ ≤ 0.3ᵗ‖r 0‖ + 3(1 − 0.3ᵗ)/0.7`。 -/
theorem SW_saturated_bounded (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (hW : ∀ t, W t = swW1 ∨ W t = swW2) (r : ℕ → Fin 2 → ℝ)
    (hr : ∀ t, r (t + 1) = swD *ᵥ r t + W t *ᵥ (fun i => Real.tanh (r t i))) (t : ℕ) :
    ‖r t‖ ≤ (3/10) ^ t * ‖r 0‖ + 3 * (1 - (3/10) ^ t) / (1 - 3/10) := by
  have hb := P1_global_bound_tanh (fun _ => swD) W (fun _ => 0) r (d := 3/10) (w := 3) (S := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ => rowSumLe_diagonal fun _ => by norm_num)
    (fun t i => by
      rcases hW t with h | h <;> rw [h] <;> fin_cases i <;>
        simp [swW1, swW2, Fin.sum_univ_two])
    (fun _ => by simp) (fun t => by simp [hr t]) t
  simpa using hb

end Switching

/-! ## 补缺口

* P6 协作网络：D、W ≥ 0 时 0 ≤ G ≤ (I − D − W)⁻¹。
* P3 K = 1：全局收敛到 0，且慢于任何几何速率。
* P3 K > 1：d ≥ 0 时吸引域按初值符号划分；d < 0 时该论断不成立（反例）。
* P5 噪声：最小二乘误差恒等式；对角方向 Gram 二次型 ≤ Σx⁶。
-/

section Cooperative

open Matrix

variable {n : ℕ}

/-- 逆正性（加权极小值原理）：J ≥ 0、Jv ≤ cv、c < 1 时，`(I − J)x ≥ 0 ⇒ x ≥ 0`。 -/
lemma nonneg_of_resolvent {J : Matrix (Fin n) (Fin n) ℝ} {v x : Fin n → ℝ} {c : ℝ}
    (hJ : ∀ i j, 0 ≤ J i j) (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hJv : ∀ i, ∑ j, J i j * v j ≤ c * v i) (hx : ∀ i, 0 ≤ ((1 - J) *ᵥ x) i) :
    ∀ i, 0 ≤ x i := by
  intro i
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun j => x j / v j)
    ⟨i, Finset.mem_univ i⟩
  set m := x k / v k
  have hxj : ∀ j, m * v j ≤ x j := fun j => by
    have := hk j (Finset.mem_univ j)
    rwa [le_div_iff₀ (hv j)] at this
  have hkk : x k = m * v k := (div_mul_cancel₀ _ (hv k).ne').symm
  suffices hm : 0 ≤ m from (mul_nonneg hm (hv i).le).trans (hxj i)
  by_contra hneg
  rw [not_le] at hneg
  have h1 : ∑ j, J k j * x j ≤ x k := by
    have := hx k
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_nonneg] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have h2 : m * ∑ j, J k j * v j ≤ ∑ j, J k j * x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by nlinarith [hJ k j, hxj j]
  have h3 : m * (c * v k) ≤ m * ∑ j, J k j * v j :=
    mul_le_mul_of_nonpos_left (hJv k) hneg.le
  have hneg' : m * v k * (1 - c) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (hv k)) (by linarith)
  linarith

lemma det_one_sub_ne_zero {A M : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {c : ℝ}
    (hA : ∀ i j, |A i j| ≤ M i j) (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hMv : ∀ i, ∑ j, M i j * v j ≤ c * v i) : (1 - A).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
  have hMn : ∀ i j, 0 ≤ M i j := fun i j => (abs_nonneg _).trans (hA i j)
  have hb := weighted_resolvent (M := M) (x := z) (β := 0) hMn hv hc1 hMv fun i => by
      rw [zero_mul, add_zero]
      calc |z i| = |(A *ᵥ z) i| := by rw [← hz]
        _ ≤ ∑ j, |A i j| * |z j| := abs_mulVec_le _ _ i
        _ ≤ _ := by gcongr with j; exact hA i j
  exact hz0 (funext fun i => abs_nonpos_iff.1 (by simpa using hb i))

lemma inv_entry_nonneg {J : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {c : ℝ}
    (hJ : ∀ i j, 0 ≤ J i j) (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hJv : ∀ i, ∑ j, J i j * v j ≤ c * v i) : ∀ i j, 0 ≤ (1 - J)⁻¹ i j := by
  have hdet := det_one_sub_ne_zero (A := J) (M := J)
    (fun i j => (abs_of_nonneg (hJ i j)).le) hv hc1 hJv
  intro i j
  have hcol : (1 - J)⁻¹ *ᵥ Pi.single j 1 = fun i => (1 - J)⁻¹ i j := by
    funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h := nonneg_of_resolvent (x := (1 - J)⁻¹ *ᵥ Pi.single j 1) hJ hv hc1 hJv fun i => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  simpa [hcol] using h i

variable {D W : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {c : ℝ}

/-- **P6（协作网络）**：D、W ≥ 0 时 `0 ≤ G ≤ (I − D − W)⁻¹` 逐元素——饱和只会降低增益。 -/
theorem P6_cooperative (hv : ∀ i, 0 < v i) (hc1 : c < 1)
    (hM : CommonWeight (fun _ => D) (fun _ => W) v c)
    (hD : ∀ i j, 0 ≤ D i j) (hW : ∀ i j, 0 ≤ W i j) (x : Fin n → ℝ) :
    ∀ i j, 0 ≤ (1 - linJ D W x)⁻¹ i j ∧ (1 - linJ D W x)⁻¹ i j ≤ (1 - (D + W))⁻¹ i j := by
  set J := linJ D W x
  set M := D + W
  have hJe : ∀ i j, J i j = D i j + W i j * sech2 (x j) := fun i j => by
    simp [J, linJ, Matrix.mul_diagonal]
  have hJ0 : ∀ i j, 0 ≤ J i j := fun i j => by
    rw [hJe]; exact add_nonneg (hD i j) (mul_nonneg (hW i j) (sech2_nonneg _))
  have hJM : ∀ i j, J i j ≤ M i j := fun i j => by
    rw [hJe]
    simp only [M, Matrix.add_apply]
    exact add_le_add le_rfl (mul_le_of_le_one_right (hW i j) (sech2_le_one _))
  have hM0 : ∀ i j, 0 ≤ M i j := fun i j => add_nonneg (hD i j) (hW i j)
  have hMv : ∀ i, ∑ j, M i j * v j ≤ c * v i := fun i => by
    have := hM 0 i
    simpa [M, abs_of_nonneg (hD _ _), abs_of_nonneg (hW _ _)] using this
  have hJv : ∀ i, ∑ j, J i j * v j ≤ c * v i := fun i =>
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hJM i j) (hv j).le).trans (hMv i)
  have hdJ := det_one_sub_ne_zero (A := J) (M := J)
    (fun i j => (abs_of_nonneg (hJ0 i j)).le) hv hc1 hJv
  have hdM := det_one_sub_ne_zero (A := M) (M := M)
    (fun i j => (abs_of_nonneg (hM0 i j)).le) hv hc1 hMv
  have hGJ := inv_entry_nonneg hJ0 hv hc1 hJv
  have hGM := inv_entry_nonneg hM0 hv hc1 hMv
  have hres : (1 - M)⁻¹ - (1 - J)⁻¹ = (1 - M)⁻¹ * (M - J) * (1 - J)⁻¹ := by
    have e : M - J = (1 - J) - (1 - M) := by abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdM),
      Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdJ),
      Matrix.mul_one]
  intro i j
  refine ⟨hGJ i j, ?_⟩
  have h := congrFun (congrFun hres i) j
  rw [Matrix.sub_apply] at h
  have : 0 ≤ ((1 - M)⁻¹ * (M - J) * (1 - J)⁻¹) i j := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Finset.sum_nonneg fun l _ =>
      mul_nonneg (hGM i l) (by rw [Matrix.sub_apply]; linarith [hJM l k])) (hGJ k j)
  linarith

end Cooperative

section ScalarGlobal

open Filter Topology Set

lemma tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x :=
  lt_trans (by positivity) (div_cosh_sq_lt_tanh hx)

lemma tanh_lt_self {x : ℝ} (hx : 0 < x) : Real.tanh x < x := by
  have h := tanh_div_strictAnti (show x / 2 ∈ Ioi (0:ℝ) by simp; linarith)
    (show x ∈ Ioi (0:ℝ) from hx) (by linarith)
  have h2 : Real.tanh (x / 2) / (x / 2) ≤ 1 :=
    div_le_one_of_le₀ (tanh_bounds_pos (by linarith)).2 (by linarith)
  have := h.trans_le h2
  rwa [div_lt_one hx] at this

lemma tanh_strictMono : StrictMono Real.tanh :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_tanh x).deriv]; positivity

lemma scalarMap_neg (d w x : ℝ) : scalarMap d w (-x) = -scalarMap d w x := by
  simp only [scalarMap, Real.tanh_neg]; ring

lemma iterate_scalarMap_neg (d w x : ℝ) (t : ℕ) :
    (scalarMap d w)^[t] (-x) = -(scalarMap d w)^[t] x := by
  induction t with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, scalarMap_neg]

lemma continuous_scalarMap (d w : ℝ) : Continuous (scalarMap d w) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_scalarMap d w x).continuousAt

/-- 收敛序列 `u(t+1) = g(u t)` 的极限是 g 的不动点。 -/
lemma fixed_of_tendsto {g : ℝ → ℝ} (hg : Continuous g) {u : ℕ → ℝ} {L : ℝ}
    (hu : Tendsto u atTop (𝓝 L)) (hs : ∀ t, u (t + 1) = g (u t)) : g L = L :=
  tendsto_nhds_unique (((hg.tendsto L).comp hu).congr fun t => (hs t).symm)
    (hu.comp (tendsto_add_atTop_nat 1))

/-- K = 1：任意 x ≠ 0 都有 `|f x| < |x|`（全局，不只局部）。 -/
theorem P3_K1_contract {d w : ℝ} (hd : |d| < 1) (hK : d + w = 1) {x : ℝ} (hx : x ≠ 0) :
    |scalarMap d w x| < |x| := by
  obtain ⟨hd1, hd2⟩ := abs_lt.1 hd
  have hw : 0 < w := by linarith
  have pos : ∀ y, 0 < y → |scalarMap d w y| < |y| := fun y hy => by
    have h1 := mul_lt_mul_of_pos_left (tanh_lt_self hy) hw
    have h2 := mul_pos hw (tanh_pos_of_pos hy)
    rw [abs_of_pos hy, abs_lt]
    unfold scalarMap
    constructor <;> nlinarith
  rcases hx.lt_or_gt with h | h
  · have := pos (-x) (by linarith)
    rwa [scalarMap_neg, abs_neg, abs_neg] at this
  · exact pos x h

lemma abs_scalarMap_abs (d w x : ℝ) : |scalarMap d w x| = |scalarMap d w (|x|)| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, scalarMap_neg, abs_neg]

/-- **P3（K = 1，全局收敛）**：任意初值的轨道都收敛到 0。 -/
theorem P3_K1_converges {d w : ℝ} (hd : |d| < 1) (hK : d + w = 1) (x₀ : ℝ) :
    Tendsto (fun t => (scalarMap d w)^[t] x₀) atTop (𝓝 0) := by
  set x := fun t => (scalarMap d w)^[t] x₀
  set a := fun t => |x t|
  have hs : ∀ t, a (t + 1) = |scalarMap d w (a t)| := fun t => by
    simp only [a, x, Function.iterate_succ_apply']
    exact abs_scalarMap_abs d w _
  have hle : ∀ y, |scalarMap d w y| ≤ |y| := fun y => by
    rcases eq_or_ne y 0 with h | h
    · simp [h, scalarMap]
    · exact (P3_K1_contract hd hK h).le
  have hanti : Antitone a := antitone_nat_of_succ_le fun t => by
    simp only [a, x, Function.iterate_succ_apply']; exact hle _
  have hbdd : BddBelow (range a) := ⟨0, by rintro _ ⟨t, rfl⟩; exact abs_nonneg _⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t, a t
  have hL0 : 0 ≤ L := le_ciInf fun t => abs_nonneg _
  have hfix := fixed_of_tendsto ((continuous_scalarMap d w).abs) hlim hs
  have hL : L = 0 := by
    by_contra hne
    have := P3_K1_contract hd hK hne
    rw [hfix, abs_of_nonneg hL0] at this
    exact lt_irrefl _ this
  rw [hL] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using hlim

/-- **P3（K = 1，慢于任何几何速率）**：对任意 q < 1，最终 `|x(t+1)| ≥ q |x(t)|`。 -/
theorem P3_K1_slow {d w : ℝ} (hd : |d| < 1) (hK : d + w = 1) (x₀ : ℝ) {q : ℝ} (hq : q < 1) :
    ∀ᶠ t in atTop, q * |(scalarMap d w)^[t] x₀| ≤ |(scalarMap d w)^[t + 1] x₀| := by
  have hx := P3_K1_converges hd hK x₀
  have hsmall : Tendsto (fun t => |w| * |(scalarMap d w)^[t] x₀| ^ 2) atTop (𝓝 0) := by
    simpa using ((hx.abs).pow 2).const_mul |w|
  filter_upwards [hsmall.eventually (gt_mem_nhds (by linarith : (0:ℝ) < 1 - q))] with t ht
  set y := (scalarMap d w)^[t] x₀
  rw [Function.iterate_succ_apply']
  have hr := scalar_residual d w y
  rw [hK, one_mul] at hr
  have h1 : |y| - |w| * |y| ^ 3 ≤ |scalarMap d w y| := by
    have := abs_sub_abs_le_abs_sub y (scalarMap d w y)
    rw [abs_sub_comm] at this
    linarith
  have hy0 := abs_nonneg y
  nlinarith [mul_le_mul_of_nonneg_left ht.le hy0]

/-- **P3（K > 1，d ≥ 0：按初值符号的吸引域）**。 -/
theorem P3_basin {d w : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) (hK : 1 < d + w) :
    ∃ p, 0 < p ∧ scalarMap d w p = p ∧
      (∀ x₀, 0 < x₀ → Tendsto (fun t => (scalarMap d w)^[t] x₀) atTop (𝓝 p)) ∧
      (∀ x₀, x₀ < 0 → Tendsto (fun t => (scalarMap d w)^[t] x₀) atTop (𝓝 (-p))) := by
  have hd : |d| < 1 := abs_lt.2 ⟨by linarith, hd1⟩
  obtain ⟨p, hp0, hfp, -, -, -⟩ := P3_bistable hd hK
  have hw : 0 < w := by linarith
  set f := scalarMap d w
  have hmono : Monotone f := fun x y hxy => by
    simp only [f, scalarMap]
    have := tanh_strictMono.monotone hxy
    nlinarith
  -- 正半轴上 f x − x 的符号由 tanh x / x 与 tanh p / p 的大小决定
  have hφp : w * (Real.tanh p / p) = 1 - d := by
    have : d * p + w * Real.tanh p = p := hfp
    field_simp; linarith
  have key : ∀ x, 0 < x → (f x - x) = x * (w * (Real.tanh x / x) - w * (Real.tanh p / p)) := by
    intro x hx
    rw [hφp]; simp only [f, scalarMap]; field_simp; ring
  have below : ∀ x, 0 < x → x ≤ p → x ≤ f x := fun x hx hxp => by
    have h : Real.tanh p / p ≤ Real.tanh x / x :=
      tanh_div_strictAnti.antitoneOn (show x ∈ Ioi (0:ℝ) from hx) (show p ∈ Ioi (0:ℝ) from hp0) hxp
    have := key x hx
    nlinarith [mul_le_mul_of_nonneg_left h hw.le]
  have above : ∀ x, p ≤ x → f x ≤ x := fun x hxp => by
    have hx : 0 < x := lt_of_lt_of_le hp0 hxp
    have h : Real.tanh x / x ≤ Real.tanh p / p :=
      tanh_div_strictAnti.antitoneOn (show p ∈ Ioi (0:ℝ) from hp0) (show x ∈ Ioi (0:ℝ) from hx) hxp
    have := key x hx
    nlinarith [mul_le_mul_of_nonneg_left h hw.le]
  have uniq : ∀ L, 0 < L → f L = L → L = p := fun L hL hfL => by
    have := key L hL
    rw [hfL, sub_self] at this
    have h2 : Real.tanh L / L = Real.tanh p / p := by
      have := (mul_eq_zero.1 this.symm).resolve_left hL.ne'
      have : w * (Real.tanh L / L) = w * (Real.tanh p / p) := by linarith
      exact mul_left_cancel₀ hw.ne' this
    exact tanh_div_strictAnti.injOn (show L ∈ Ioi (0:ℝ) from hL) (show p ∈ Ioi (0:ℝ) from hp0) h2
  have hs : ∀ x₀ : ℝ, ∀ t, (fun t => f^[t] x₀) (t + 1) = f ((fun t => f^[t] x₀) t) :=
    fun x₀ t => Function.iterate_succ_apply' f t x₀
  have pos : ∀ x₀, 0 < x₀ → Tendsto (fun t => f^[t] x₀) atTop (𝓝 p) := by
    intro x₀ hx₀
    rcases le_total x₀ p with hle | hge
    · have inv : ∀ t, 0 < f^[t] x₀ ∧ f^[t] x₀ ≤ p := by
        intro t
        induction t with
        | zero => exact ⟨hx₀, hle⟩
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact ⟨lt_of_lt_of_le ih.1 (below _ ih.1 ih.2), hfp ▸ hmono ih.2⟩
      have hm : Monotone fun t => f^[t] x₀ := monotone_nat_of_le_succ fun t => by
        rw [Function.iterate_succ_apply']; exact below _ (inv t).1 (inv t).2
      have hlim := tendsto_atTop_ciSup hm ⟨p, by rintro _ ⟨t, rfl⟩; exact (inv t).2⟩
      have hL : 0 < ⨆ t, f^[t] x₀ := lt_of_lt_of_le hx₀
        (le_ciSup (f := fun t => f^[t] x₀) ⟨p, by rintro _ ⟨t, rfl⟩; exact (inv t).2⟩ 0)
      rwa [uniq _ hL (fixed_of_tendsto (continuous_scalarMap d w) hlim (hs x₀))] at hlim
    · have inv : ∀ t, p ≤ f^[t] x₀ := by
        intro t
        induction t with
        | zero => exact hge
        | succ k ih => rw [Function.iterate_succ_apply']; exact hfp ▸ hmono ih
      have ha : Antitone fun t => f^[t] x₀ := antitone_nat_of_succ_le fun t => by
        rw [Function.iterate_succ_apply']; exact above _ (inv t)
      have hlim := tendsto_atTop_ciInf ha ⟨p, by rintro _ ⟨t, rfl⟩; exact inv t⟩
      have hL : 0 < ⨅ t, f^[t] x₀ := lt_of_lt_of_le hp0 (le_ciInf inv)
      rwa [uniq _ hL (fixed_of_tendsto (continuous_scalarMap d w) hlim (hs x₀))] at hlim
  refine ⟨p, hp0, hfp, pos, fun x₀ hx₀ => ?_⟩
  have := (pos (-x₀) (by linarith)).neg
  refine this.congr fun t => ?_
  simp only [f]
  rw [← neg_neg x₀, iterate_scalarMap_neg, neg_neg, neg_neg]

/-- d < 0 时"按初值符号决定吸引域"不成立：d = −0.9、w = 2（K = 1.1）时正初值 10 一步变负。 -/
theorem P3_basin_fails_neg_d :
    |(-9/10 : ℝ)| < 1 ∧ 1 < (-9/10 : ℝ) + 2 ∧ scalarMap (-9/10) 2 10 < 0 := by
  refine ⟨by norm_num [abs_of_neg], by norm_num, ?_⟩
  have := (abs_lt.1 (Real.abs_tanh_lt_one 10)).2
  simp only [scalarMap]
  linarith

end ScalarGlobal

section NoiseAlgebra

open Matrix

variable {T p : Type*} [Fintype T] [Fintype p] [DecidableEq p]

/-- **P5（噪声误差恒等式）**：`y = Zθ + ε` 时最小二乘误差恰为 `(ZᵀZ)⁻¹Zᵀε`。 -/
theorem P5_ols_error (Z : Matrix T p ℝ) (hdet : (Zᵀ * Z).det ≠ 0) (θ : p → ℝ) (ε : T → ℝ) :
    (Zᵀ * Z)⁻¹ *ᵥ (Zᵀ *ᵥ (Z *ᵥ θ + ε)) - θ = (Zᵀ * Z)⁻¹ *ᵥ (Zᵀ *ᵥ ε) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_add, P5_ols_exact Z hdet θ, add_sub_cancel_left]

omit [DecidableEq p] in
/-- **P5（对角方向病态的定量形式）**：回归量取 `[x, tanh x]` 时，Gram 矩阵沿 (1, −1)
的二次型 ≤ Σ x⁶，所以小幅度下该方向的信息量是六阶小量。 -/
theorem P5_diag_gram (x : T → ℝ) :
    let Z : Matrix T (Fin 2) ℝ := Matrix.of fun t k => ![x t, Real.tanh (x t)] k
    ![1, -1] ⬝ᵥ ((Zᵀ * Z) *ᵥ ![1, -1]) ≤ ∑ t, x t ^ 6 := by
  intro Z
  rw [gram_quad]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Z, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  refine Finset.sum_le_sum fun t _ => ?_
  have h := abs_tanh_sub_self_le (x t)
  have h0 : 0 ≤ |Real.tanh (x t) - x t| := abs_nonneg _
  have : (x t * 1 + Real.tanh (x t) * -1) * (x t * 1 + Real.tanh (x t) * -1) =
      |Real.tanh (x t) - x t| ^ 2 := by rw [sq_abs]; ring
  rw [this, show x t ^ 6 = (|x t| ^ 3) ^ 2 by rw [← pow_mul, pow_abs]; simp [abs_pow, Even.pow_abs ⟨3, rfl⟩]]
  exact pow_le_pow_left₀ h0 h 2

end NoiseAlgebra


section CriticalRate

open Filter Topology Set Finset

/-- 三阶上界：x ≥ 0 时 `x − tanh x ≤ x³/3`。 -/
lemma tanh_cubic_upper {x : ℝ} (hx : 0 ≤ x) : x - Real.tanh x ≤ x ^ 3 / 3 := by
  set g := fun y : ℝ => Real.tanh y - y + y ^ 3 / 3
  have hg : ∀ y, HasDerivAt g (y ^ 2 - Real.tanh y ^ 2) y := fun y => by
    have h := ((hasDerivAt_tanh y).sub (hasDerivAt_id' y)).add ((hasDerivAt_pow 3 y).div_const 3)
    rw [one_div_cosh_sq] at h
    convert h using 1; norm_num; ring
  have hmono : Monotone g := monotone_of_deriv_nonneg (fun y => (hg y).differentiableAt)
    fun y => by
      rw [(hg y).deriv, sub_nonneg, ← sq_abs, ← sq_abs y]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_tanh_le_abs y) 2
  have := hmono hx
  simp only [g, Real.tanh_zero] at this
  linarith

lemma tanh_sq_lower (y : ℝ) : y ^ 2 - 2 / 3 * y ^ 4 ≤ Real.tanh y ^ 2 := by
  have pos : ∀ z : ℝ, 0 ≤ z → z ^ 2 - 2 / 3 * z ^ 4 ≤ Real.tanh z ^ 2 := fun z hz => by
    have hu := tanh_cubic_upper hz
    rcases le_or_gt (z ^ 2) 3 with h | h
    · have h0 : 0 ≤ z - z ^ 3 / 3 := by nlinarith
      have h1 : z - z ^ 3 / 3 ≤ Real.tanh z := by linarith
      nlinarith [mul_le_mul h1 h1 h0 (h0.trans h1), pow_two_nonneg (z ^ 3)]
    · nlinarith [sq_nonneg (Real.tanh z)]
  rcases le_or_gt 0 y with h | h
  · exact pos y h
  · have := pos (-y) (by linarith)
    rwa [Real.tanh_neg, neg_sq, neg_sq, show (-y) ^ 4 = y ^ 4 by ring] at this

/-- 五阶下界：x ≥ 0 时 `x³/3 − 2x⁵/15 ≤ x − tanh x`。 -/
lemma tanh_quintic_lower {x : ℝ} (hx : 0 ≤ x) : x ^ 3 / 3 - 2 * x ^ 5 / 15 ≤ x - Real.tanh x := by
  set h := fun y : ℝ => y - Real.tanh y - y ^ 3 / 3 + 2 * y ^ 5 / 15
  have hh : ∀ y, HasDerivAt h (Real.tanh y ^ 2 - y ^ 2 + 2 / 3 * y ^ 4) y := fun y => by
    have e := (((hasDerivAt_id' y).sub (hasDerivAt_tanh y)).sub
      ((hasDerivAt_pow 3 y).div_const 3)).add (((hasDerivAt_pow 5 y).const_mul 2).div_const 15)
    rw [one_div_cosh_sq] at e
    convert e using 1; norm_num; ring
  have hmono : Monotone h := monotone_of_deriv_nonneg (fun y => (hh y).differentiableAt)
    fun y => by rw [(hh y).deriv]; linarith [tanh_sq_lower y]
  have := hmono hx
  simp only [h, Real.tanh_zero] at this
  linarith

/-- **P3（K = 1，精确临界慢化）**：只要轨道不恰好落到 0，`t · x(t)² → 3/(2w)`，
即 `|x(t)| ≈ √(3/(2w t))`。 -/
theorem P3_K1_rate {d w : ℝ} (hd : |d| < 1) (hK : d + w = 1) (x₀ : ℝ)
    (hne : ∀ t, (scalarMap d w)^[t] x₀ ≠ 0) :
    Tendsto (fun t : ℕ => (t : ℝ) * ((scalarMap d w)^[t] x₀) ^ 2) atTop (𝓝 (3 / (2 * w))) := by
  have hw : 0 < w := by linarith [(abs_lt.1 hd).2]
  set x := fun t => (scalarMap d w)^[t] x₀
  set a := fun t => |x t|
  have ha0 : ∀ t, 0 < a t := fun t => abs_pos.2 (hne t)
  have has : ∀ t, a (t + 1) = |scalarMap d w (a t)| := fun t => by
    simp only [a, x, Function.iterate_succ_apply']
    exact abs_scalarMap_abs d w _
  have hlim_a : Tendsto a atTop (𝓝 0) := by
    simpa using (P3_K1_converges hd hK x₀).abs
  have hxa : ∀ t, x t ^ 2 = a t ^ 2 := fun t => (sq_abs _).symm
  clear_value a
  set s := fun t => (a t - Real.tanh (a t)) / a t ^ 3
  have hs_up : ∀ t, s t ≤ 1 / 3 := fun t => by
    have := tanh_cubic_upper (ha0 t).le
    simp only [s]; rw [div_le_iff₀ (pow_pos (ha0 t) 3)]; linarith
  have hs_lo : ∀ t, 1 / 3 - 2 / 15 * a t ^ 2 ≤ s t := fun t => by
    have := tanh_quintic_lower (ha0 t).le
    simp only [s]; rw [le_div_iff₀ (pow_pos (ha0 t) 3)]; nlinarith
  have hlim_s : Tendsto s atTop (𝓝 (1 / 3)) := by
    have hl : Tendsto (fun t => 1 / 3 - 2 / 15 * a t ^ 2) atTop (𝓝 (1 / 3)) := by
      simpa using tendsto_const_nhds.sub ((hlim_a.pow 2).const_mul (2 / 15 : ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hs_lo hs_up
  have he_all : ∀ t, a t - Real.tanh (a t) = s t * a t ^ 3 := fun t => by
    simp only [s]; rw [div_mul_cancel₀ _ (pow_ne_zero 3 (ha0 t).ne')]
  clear_value s
  set u := fun t => 1 / a t ^ 2
  have hstep : ∀ t, u (t + 1) - u t =
      (2 * w * s t - w ^ 2 * s t ^ 2 * a t ^ 2) / (1 - w * s t * a t ^ 2) ^ 2 := fun t => by
    have hat := (ha0 t).ne'
    have he := he_all t
    have hf : scalarMap d w (a t) = a t * (1 - w * s t * a t ^ 2) := by
      have : d = 1 - w := by linarith
      simp only [scalarMap, this]; linear_combination (-w) * he
    have hq : 1 - w * s t * a t ^ 2 ≠ 0 := by
      intro h0
      have := (ha0 (t + 1)).ne'
      rw [has, hf, h0, mul_zero, abs_zero] at this
      exact this rfl
    simp only [u]
    rw [has, hf, abs_mul, mul_pow, sq_abs, sq_abs, eq_div_iff (pow_ne_zero 2 hq), sub_mul,
      one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hq), mul_one]
    field_simp
    ring
  have hlim_d : Tendsto (fun t => u (t + 1) - u t) atTop (𝓝 (2 * w / 3)) := by
    have := ((hlim_s.const_mul (2 * w)).sub (((hlim_s.pow 2).const_mul (w ^ 2)).mul
      (hlim_a.pow 2))).div ((tendsto_const_nhds (x := (1 : ℝ))).sub
        ((hlim_s.const_mul w).mul (hlim_a.pow 2)) |>.pow 2) (by norm_num)
    refine (this.congr fun t => (hstep t).symm).trans_eq ?_
    ring
  have hlim_u : Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * u t) atTop (𝓝 (2 * w / 3)) := by
    have hc := hlim_d.cesaro
    have h0 : Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * u 0) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (u 0)
    refine ((h0.add hc).congr fun t => ?_).trans_eq (by ring)
    rw [Finset.sum_range_sub (f := u)]; ring
  have hfin := hlim_u.inv₀ (by positivity)
  refine (hfin.congr fun t => ?_).trans_eq (by field_simp)
  simp only [u]
  rw [hxa, one_div, mul_inv, inv_inv, inv_inv]

/-- 推论（0 ≤ d < 1）：x₀ ≠ 0 时轨道永不为 0，故 `t x(t)² → 3/(2w)` 且
`√t · |x(t)| → √(3/(2w))`。 -/
theorem P3_K1_rate_pos {d w : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) (hK : d + w = 1) {x₀ : ℝ}
    (hx₀ : x₀ ≠ 0) :
    Tendsto (fun t : ℕ => (t : ℝ) * ((scalarMap d w)^[t] x₀) ^ 2) atTop (𝓝 (3 / (2 * w))) ∧
    Tendsto (fun t : ℕ => Real.sqrt t * |(scalarMap d w)^[t] x₀|) atTop
      (𝓝 (Real.sqrt (3 / (2 * w)))) := by
  have hd : |d| < 1 := abs_lt.2 ⟨by linarith, hd1⟩
  have hw : 0 < w := by linarith
  have hpos : ∀ y, 0 < y → 0 < scalarMap d w y := fun y hy => by
    have := tanh_pos_of_pos hy
    unfold scalarMap; positivity
  have hnz : ∀ y, y ≠ 0 → scalarMap d w y ≠ 0 := fun y hy => by
    rcases hy.lt_or_gt with h | h
    · have := hpos (-y) (by linarith)
      rw [scalarMap_neg] at this; linarith
    · exact (hpos y h).ne'
  have hne : ∀ t, (scalarMap d w)^[t] x₀ ≠ 0 := fun t => by
    induction t with
    | zero => exact hx₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact hnz _ ih
  have h1 := P3_K1_rate hd hK x₀ hne
  refine ⟨h1, (h1.sqrt).congr fun t => ?_⟩
  rw [Real.sqrt_mul (Nat.cast_nonneg t), Real.sqrt_sq_eq_abs]

end CriticalRate

end KRippleV2

#print axioms KRippleV2.P1_global_bound
#print axioms KRippleV2.P1_uniform_bound
#print axioms KRippleV2.P1_global_bound_tanh
#print axioms KRippleV2.rowSumLe_diagonal
#print axioms KRippleV2.P2_contraction
#print axioms KRippleV2.P2_exists_equilibrium
#print axioms KRippleV2.P2_unique_equilibrium
#print axioms KRippleV2.P2_global_attraction
#print axioms KRippleV2.P2_tanh
#print axioms KRippleV2.abs_tanh_sub_le
#print axioms KRippleV2.rho_lt_one_of_weight
#print axioms KRippleV2.weight_of_rho_lt_one
#print axioms KRippleV2.weight_iff_rho_lt_one
#print axioms KRippleV2.P2_tanh_of_rho
#print axioms KRippleV2.P3_deriv_zero
#print axioms KRippleV2.P3_local_contraction
#print axioms KRippleV2.P3_alternating_decay
#print axioms KRippleV2.P3_monotone_decay
#print axioms KRippleV2.P3_decoupled
#print axioms KRippleV2.P3_origin_unstable
#print axioms KRippleV2.P3_bistable
#print axioms KRippleV2.P3_period_two
#print axioms KRippleV2.P4_rho_le_rho_abs
#print axioms KRippleV2.P4_balanced_eq
#print axioms KRippleV2.P4_eta_le_one
#print axioms KRippleV2.P4_eta_balanced
#print axioms KRippleV2.P5_identifiable_iff
#print axioms KRippleV2.P5_ols_exact
#print axioms KRippleV2.P5_diag_separable
#print axioms KRippleV2.P5_diag_identify
#print axioms KRippleV2.P5_diag_weak
#print axioms KRippleV2.P5_kappa_identify
#print axioms KRippleV2.P6_invertible
#print axioms KRippleV2.P6_lipschitz
#print axioms KRippleV2.P6_gain
#print axioms KRippleV2.P6_equilibrium_map
#print axioms KRippleV2.SW_single_eigen
#print axioms KRippleV2.SW_linear_diverges
#print axioms KRippleV2.SW_no_common_weight
#print axioms KRippleV2.SW_saturated_bounded
#print axioms KRippleV2.P6_cooperative
#print axioms KRippleV2.P3_K1_contract
#print axioms KRippleV2.P3_K1_converges
#print axioms KRippleV2.P3_K1_slow
#print axioms KRippleV2.P3_basin
#print axioms KRippleV2.P3_basin_fails_neg_d
#print axioms KRippleV2.P5_ols_error
#print axioms KRippleV2.P5_diag_gram
#print axioms KRippleV2.P3_K1_rate
#print axioms KRippleV2.P3_K1_rate_pos
