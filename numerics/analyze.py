"""涟漪场方程 V2（饱和型、带符号、有向）的数值验证。

模型：r(t+1) = D r(t) + W tanh(r(t)) + s(t)
  r ∈ R^n 带符号不限区间；D 对角（保持-耗散）；W 带符号有向，不做行归一化。
每个检查对应 01_THEORY_CORE/K_RIPPLE_FIELD_EQUATION_V2_DRAFT.md 中的一条命题。
"""
import itertools
import json
import sys

import numpy as np
from scipy.stats import spearmanr

rng = np.random.default_rng(20261118)
rho = lambda A: float(max(abs(np.linalg.eigvals(A))))
step = lambda r, D, W, s: D @ r + W @ np.tanh(r) + s
out = {}

# P1 全局有界：||D||∞ = d < 1 时，limsup ||r||∞ ≤ (||W||∞ + S)/(1-d)，与初值、W 的谱无关；对时变 D、W 同样成立。
viol, worst = 0, 0.0
for _ in range(300):
    n = rng.integers(2, 12)
    d = rng.uniform(0, 0.95)
    T = 200
    Ds = [np.diag(rng.uniform(-d, d, n)) for _ in range(T)]
    Ws = [rng.normal(0, rng.uniform(0.1, 5), (n, n)) for _ in range(T)]
    ss = [rng.normal(0, 1, n) for _ in range(T)]
    w = max(np.abs(W).sum(1).max() for W in Ws)
    S = max(np.abs(s).max() for s in ss)
    r = rng.normal(0, 1e4, n)
    r0 = np.abs(r).max()
    for t in range(T):
        r = step(r, Ds[t], Ws[t], ss[t])
        bound = d ** (t + 1) * r0 + (w + S) * (1 - d ** (t + 1)) / (1 - d)
        worst = max(worst, np.abs(r).max() / bound)
        viol += np.abs(r).max() > bound * (1 + 1e-9)
cubic = [0.9 * x - 0.5 * x ** 3 for x in [2.5]]
x = 2.5
for _ in range(4):
    x = 0.9 * x - 0.5 * x ** 3
out["P1_global_bound"] = {"trials": 300, "violations": int(viol), "max_ratio_to_bound": round(worst, 4),
                          "contrast_cubic_r0_2.5_after_4_steps": float(f"{x:.3e}")}

# P2 全局收缩：rho(|D|+|W|) < 1 ⇒ 唯一平衡点，任意初值指数收敛。
fails, n_ok = 0, 0
for _ in range(300):
    n = rng.integers(2, 10)
    D = np.diag(rng.uniform(-0.6, 0.6, n))
    W = rng.normal(0, 1, (n, n))
    while rho(np.abs(D) + np.abs(W)) >= 0.97:
        W *= 0.9
    s = rng.normal(0, 2, n)
    ends = []
    for _ in range(5):
        r = rng.normal(0, 50, n)
        for _ in range(3000):
            r = step(r, D, W, s)
        ends.append(r)
    n_ok += 1
    fails += max(np.abs(e - ends[0]).max() for e in ends) > 1e-8
out["P2_contraction_unique_equilibrium"] = {"systems": n_ok, "non_unique": int(fails)}

# P3 标量相图：K := d + w 为线性增益（带符号、不限区间），决定形态。
def phase(d, w):
    rs = []
    for r0 in (0.3, -0.3, 3.0):
        r = r0
        for _ in range(4000):
            r = d * r + w * np.tanh(r)
        rs.append((r, d * r + w * np.tanh(r)))
    a = [abs(x) for x, _ in rs]
    if max(a) < 1e-6:
        return "decay"
    r, r1 = rs[0]
    if abs(r1 - r) < 1e-8:
        return "bistable_fixed" if np.sign(rs[0][0]) != np.sign(rs[1][0]) else "fixed"
    if abs(d * r1 + w * np.tanh(r1) - r) < 1e-8 and np.sign(r1) != np.sign(r):
        return "period2_oscillation"
    return "other"

grid = {}
mismatch = 0
for d in np.linspace(-0.8, 0.8, 9):
    for w in np.linspace(-3, 3, 25):
        K = d + w
        if abs(abs(K) - 1) < 0.05 or abs(d) + abs(w) < 1e-9:
            continue
        p = phase(d, w)
        expect = "decay" if abs(K) < 1 else ("bistable_fixed" if K > 1 else "period2_oscillation")
        # |K|<1 但 |d|+|w|>1 时只保证局部稳定，单独计数
        local_only = abs(K) < 1 and abs(d) + abs(w) >= 1
        key = "K<-1" if K < -1 else "-1<K<0" if K < 0 else "0<K<1" if K < 1 else "K>1"
        g = grid.setdefault(key, {"n": 0, "as_predicted": 0, "local_only_cases": 0, "local_only_deviate": 0})
        g["n"] += 1
        g["as_predicted"] += p == expect
        g["local_only_cases"] += local_only
        g["local_only_deviate"] += local_only and p != expect
        mismatch += (p != expect) and not local_only
out["P3_scalar_phase_by_K"] = {"cells": grid, "mismatch_outside_local_only": int(mismatch)}

# P3b 复数形态：D + W 的主特征值为 ρe^{iθ}。ρ>1 时饱和为不衰减的旋转（不变圈），每步转角≈θ。
rot = []
for theta in (0.3, 0.8, 1.6):
    for g in (0.8, 1.3):
        W = g * np.array([[np.cos(theta), -np.sin(theta)], [np.sin(theta), np.cos(theta)]])
        r = np.array([0.1, 0.0])
        traj = []
        for t in range(6000):
            r = W @ np.tanh(r)
            traj.append(r.copy())
        tr = np.array(traj[-500:])
        amp = float(np.linalg.norm(tr, axis=1).mean())
        ang = np.unwrap(np.arctan2(tr[:, 1], tr[:, 0]))
        rot.append({"theta": theta, "gain": g, "late_amplitude": round(amp, 4),
                    "mean_turn_per_step": round(float(np.diff(ang).mean()), 4)})
out["P3b_complex_rotation"] = rot

# P4 挫败衰减（Wielandt）：不可约 W 有 ρ(W) ≤ ρ(|W|)；对本原 |W|，取等 ⇔ W = ±S|W|S（平衡或反平衡）。
def cycles_frustration(W):
    """暴力求挫败指数：最少翻转多少条边使符号图平衡（小图）。"""
    n = W.shape[0]
    E = [(i, j) for i in range(n) for j in range(n) if i != j and W[i, j] != 0]
    best = len(E)
    for sig in itertools.product([1, -1], repeat=n - 1):
        s = np.array((1,) + sig)
        best = min(best, sum(np.sign(W[i, j]) != s[i] * s[j] for i, j in E))
    return best

ratios, frus, eq_bal, n_bal, strict = [], [], 0, 0, 0
for _ in range(400):
    n = rng.integers(3, 8)
    A = (rng.random((n, n)) < 0.55) * rng.uniform(0.2, 1.5, (n, n))
    np.fill_diagonal(A, 0)
    if rho(A) == 0 or np.linalg.matrix_rank(np.linalg.matrix_power(A + np.eye(n), n)) < n:
        continue
    if (np.linalg.matrix_power(A + np.eye(n), n) <= 0).any():
        continue  # 非强连通
    S = np.diag(rng.choice([1, -1], n))
    Wb = S @ A @ S
    n_bal += 1
    eq_bal += abs(rho(Wb) - rho(A)) < 1e-9
    W = A * rng.choice([1, -1], (n, n))
    f = cycles_frustration(W)
    ratio = rho(W) / rho(A)
    anti = abs(rho(-W) - rho(A)) < 1e-9 and cycles_frustration(-W) == 0
    if f > 0 and not anti:
        strict += ratio < 1 - 1e-9
        ratios.append(ratio)
        frus.append(f / max(1, (A > 0).sum()))
rs = spearmanr(frus, ratios)
out["P4_frustration_attenuates"] = {
    "balanced_equal": f"{eq_bal}/{n_bal}",
    "unbalanced_strictly_smaller": f"{strict}/{len(ratios)}",
    "rho_ratio_median": round(float(np.median(ratios)), 4),
    "spearman_frustration_fraction_vs_ratio": round(float(rs.statistic), 3),
    "spearman_p": float(f"{rs.pvalue:.2e}")}

# P5 可辨识性：线性区只能识别 D_ii + W_ii；激发到饱和区后 D、W 可分离。κ 恒定时 β 与 λ 不可分。
def fit_err(amp, n=4, T=400, noise=0.01):
    D = np.diag(rng.uniform(0.2, 0.6, n))
    W = rng.normal(0, 0.4, (n, n))
    r = np.zeros(n)
    X, Y = [], []
    for _ in range(T):
        s = rng.normal(0, amp, n)
        r1 = step(r, D, W, s) + rng.normal(0, noise, n)
        X.append(np.concatenate([r, np.tanh(r), s]))
        Y.append(r1)
        r = r1
    X, Y = np.array(X), np.array(Y)
    errs_d, errs_wd, errs_wo, conds = [], [], [], []
    for i in range(n):
        cols = [i] + list(range(n, 2 * n)) + [2 * n + i]
        Xi = X[:, cols]
        b = np.linalg.lstsq(Xi, Y[:, i], rcond=None)[0]
        conds.append(np.linalg.cond(Xi))
        errs_d.append(abs(b[0] - D[i, i]))
        errs_wd.append(abs(b[1 + i] - W[i, i]))
        errs_wo += [abs(b[1 + j] - W[i, j]) for j in range(n) if j != i]
        errs_sum = None
    return {"input_amp": amp, "cond": round(float(np.median(conds)), 1), "err_D_ii": round(float(np.median(errs_d)), 4),
            "err_W_ii": round(float(np.median(errs_wd)), 4), "err_W_ij": round(float(np.median(errs_wo)), 4)}

ident = [fit_err(a) for a in (0.01, 0.1, 1.0, 3.0)]

def kappa_split(vary):
    n, T = 1, 600
    beta, lam = 0.9, 0.5
    r, X, Y = 0.0, [], []
    for t in range(T):
        k = rng.uniform(0.2, 1.4) if vary else 0.8
        s = rng.normal(0, 1)
        r1 = (beta - lam * k) * r + 0.3 * np.tanh(r) + s + rng.normal(0, 0.01)
        X.append([r, k * r, np.tanh(r), s])
        Y.append(r1)
        r = r1
    X = np.array(X)
    rank = int(np.linalg.matrix_rank(X, tol=1e-8 * np.abs(X).max()))
    b = np.linalg.lstsq(X, Y, rcond=None)[0]
    return {"kappa_varies": vary, "design_rank": rank, "of": 4, "beta_hat": round(float(b[0]), 4), "lambda_hat": round(float(-b[1]), 4),
            "true": [beta, lam]}

out["P5_identifiability"] = {"diag_vs_offdiag_by_amplitude": ident, "beta_lambda_split": [kappa_split(False), kappa_split(True)]}

# P6 切换：原反例（每个矩阵 ρ=0.3，交替乘积增长率 >1）。线性版发散；饱和版有界（P1）；公共权重范数判据正确地不予认证。
A1 = np.array([[0.3, 3.0], [0.0, 0.3]])
A2 = np.array([[0.3, 0.0], [3.0, 0.3]])
growth = rho(A2 @ A1) ** 0.5
r_lin = np.array([1.0, 1.0])
r_sat = np.array([1.0, 1.0])
for t in range(60):
    A = A1 if t % 2 == 0 else A2
    r_lin = A @ r_lin
    D = 0.3 * np.eye(2)
    r_sat = D @ r_sat + (A - D) @ np.tanh(r_sat)
cert = max(np.abs(A).sum(1).max() for A in (A1, A2)) < 1
out["P6_switching"] = {"each_rho": [rho(A1), rho(A2)], "alternating_growth_per_step": round(growth, 4),
                       "linear_norm_after_60": float(f"{np.abs(r_lin).max():.3e}"),
                       "saturating_norm_after_60": round(float(np.abs(r_sat).max()), 4),
                       "saturating_bound_P1": round((3.0 + 0) / (1 - 0.3), 4),
                       "common_inf_norm_certificate": bool(cert)}

# P7 量化：平衡点处输入-响应增益 G = (I - D - W diag(sech² r*))^{-1}；饱和降低增益。用有限差分核对。
errs, sat_gain = [], []
for _ in range(100):
    n = rng.integers(2, 7)
    D = np.diag(rng.uniform(0, 0.5, n))
    W = rng.normal(0, 1, (n, n))
    W *= 0.9 * (1 - 0.5) / rho(np.abs(W))
    s = rng.normal(0, 3, n)
    def eq(s):
        r = np.zeros(n)
        for _ in range(5000):
            r = step(r, D, W, s)
        return r
    rs_ = eq(s)
    G = np.linalg.inv(np.eye(n) - D - W @ np.diag(1 / np.cosh(rs_) ** 2))
    h = 1e-6
    Gfd = np.column_stack([(eq(s + h * e) - eq(s - h * e)) / (2 * h) for e in np.eye(n)])
    errs.append(np.abs(G - Gfd).max())
    G0 = np.linalg.inv(np.eye(n) - D - W)
    sat_gain.append(np.abs(G).sum() / np.abs(G0).sum())
out["P7_response_gain"] = {"systems": 100, "max_abs_err_vs_finite_diff": float(f"{max(errs):.2e}"),
                           "median_gain_ratio_saturated_vs_linear": round(float(np.median(sat_gain)), 4)}

out["meta"] = {"seed": 20261118, "numpy": np.__version__, "python": sys.version.split()[0]}
txt = json.dumps(out, ensure_ascii=False, indent=1, default=lambda o: o.item() if hasattr(o, "item") else str(o))
open(__file__.replace("analyze.py", "RESULTS.json"), "w").write(txt)
print(txt)
