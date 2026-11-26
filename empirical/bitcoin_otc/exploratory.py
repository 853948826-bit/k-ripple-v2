"""探索性诊断（看过 RESULTS.json 之后写，不属于计划内检验）。用法同 fit.py。"""
import json
import runpy
import sys

import numpy as np
import scipy.sparse as sp

g = runpy.run_path(__file__.replace("exploratory.py", "fit.py"), run_name="fit")
X, Y, WK, tr, te, design, MODELS, sqerr, draws = (g[k] for k in ["X", "Y", "WK", "tr", "te", "design", "MODELS", "sqerr", "draws"])
C, wk_te = g["C"], g["WK"][g["te"]]
out = {}

# E1 误差拆分：零行（下周没收到评分）与非零行
z = Y[te] == 0
out["E1_error_split"] = {m: {"zero_rows_mse": float(sqerr[m][z].mean()), "nonzero_rows_sum_share": float(sqerr[m][~z].sum() / sqerr[m].sum())}
                         for m in ["M0_const", "M1_persist", "M3_v2"]}

# E2 只在非零行上比较（条件于下周有评分），整周块自助法
weeks = np.unique(wk_te[~z])
idx = np.searchsorted(weeks, wk_te[~z])
cnt = np.bincount(idx, minlength=len(weeks))
rng = np.random.default_rng(20261118)
dr = [rng.integers(0, len(weeks), len(weeks)) for _ in range(1000)]
ws = {m: np.bincount(idx, weights=sqerr[m][~z], minlength=len(weeks)) for m in sqerr}
def ci(a, b):
    d = [ws[a][q].sum() / cnt[q].sum() - ws[b][q].sum() / cnt[q].sum() for q in dr]
    return {"diff": float(sqerr[a][~z].mean() - sqerr[b][~z].mean()), "ci95": [float(x) for x in np.percentile(d, [2.5, 97.5])]}
out["E2_nonzero_rows"] = {f"{a}_vs_{b}": ci(a, b) for a, b in
                          [("M3_v2", "M1_persist"), ("M3_v2", "M2_linear"), ("M3_v2", "M4_unsigned"), ("M3_v2", "M5_perm")]}

# E3 H4 的混杂检查：负边效应是否只是"被差评过多少次"？加入正/负入度、出度（截至第 t 周的计数）作为控制
latest, ptr, D = {}, 0, []
week, order, s_i, d_i, n, first_seen = (g[k] for k in ["week", "order", "s_i", "d_i", "n", "first_seen"])
rating = g["rating"]
one = np.ones(n)
for t in range(g["T"] - 1):
    while ptr < len(order) and week[order[ptr]] <= t:
        k = order[ptr]; latest[(d_i[k], s_i[k])] = np.sign(rating[k]); ptr += 1
    ij = np.array(list(latest.keys())); sg = np.array(list(latest.values()))
    P = sp.csr_matrix(((sg > 0).astype(float), (ij[:, 0], ij[:, 1])), shape=(n, n))
    N = sp.csr_matrix(((sg < 0).astype(float), (ij[:, 0], ij[:, 1])), shape=(n, n))
    el = first_seen <= t
    D.append(np.column_stack([P @ one, N @ one, P.T @ one, N.T @ one])[el])
D = np.vstack(D)
assert len(D) == len(Y)
base = design(MODELS["M3_v2"], tr)
A = np.column_stack([base, D[tr]])
b = np.linalg.lstsq(A, Y[tr], rcond=None)[0]
At = np.column_stack([design(MODELS["M3_v2"], te), D[te]])
e = (At @ b - Y[te]) ** 2
names = ["const"] + MODELS["M3_v2"] + ["deg_in_pos", "deg_in_neg", "deg_out_pos", "deg_out_neg"]
out["E3_H4_with_degree_controls"] = {"coef": dict(zip(names, np.round(b, 5).tolist())),
                                     "test_mse": float(e.mean()), "test_mse_nonzero": float(e[Y[te] != 0].mean())}
print(json.dumps(out, ensure_ascii=False, indent=1))
json.dump(out, open(__file__.replace("exploratory.py", "EXPLORATORY.json"), "w"), ensure_ascii=False, indent=1)
