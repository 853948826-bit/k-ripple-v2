"""按 PLAN.md（哈希见 PLAN.sha256）拟合涟漪场方程 V2。用法：python fit.py <csv.gz>"""
import gzip
import hashlib
import json
import sys

import numpy as np
import scipy.sparse as sp
from scipy.stats import rankdata

path = sys.argv[1]
raw = open(path, "rb").read()
assert hashlib.sha256(raw).hexdigest().startswith("6424ac98"), "数据哈希不符"
E = np.loadtxt(gzip.decompress(raw).decode().splitlines(), delimiter=",")
src, dst, rating, tm = E[:, 0].astype(int), E[:, 1].astype(int), E[:, 2], E[:, 3]
ids = {v: k for k, v in enumerate(np.unique(np.concatenate([src, dst])))}
s_i, d_i = np.array([ids[x] for x in src]), np.array([ids[x] for x in dst])
week = ((tm - tm.min()) // (7 * 86400)).astype(int)
n, T = len(ids), week.max() + 1

R = np.zeros((T, n))
np.add.at(R, (week, d_i), rating / 10.0)
first_seen = np.full(n, T)
for w, a, b in zip(week, s_i, d_i):
    first_seen[a] = min(first_seen[a], w)
    first_seen[b] = min(first_seen[b], w)

rng = np.random.default_rng(20261118)
latest = {}
order = np.argsort(tm, kind="stable")
ptr = 0
cols = ["r", "tanh_r", "in_pos", "in_neg", "out_pos", "out_neg", "in_pos_lin", "in_neg_lin", "out_pos_lin", "out_neg_lin",
        "in_pos_perm", "in_neg_perm", "out_pos_perm", "out_neg_perm"]
X, Y, WK = [], [], []
for t in range(T - 1):
    while ptr < len(order) and week[order[ptr]] <= t:
        k = order[ptr]
        latest[(d_i[k], s_i[k])] = np.sign(rating[k])  # (i, j)：j→i
        ptr += 1
    if latest:
        ij = np.array(list(latest.keys()))
        sg = np.array(list(latest.values()))
        P = sp.csr_matrix(((sg > 0).astype(float), (ij[:, 0], ij[:, 1])), shape=(n, n))
        N = sp.csr_matrix(((sg < 0).astype(float), (ij[:, 0], ij[:, 1])), shape=(n, n))
    else:
        P = N = sp.csr_matrix((n, n))
    r = R[t]
    th = np.tanh(r)
    thp = th[rng.permutation(n)]
    feats = [r, th, P @ th, N @ th, P.T @ th, N.T @ th, P @ r, N @ r, P.T @ r, N.T @ r, P @ thp, N @ thp, P.T @ thp, N.T @ thp]
    el = first_seen <= t
    X.append(np.column_stack(feats)[el])
    Y.append(R[t + 1][el])
    WK.append(np.full(el.sum(), t + 1))
X, Y, WK = np.vstack(X), np.concatenate(Y), np.concatenate(WK)
C = {c: i for i, c in enumerate(cols)}
cut = int(np.floor(0.7 * T))
tr, te = WK < cut, WK >= cut

MODELS = {
    "M0_const": [],
    "M1_persist": ["r"],
    "M2_linear": ["r", "in_pos_lin", "in_neg_lin", "out_pos_lin", "out_neg_lin"],
    "M3_v2": ["r", "tanh_r", "in_pos", "in_neg", "out_pos", "out_neg"],
    "M4_unsigned": ["r", "tanh_r", "in_all", "out_all"],
    "M5_perm": ["r", "tanh_r", "in_pos_perm", "in_neg_perm", "out_pos_perm", "out_neg_perm"],
}


def design(names, rows):
    parts = [np.ones(rows.sum())]
    for nm in names:
        if nm == "in_all":
            parts.append(X[rows, C["in_pos"]] + X[rows, C["in_neg"]])
        elif nm == "out_all":
            parts.append(X[rows, C["out_pos"]] + X[rows, C["out_neg"]])
        else:
            parts.append(X[rows, C[nm]])
    return np.column_stack(parts)


def auc(score, label):
    rk = rankdata(score)
    p = label.sum()
    return float((rk[label].sum() - p * (p + 1) / 2) / (p * (len(label) - p)))


res, sqerr = {}, {}
wk_te = WK[te]
for m, names in MODELS.items():
    b = np.linalg.lstsq(design(names, tr), Y[tr], rcond=None)[0]
    pred = design(names, te) @ b
    e = (pred - Y[te]) ** 2
    sqerr[m] = e
    nz = Y[te] != 0
    res[m] = {"coef": dict(zip(["const"] + names, np.round(b, 5).tolist())), "test_mse": float(e.mean()),
              "test_mse_nonzero": float(e[nz].mean()), "auc_next_week_net_negative": auc(-pred, Y[te] < 0)}

weeks = np.unique(wk_te)
idx = np.searchsorted(weeks, wk_te)
cnt = np.bincount(idx, minlength=len(weeks))
wsum = {m: np.bincount(idx, weights=e, minlength=len(weeks)) for m, e in sqerr.items()}
boot = np.random.default_rng(20261118)
draws = [boot.integers(0, len(weeks), len(weeks)) for _ in range(1000)]


def diff_ci(a, b):
    point = sqerr[a].mean() - sqerr[b].mean()
    ds = [wsum[a][g].sum() / cnt[g].sum() - wsum[b][g].sum() / cnt[g].sum() for g in draws]
    lo, hi = np.percentile(ds, [2.5, 97.5])
    return {"mse_diff": float(point), "ci95": [float(lo), float(hi)], "rel_improvement": float(-point / sqerr[b].mean())}


c3 = res["M3_v2"]["coef"]
hyp = {
    "H1_network_vs_persist": diff_ci("M3_v2", "M1_persist"),
    "H2_saturating_vs_linear": diff_ci("M3_v2", "M2_linear"),
    "H3_signed_vs_unsigned": diff_ci("M3_v2", "M4_unsigned"),
    "H5_structure_vs_permuted": diff_ci("M3_v2", "M5_perm"),
}
for h in hyp.values():
    h["holds"] = h["ci95"][1] < 0
hyp["H4_negative_edge_flips_sign"] = {"theta_in_pos": c3["in_pos"], "theta_in_neg": c3["in_neg"],
                                      "theta_out_pos": c3["out_pos"], "theta_out_neg": c3["out_neg"],
                                      "holds": bool(np.sign(c3["in_pos"]) == -np.sign(c3["in_neg"]))}
K = c3["r"] + c3["tanh_r"]
out = {"plan_sha256": open(__file__.replace("fit.py", "PLAN.sha256")).read().split()[0],
       "data": {"edges": len(E), "nodes": n, "weeks": int(T), "train_target_weeks": [1, cut - 1], "test_target_weeks": [cut, int(T) - 1],
                "rows_train": int(tr.sum()), "rows_test": int(te.sum()), "test_nonzero_rows": int((Y[te] != 0).sum()),
                "test_net_negative_rows": int((Y[te] < 0).sum())},
       "models": res, "hypotheses": hyp, "K_self": {"d": c3["r"], "w0": c3["tanh_r"], "K": round(K, 5)}}
txt = json.dumps(out, ensure_ascii=False, indent=1)
open(__file__.replace("fit.py", "RESULTS.json"), "w").write(txt)
print(txt)
