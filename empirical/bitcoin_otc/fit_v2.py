"""按 PLAN_V2.md（哈希见 PLAN_V2.sha256）拟合两部分模型。用法：python fit_v2.py <csv.gz> <输出名>"""
import gzip
import hashlib
import json
import sys

import numpy as np
import scipy.sparse as sp
from scipy.stats import rankdata
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler

path, tag = sys.argv[1], sys.argv[2]
raw = open(path, "rb").read()
E = np.loadtxt(gzip.decompress(raw).decode().splitlines(), delimiter=",")
src, dst, rating, tm = E[:, 0].astype(int), E[:, 1].astype(int), E[:, 2], E[:, 3]
ids = {v: k for k, v in enumerate(np.unique(np.concatenate([src, dst])))}
s_i, d_i = np.array([ids[x] for x in src]), np.array([ids[x] for x in dst])
week = ((tm - tm.min()) // (7 * 86400)).astype(int)
n, T = len(ids), week.max() + 1
Q, Cn, Gv = np.zeros((T, n)), np.zeros((T, n)), np.zeros((T, n))
np.add.at(Q, (week, d_i), rating / 10.0)
np.add.at(Cn, (week, d_i), 1)
np.add.at(Gv, (week, s_i), 1)
first_seen = np.full(n, T)
np.minimum.at(first_seen, s_i, week)
np.minimum.at(first_seen, d_i, week)

a = np.exp(-1 / 4)
rng = np.random.default_rng(20261118)
order = np.argsort(tm, kind="stable")
latest, ptr = {}, 0
x, h, g = np.zeros(n), np.zeros(n), np.zeros(n)
rows = {k: [] for k in ["A", "B", "q_now", "y", "wk"]}
for t in range(T - 1):
    x, h, g = a * x + Q[t], a * h + Cn[t], a * g + Gv[t]
    while ptr < len(order) and week[order[ptr]] <= t:
        k = order[ptr]
        latest[(d_i[k], s_i[k])] = np.sign(rating[k])
        ptr += 1
    ij = np.array(list(latest.keys()))
    sg = np.array(list(latest.values()))
    P = sp.csr_matrix(((sg > 0).astype(float), (ij[:, 0], ij[:, 1])), shape=(n, n))
    N = sp.csr_matrix(((sg < 0).astype(float), (ij[:, 0], ij[:, 1])), shape=(n, n))
    Aall = P + N
    el = first_seen <= t
    featA = [np.log1p(h), np.log1p(g), np.log1p(Cn[t]), np.log1p(Aall @ h), np.log1p(Aall.T @ h), np.log1p(t - first_seen + 1.0)]
    th, thp = np.tanh(x), np.tanh(x[rng.permutation(n)])
    featB = [x, th, P @ th, N @ th, P.T @ th, N.T @ th, P @ x, N @ x, P.T @ x, N.T @ x, P @ thp, N @ thp, P.T @ thp, N.T @ thp]
    rows["A"].append(np.column_stack(featA)[el])
    rows["B"].append(np.column_stack(featB)[el])
    rows["q_now"].append(Q[t][el])
    rows["y"].append(Q[t + 1][el] if False else np.column_stack([Q[t + 1], Cn[t + 1]])[el])
    rows["wk"].append(np.full(el.sum(), t + 1))
XA, XB, qnow, YY, WK = (np.vstack(rows[k]) if k in ("A", "B", "y") else np.concatenate(rows[k]) for k in ["A", "B", "q_now", "y", "wk"])
Y, ev = YY[:, 0], YY[:, 1] >= 1
cut = int(np.floor(0.7 * T))
tr, te = WK < cut, WK >= cut
colsB = ["x", "tanh_x", "in_pos", "in_neg", "out_pos", "out_neg", "in_pos_lin", "in_neg_lin", "out_pos_lin", "out_neg_lin",
         "in_pos_perm", "in_neg_perm", "out_pos_perm", "out_neg_perm"]
CB = {c: i for i, c in enumerate(colsB)}
BM = {"B1_persist": ["x"], "B2_linear": ["x", "in_pos_lin", "in_neg_lin", "out_pos_lin", "out_neg_lin"],
      "B3_v2": ["x", "tanh_x", "in_pos", "in_neg", "out_pos", "out_neg"], "B4_unsigned": ["x", "tanh_x", "in_all", "out_all"],
      "B5_perm": ["x", "tanh_x", "in_pos_perm", "in_neg_perm", "out_pos_perm", "out_neg_perm"]}


def dB(names, m):
    parts = [np.ones(m.sum())]
    for nm in names:
        if nm == "in_all":
            parts.append(XB[m, CB["in_pos"]] + XB[m, CB["in_neg"]])
        elif nm == "out_all":
            parts.append(XB[m, CB["out_pos"]] + XB[m, CB["out_neg"]])
        else:
            parts.append(XB[m, CB[nm]])
    return np.column_stack(parts)


def auc(score, label):
    p = label.sum()
    if p == 0 or p == len(label):
        return float("nan")
    rk = rankdata(score)
    return float((rk[label].sum() - p * (p + 1) / 2) / (p * (len(label) - p)))


# A 部分
sc = StandardScaler().fit(XA[tr])
lr = LogisticRegression(penalty=None, max_iter=2000).fit(sc.transform(XA[tr]), ev[tr])
pA = lr.predict_proba(sc.transform(XA[te]))[:, 1]
res = {"A_event": {"test_auc": auc(pA, ev[te]), "coef_std": dict(zip(["log_h", "log_g", "log_c_now", "log_nb_in_h", "log_nb_out_h", "log_age"],
                                                                    np.round(lr.coef_[0], 4).tolist()))}}
# 第一次的 M1 基线
M1 = np.linalg.lstsq(np.column_stack([np.ones(tr.sum()), qnow[tr]]), Y[tr], rcond=None)[0]
err = {"M1_first_round": (M1[0] + M1[1] * qnow[te] - Y[te]) ** 2}
errB, predB = {}, {}
trB, teB = tr & ev, te & ev
for m, names in BM.items():
    b = np.linalg.lstsq(dB(names, trB), Y[trB], rcond=None)[0]
    mu = dB(names, te) @ b
    err["hurdle_" + m] = (pA * mu - Y[te]) ** 2
    muE = dB(names, teB) @ b
    errB[m] = (muE - Y[teB]) ** 2
    predB[m] = muE
    res[m] = {"coef": dict(zip(["const"] + names, np.round(b, 5).tolist())), "event_rows_mse": float(errB[m].mean()),
              "hurdle_total_mse": float(err["hurdle_" + m].mean()), "auc_net_negative_given_event": auc(-muE, Y[teB] < 0)}
res["M1_first_round"] = {"total_mse": float(err["M1_first_round"].mean())}

boot = np.random.default_rng(20261118)


def block_ci(errs, a_, b_, wk):
    weeks = np.unique(wk)
    idx = np.searchsorted(weeks, wk)
    cnt = np.bincount(idx, minlength=len(weeks))
    sa, sb = np.bincount(idx, weights=errs[a_], minlength=len(weeks)), np.bincount(idx, weights=errs[b_], minlength=len(weeks))
    ds = []
    for _ in range(1000):
        q = boot.integers(0, len(weeks), len(weeks))
        ds.append(sa[q].sum() / cnt[q].sum() - sb[q].sum() / cnt[q].sum())
    lo, hi = np.percentile(ds, [2.5, 97.5])
    pt = errs[a_].mean() - errs[b_].mean()
    return {"diff": float(pt), "ci95": [float(lo), float(hi)], "rel": float(pt / errs[b_].mean()), "holds": bool(hi < 0)}


wkE = WK[teB]
weeksE = np.unique(wkE)
byw = {w: np.where(wkE == w)[0] for w in weeksE}
lab = Y[teB] < 0
aucs = []
for _ in range(1000):
    q = boot.integers(0, len(weeksE), len(weeksE))
    ii = np.concatenate([byw[weeksE[j]] for j in q])
    aucs.append(auc(-predB["B3_v2"][ii], lab[ii]))
c3 = res["B3_v2"]["coef"]
hyp = {"G1_hurdle_vs_first_M1": block_ci(err, "hurdle_B3_v2", "M1_first_round", WK[te]),
       "G2_v2_vs_persist": block_ci(errB, "B3_v2", "B1_persist", wkE),
       "G3_saturating_vs_linear": block_ci(errB, "B3_v2", "B2_linear", wkE),
       "G4_signed_vs_unsigned": block_ci(errB, "B3_v2", "B4_unsigned", wkE),
       "G5_structure_vs_perm": block_ci(errB, "B3_v2", "B5_perm", wkE),
       "G6_neg_edge_flips": {"in_pos": c3["in_pos"], "in_neg": c3["in_neg"], "holds": bool(np.sign(c3["in_pos"]) == -np.sign(c3["in_neg"]))},
       "G7_sign_warning_auc": {"auc": res["B3_v2"]["auc_net_negative_given_event"],
                               "ci95": [float(v) for v in np.nanpercentile(aucs, [2.5, 97.5])]}}
hyp["G7_sign_warning_auc"]["holds"] = hyp["G7_sign_warning_auc"]["ci95"][0] > 0.5
out = {"plan_sha256": open(__file__.replace("fit_v2.py", "PLAN_V2.sha256")).read().split()[0],
       "data_sha256": hashlib.sha256(raw).hexdigest(), "tag": tag,
       "data": {"edges": len(E), "nodes": n, "weeks": int(T), "cut_week": cut, "rows_train": int(tr.sum()), "rows_test": int(te.sum()),
                "test_event_rows": int(teB.sum()), "test_net_negative_event_rows": int(lab.sum())},
       "results": res, "hypotheses": hyp, "K_self": round(c3["x"] + c3["tanh_x"], 5)}
txt = json.dumps(out, ensure_ascii=False, indent=1)
open(__file__.replace("fit_v2.py", f"RESULTS_V2_{tag}.json"), "w").write(txt)
print(txt)
