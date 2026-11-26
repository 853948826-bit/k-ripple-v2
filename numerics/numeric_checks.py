"""Pure-Python checks for two numbers quoted in the paper (no third-party packages).

1. Theorem 5 (critical slowing): t * x(t)^2 -> 3/(2w) at K = d + w = 1.
2. Section 3.5: in a signed scalar network (d = 0, w = -0.9, constant input s = 1.5),
   saturation raises the input-response gain above the linear gain 1/(1 - d - w).
Usage: python3 numeric_checks.py   (writes numeric_checks.json next to this file)
"""
import json
import math
import pathlib

out = {"critical_rate": [], "signed_gain": {}}
for d, w in [(0.5, 0.5), (0.0, 1.0), (0.9, 0.1)]:
    x, steps = 1.0, 2_000_000
    for _ in range(steps):
        x = d * x + w * math.tanh(x)
    out["critical_rate"].append({"d": d, "w": w, "steps": steps, "x0": 1.0,
                                 "t_x2": steps * x * x, "predicted": 3 / (2 * w)})

d, w, s = 0.0, -0.9, 1.5
r = 0.0
for _ in range(10_000):
    r = d * r + w * math.tanh(r) + s
out["signed_gain"] = {"d": d, "w": w, "s": s, "equilibrium": r,
                      "linear_gain": 1 / (1 - d - w),
                      "saturated_gain": 1 / (1 - d - w / math.cosh(r) ** 2)}
path = pathlib.Path(__file__).with_name("numeric_checks.json")
path.write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1))
