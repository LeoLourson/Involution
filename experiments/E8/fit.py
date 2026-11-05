# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11"]
# ///
"""E8, дополнительный анализ (ПОСЛЕ основного расчёта, в README помечен как апостериорный).

Элемент связи от стационарной точки x0=1/2 фазы Phi(x)=nu S_+(x)-nu' S_-(x) осциллирует по паре:
  |X| ~ A nu^p |cos(psi + phi0)| + O(1),  psi = nu S_+(1/2) - nu' S_-(1/2),  S_pm(x)=int_0^x (1 pm b)^(-1/2).
Для каждого p из сетки: phi0 по сетке, A — по МНК; невязка RMS/сумма X^2. Читает data/pairs_*_D200.json.
Запуск: uv run experiments/E8/fit.py [суффикс, по умолчанию _D200]
"""
import os, sys, json
import numpy as np
from scipy.integrate import quad

HERE = os.path.dirname(os.path.abspath(__file__))
SUF = sys.argv[1] if len(sys.argv) > 1 else "_D200"
SEED = 20261025
BS = {
    "MAIN": lambda x: (x * x - .25) ** 2,
    "EVEN": lambda x: (x * x - .25) ** 2,
    "M1": lambda x: (x * x - .25) * np.sqrt(1 - x * x / 16),
    "M2": lambda x: (x * x - .25) ** 2 * np.sqrt(1 - x * x / 16),
}
PGRID = np.round(np.arange(0.0, 1.0001, 0.05), 3)
PHIS = np.linspace(0, np.pi, 181, endpoint=False)


def load(case, numin):
    recs = json.load(open(os.path.join(HERE, "data", f"pairs_{case}{SUF}.json"), encoding="utf-8"))
    recs = [r for r in recs if r.get("ok") and r.get("X_corr") is not None and np.isfinite(r["X_corr"]) and r["nu"] >= numin]
    b = BS[case]
    Sp = quad(lambda x: (1 + b(x)) ** -.5, 0, .5, epsabs=1e-14)[0]
    Sm = quad(lambda x: (1 - b(x)) ** -.5, 0, .5, epsabs=1e-14)[0]
    nu = np.array([r["nu"] for r in recs]); nup = np.array([r["nup"] for r in recs])
    X = np.array([r["X_corr"] for r in recs])
    psi = nu * Sp - nup * Sm
    return nu, psi, X


def best_phi(nu, psi, X, p):
    f0 = nu ** p
    best = (np.inf, None, None)
    for ph in PHIS:
        f = f0 * np.abs(np.cos(psi + ph))
        A = (X @ f) / (f @ f)
        sse = np.sum((X - A * f) ** 2)
        if sse < best[0]:
            best = (sse, A, ph)
    return best


def profile(nu, psi, X):
    return np.array([np.sqrt(best_phi(nu, psi, X, p)[0] / np.sum(X ** 2)) for p in PGRID])


def run(case, numin):
    nu, psi, X = load(case, numin)
    prof = profile(nu, psi, X)
    ip = int(np.argmin(prof))
    sse, A, ph = best_phi(nu, psi, X, PGRID[ip])
    rng = np.random.default_rng(SEED)
    ps = []
    for _ in range(300):
        i = rng.integers(0, len(nu), len(nu))
        pr = profile(nu[i], psi[i], X[i])
        ps.append(PGRID[int(np.argmin(pr))])
    lo, hi = np.percentile(ps, [5, 95])
    def r(p): return prof[int(np.argmin(abs(PGRID - p)))]
    print(f"{case:5s} nu>={numin:4.0f} n={len(nu):3d}: p_best={PGRID[ip]:.2f} (A={A:.3f}, phi0={ph:.2f}, отн. невязка {prof[ip]:.3f}); "
          f"бутстреп 5-95% p in [{lo:.2f},{hi:.2f}]; невязка при p=0: {r(0):.3f}, 1/3: {r(1/3):.3f}, 1/2: {r(.5):.3f}, 2/3: {r(2/3):.3f}, 1: {r(1.0):.3f}")
    return PGRID[ip], lo, hi


if __name__ == "__main__":
    print(f"Фазовый анализ, данные pairs_*{SUF}.json (X_corr)")
    for numin in (100.0, 300.0):
        for case in ("EVEN", "M1", "M2", "MAIN"):
            if case == "EVEN":
                nu, psi, X = load(case, numin)
                print(f"EVEN  nu>={numin:4.0f} n={len(nu)}: max X_corr {X.max():.3f} (X=0 ожидается)")
                continue
            run(case, numin)
