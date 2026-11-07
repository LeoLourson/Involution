# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11", "mpmath>=1.3"]
# ///
"""E8 (узел I42): элемент межканальной связи X на резонансных парах L_a, условия Дирихле.

Метод 1 (стрельба по сложенной системе). u(x)=y(x), w(x)=y(-x), x in [0,1]:
  (u'',w'')^T = -lam T(x)^{-1} (u,w)^T,  T=[[1,a(x)],[a(-x),1]],
  u(0)=w(0), u'(0)=-w'(0), u(1)=w(1)=0.
Определитель D(lam) двух решений в x=1 целая функция lam. Интегрирование: кусочная коллокация Гаусса
(s=10 узлов, порядок 20, P панелей; линейная система решается точно, батчем по lam).
Нули D в круге: значения D на окружности (M точек) -> БПФ -> коэффициенты Тейлора -> корни многочлена;
число нулей контролируется числом обмоток arg D.
Метод 2 (независимый): плотная коллокация Чебышёва-Лобатто на (-1,1) (только nu<=~150), и scipy DOP853.
Расщепление: (l1-l2)^2 = (Delta + d1 - d2)^2 + 4XY, Delta = nu^2 - nu'^2 (модельные серии I41):
  N_+ = pi(n-1/2)/l_+, N_- = pi m/l_-, l_pm = int_0^1 (1 pm b)^(-1/2) dx.
d1, d2 — диагональные сдвиги (lam_k - nu_k^2 у изолированных соседей той же серии).
Случайные числа: только бутстреп с зерном 20261025. Запуск: uv run experiments/E8/run.py [CHECK|MAIN|ALL]
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import sys, time, json
import numpy as np
import scipy.linalg as la
from scipy.integrate import quad, solve_ivp
from concurrent.futures import ProcessPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

# ---------------- параметры (выбраны до расчёта; см. README) ----------------
S_NODES = 10                 # узлов Гаусса на панель
PHASES = (4.0, 3.0, 2.4)     # фаза nu на панель: три разрешения (панелей P = nu*PH_TOT/phase)
PH_MAIN = 3.0                # разрешение для соседей (оценка d)
NU_MIN, NU_MAX = 100.0, 2000.0
D_MAX = float(os.environ.get('E8_DMAX', 80))   # порог резонанса |nu^2 - nu'^2| <= D_MAX (80 — основной, 200 — расширенный)
SUF = '' if D_MAX == 80 else f'_D{int(D_MAX)}'
D_TIGHT = 40.0
PAD = 80.0                   # R = |Delta|/2 + PAD
M_PTS = 48
K_LIST = (10, 16)
ISO_MIN = 400.0              # сосед годится для d, если ближайшая модельная точка другой серии дальше
EPS = 3.0
SEED = 20261025


# ---------------- случаи: a(x), чётная b(x) (b^2 = a Ra, sign b = sign a) ----------------
def a_main(x): return (x * x - .25) ** 2 * np.exp(EPS * (x ** 3 / 3 - x / 4))
def b_main(x): return (x * x - .25) ** 2
def a_even(x): return (x * x - .25) ** 2
def a_m1(x): return (x * x - .25) * (1 + x / 4)
def b_m1(x): return (x * x - .25) * np.sqrt(1 - x * x / 16)
def a_m2(x): return (x * x - .25) ** 2 * (1 + x / 4)
def b_m2(x): return (x * x - .25) ** 2 * np.sqrt(1 - x * x / 16)
def a_c16(x): return .5 + x / 4
def b_c16(x): return np.sqrt(4 - x * x) / 4
def a_half(x): return .5 + 0 * x
def b_half(x): return .5 + 0 * x

CASES = {
    "MAIN":  dict(a=a_main, b=b_main, brk=[0.5], theta="1/3 (критик), 0 ((A) как записано)"),
    "EVEN":  dict(a=a_even, b=a_even, brk=[0.5], theta="X=0 (g=0, C5/C20)"),
    "M1":    dict(a=a_m1, b=b_m1, brk=[0.5], theta="1/2"),
    "M2":    dict(a=a_m2, b=b_m2, brk=[0.5], theta="2/3"),
    "C16":   dict(a=a_c16, b=b_c16, brk=[], theta="0 (m_*=0, корни различны)"),
    "HALF":  dict(a=a_half, b=b_half, brk=[], theta="точный спектр"),
}


def ells(case):
    c = CASES[case]
    b = c["b"]
    pts = [0.0] + c["brk"] + [1.0]
    lp = sum(quad(lambda x: (1 + b(x)) ** -.5, pts[i], pts[i + 1], epsabs=1e-15, epsrel=1e-14)[0] for i in range(len(pts) - 1))
    lm = sum(quad(lambda x: (1 - b(x)) ** -.5, pts[i], pts[i + 1], epsabs=1e-15, epsrel=1e-14)[0] for i in range(len(pts) - 1))
    return lp, lm


def ells_mp(case):
    """Независимо: mpmath, 30 знаков."""
    import mpmath as mp
    mp.mp.dps = 30
    name = {"MAIN": lambda x: (x * x - mp.mpf(1) / 4) ** 2, "EVEN": lambda x: (x * x - mp.mpf(1) / 4) ** 2,
            "M1": lambda x: (x * x - mp.mpf(1) / 4) * mp.sqrt(1 - x * x / 16),
            "M2": lambda x: (x * x - mp.mpf(1) / 4) ** 2 * mp.sqrt(1 - x * x / 16),
            "C16": lambda x: mp.sqrt(4 - x * x) / 4, "HALF": lambda x: mp.mpf(1) / 2}[case]
    pts = [0] + ([mp.mpf(1) / 2] if CASES[case]["brk"] else []) + [1]
    lp = mp.quad(lambda x: (1 + name(x)) ** -.5, pts)
    lm = mp.quad(lambda x: (1 - name(x)) ** -.5, pts)
    return float(lp), float(lm)


# ---------------- интегратор ----------------
_IRK = {}


def irk(s):
    if s not in _IRK:
        xi, w = np.polynomial.legendre.leggauss(s)
        c = (xi + 1) / 2
        bw = w / 2
        A = np.zeros((s, s))
        for i in range(s):
            t = c[i] * (xi + 1) / 2
            wt = c[i] * w / 2
            for j in range(s):
                l = np.ones_like(t)
                for m in range(s):
                    if m != j:
                        l = l * (t - c[m]) / (c[j] - c[m])
                A[i, j] = np.sum(wt * l)
        _IRK[s] = (c, bw, A)
    return _IRK[s]


def Dvals(case, lams, P, s=S_NODES):
    """Определитель D(lam) для массива lam (комплексных); P панелей."""
    afun = CASES[case]["a"]
    lams = np.asarray(lams, complex)
    B = lams.size
    nus = np.sqrt(abs(lams.mean()))
    c, bw, A = irk(s)
    h = 1.0 / P
    xs = np.arange(P) * h
    nodes = xs[:, None] + h * c[None, :]
    ax = afun(nodes); am = afun(-nodes); det = 1 - ax * am
    Y = np.zeros((B, 4, 2), complex)
    Y[:, 0, 0] = 1; Y[:, 1, 0] = 1; Y[:, 2, 1] = 1; Y[:, 3, 1] = -1
    I = np.eye(4 * s)
    for p in range(P):
        cc = lams[:, None] / nus / det[p][None, :]
        F = np.zeros((B, s, 4, 4), complex)
        F[:, :, 0, 2] = nus; F[:, :, 1, 3] = nus
        F[:, :, 2, 0] = -cc; F[:, :, 2, 1] = cc * ax[p]
        F[:, :, 3, 1] = -cc; F[:, :, 3, 0] = cc * am[p]
        M = I[None] - h * np.einsum("ij,bipq->bipjq", A, F).reshape(B, 4 * s, 4 * s)
        rhs = np.einsum("bipq,bqr->bipr", F, Y).reshape(B, 4 * s, 2)
        K = np.linalg.solve(M, rhs).reshape(B, s, 4, 2)
        Y = Y + h * np.einsum("j,bjpr->bpr", bw, K)
    return Y[:, 0, 0] * Y[:, 1, 1] - Y[:, 0, 1] * Y[:, 1, 0]


def Dvals_dop(case, lams, rtol=1e-12):
    """Независимый интегратор: scipy DOP853, те же уравнения."""
    afun = CASES[case]["a"]
    out = []
    lams = np.atleast_1d(lams)
    nus = np.sqrt(abs(lams.mean()))      # та же нормировка p=u'/nus, что в Dvals
    for lam in lams:

        def rhs(x, y):
            ax = afun(x); am = afun(-x); det = 1 - ax * am
            cc = lam / nus / det
            return np.array([nus * y[2], nus * y[3], -cc * (y[0] - ax * y[1]), -cc * (y[1] - am * y[0])])
        r = []
        for ic in ([1, 1, 0, 0], [0, 0, 1, -1]):
            r.append(solve_ivp(rhs, (0, 1), np.array(ic, complex), method="DOP853", rtol=rtol, atol=rtol * 1e-2).y[:, -1])
        out.append(r[0][0] * r[1][1] - r[1][0] * r[0][1])
    return np.array(out)


def zeros_in_disc(case, centre, R, P, M=M_PTS, Ks=K_LIST):
    th = 2 * np.pi * np.arange(M) / M
    lam = centre + R * np.exp(1j * th)
    Dv = Dvals(case, lam, P)
    ph = np.unwrap(np.angle(np.append(Dv, Dv[0])))
    wind = (ph[-1] - ph[0]) / (2 * np.pi)
    coef = np.fft.fft(Dv) / M
    res = {}
    for K in Ks:
        r = np.roots(coef[:K + 1][::-1])
        r = r[np.abs(r) < 1.0]
        res[K] = np.sort_complex(centre + R * r) if r.size else np.array([])
    return res, wind, np.abs(coef[:max(Ks) + 1])


def sort_ev(z):
    return z[np.lexsort((z.imag, z.real))]


# ---------------- модельные серии ----------------
def series(lp, lm, lo, hi):
    n = np.arange(1, int(hi * lp / np.pi) + 3)
    nup = np.pi * (n - .5) / lp
    m = np.arange(1, int(hi * lm / np.pi) + 3)
    num = np.pi * m / lm
    return n, nup, m, num


def enum_pairs(lp, lm, lo, hi, D):
    n, nup, m, num = series(lp, lm, lo, hi)
    out = []
    for i, v in enumerate(nup):
        if not (lo <= v <= hi):
            continue
        d = v * v - num * num
        for j in np.where(np.abs(d) <= D)[0]:
            out.append((int(n[i]), int(m[j]), float(v), float(num[j]), float(d[j])))
    return out


# ---------------- задача для пары ----------------
def pair_job(args):
    case, n, m, lp, lm = args
    t0 = time.time()
    nu = np.pi * (n - .5) / lp
    nup = np.pi * m / lm
    la_, lb_ = nu ** 2, nup ** 2
    Delta = la_ - lb_
    centre = .5 * (la_ + lb_)
    R = abs(Delta) / 2 + PAD
    out = dict(case=case, n=n, m=m, nu=nu, nup=nup, Delta=Delta, R=R, res={})
    nuv = max(nu, nup)
    for ph in PHASES:
        P = int(np.ceil(nuv * 1.2 / ph)) + 4
        roots, wind, co = zeros_in_disc(case, centre, R, P)
        entry = dict(P=P, wind=float(wind))
        for K, r in roots.items():
            entry[f"K{K}"] = [[float(z.real), float(z.imag)] for z in r]
        out["res"][ph] = entry
    # соседи для d
    ser_p = [(k, np.pi * (k - .5) / lp) for k in (n - 2, n - 1, n + 1, n + 2) if k >= 1]
    ser_m = [(k, np.pi * k / lm) for k in (m - 2, m - 1, m + 1, m + 2) if k >= 1]
    nb = {"p": [], "m": []}
    for lab, ser, other in (("p", ser_p, lambda v: np.pi * np.arange(1, int(v * lm / np.pi) + 4) / lm),
                            ("m", ser_m, lambda v: np.pi * (np.arange(1, int(v * lp / np.pi) + 4) - .5) / lp)):
        for k, v in ser:
            ot = other(v) ** 2
            if np.min(np.abs(ot - v * v)) < ISO_MIN:
                continue
            P = int(np.ceil(v * 1.2 / PH_MAIN)) + 4
            roots, wind, co = zeros_in_disc(case, v * v, 40.0, P, M=32, Ks=(12,))
            r = roots[12]
            if r.size == 1 and abs(wind - 1) < 0.2:
                nb[lab].append([k, v * v, float(r[0].real - v * v), float(r[0].imag)])
            else:
                nb[lab].append([k, v * v, None, int(r.size)])
    out["nb"] = nb
    out["time"] = time.time() - t0
    return out


def dfit(lst, x0):
    pts = [(x, d) for _, x, d, im in lst if d is not None]
    if not pts:
        return np.nan, np.nan, np.nan
    x = np.array([p[0] for p in pts]); d = np.array([p[1] for p in pts])
    mean = d.mean()
    if len(pts) >= 2:
        sl = np.polyfit(x - x0, d, 1)
        lin = sl[1]
    else:
        lin = mean
    # оценка по ближайшей паре соседей (±1)
    near = [dd for (k, xx, dd, im) in lst if dd is not None]
    return lin, mean, (d.max() - d.min())


def analyse_pair(rec):
    """По записи пары: собственные значения на разрешениях, X с d-поправкой и без."""
    ev = {}
    for ph, e in rec["res"].items():
        for K in K_LIST:
            z = np.array([complex(*c) for c in e[f"K{K}"]])
            ev[(ph, K)] = sort_ev(z)
    ok = all(v.size == 2 for v in ev.values()) and all(abs(e["wind"] - 2) < 0.2 for e in rec["res"].values())
    rec["ok"] = bool(ok)
    if not ok:
        return rec
    base = ev[(PHASES[-1], K_LIST[-1])]
    rec["lam"] = [[z.real, z.imag] for z in base]
    # разности между разрешениями и усечениями
    rec["d_res"] = float(max(np.max(np.abs(ev[(PHASES[i], K_LIST[-1])] - ev[(PHASES[i + 1], K_LIST[-1])])) for i in range(len(PHASES) - 1)))
    rec["d_res_last"] = float(np.max(np.abs(ev[(PHASES[-2], K_LIST[-1])] - ev[(PHASES[-1], K_LIST[-1])])))
    rec["d_K"] = float(max(np.max(np.abs(ev[(ph, K_LIST[0])] - ev[(ph, K_LIST[-1])])) for ph in PHASES))
    l1, l2 = base
    nu, nup, Delta = rec["nu"], rec["nup"], rec["Delta"]
    sp2 = (l1 - l2) ** 2
    rec["split"] = float(abs(l1 - l2))
    rec["imag"] = float(abs(l1.imag))
    rec["tr"] = complex(l1 + l2 - nu ** 2 - nup ** 2).real
    xy_model = ((sp2 - Delta ** 2) / 4)
    rec["XY_model"] = float(xy_model.real)
    rec["X_model"] = float(np.sqrt(abs(xy_model.real)))
    dp = dfit(rec["nb"]["p"], nu ** 2)
    dm = dfit(rec["nb"]["m"], nup ** 2)
    rec["d1"], rec["d2"] = float(dp[0]), float(dm[0])
    if np.isfinite(dp[0]) and np.isfinite(dm[0]):
        dd = []
        for u, v in ((dp[0], dm[0]), (dp[1], dm[1]), (dp[0], dm[1]), (dp[1], dm[0])):
            Dc = Delta + u - v
            dd.append(float(((sp2 - Dc ** 2) / 4).real))
        rec["XY_corr"] = dd[0]
        rec["X_corr"] = float(np.sqrt(abs(dd[0])))
        rec["XY_corr_alt"] = dd
        # неопределённость: разброс альтернативных оценок d и разрешений
        rec["X_corr_lo"] = float(np.sqrt(abs(min(dd, key=abs))))
        rec["X_corr_hi"] = float(np.sqrt(abs(max(dd, key=abs))))
        rec["tr_check"] = float(rec["tr"] - dp[0] - dm[0])
    else:
        rec["XY_corr"] = rec["X_corr"] = np.nan
    return rec


# ---------------- контрольные проверки ----------------
LOG = []


def say(*p):
    s = " ".join(str(x) for x in p)
    print(s, flush=True)
    LOG.append(s)


def half_exact(kmax=1400):
    ev = [(1.5 * np.pi ** 2 * (k + .5) ** 2, "e", k) for k in range(kmax)] + [(0.5 * np.pi ** 2 * (k + 1) ** 2, "o", k) for k in range(kmax)]
    return sorted(ev)


def check_half():
    """a=1/2: точный спектр. Пары около nu ~ 150, 600, 1500, 2000."""
    say("\n== Проверка 1: a=1/2, точный спектр lam = 1.5 pi^2 (k+1/2)^2 и 0.5 pi^2 (k+1)^2 ==")
    ex = np.array([e[0] for e in half_exact()])
    worst = 0.0
    lp, lm = ells("HALF")
    for target in (150., 600., 1500., 1990.):
        pr = min(enum_pairs(lp, lm, target - 40, target + 40, 3000.0), key=lambda t: abs(t[4]))
        n, m, v, vp, d = pr
        c = .5 * (v * v + vp * vp)
        Rr = abs(d) / 2 + 80
        for ph in PHASES:
            P = int(np.ceil(max(v, vp) * 1.2 / ph)) + 4
            roots, wind, _ = zeros_in_disc("HALF", c, Rr, P)
            r = sort_ev(roots[16])
            exact = np.sort([ex[np.argmin(abs(ex - v * v))], ex[np.argmin(abs(ex - vp * vp))]])
            err = np.max(np.abs(r.real - exact)) if r.size == 2 else np.inf
            if ph == PHASES[-1]:
                worst = max(worst, err)
            say(f"  nu={v:.2f}, nu'={vp:.2f}, Delta={d:.1f}, phase/панель {ph}: P={P}, обмотка {wind:.3f}, нулей {r.size}, "
                f"max|lam-lam_exact|={err:.2e}, max|Im|={np.abs(r.imag).max() if r.size else np.nan:.1e}")
    return worst


def check_integrators():
    say("\n== Проверка 2: IRK против scipy DOP853 (MAIN, D(lam) в комплексных точках) ==")
    worst = 0.0
    for nu in (60., 150.):
        lams = nu ** 2 + np.array([3 + 5j, -20 + 30j, 40 - 10j])
        P = int(np.ceil(nu * 1.2 / PHASES[-1])) + 4
        d1 = Dvals("MAIN", lams, P)
        d2 = Dvals_dop("MAIN", lams, 1e-12)
        rel = np.max(np.abs(d1 - d2) / np.abs(d2))
        worst = max(worst, rel)
        say(f"  nu={nu:.0f}: max отн. разность D {rel:.2e}")
    return worst


def check_ell():
    say("\n== Проверка 3: l_pm, quad против mpmath (30 знаков) ==")
    for c in CASES:
        a1 = ells(c); a2 = ells_mp(c)
        say(f"  {c}: l+={a1[0]:.12f}, l-={a1[1]:.12f}; mpmath {a2[0]:.12f}, {a2[1]:.12f}; разность {max(abs(a1[0]-a2[0]), abs(a1[1]-a2[1])):.1e}")
    # b^2 = a Ra
    xx = np.linspace(-1, 1, 41)
    for c, cs in CASES.items():
        e = np.max(np.abs(cs["b"](xx) ** 2 - cs["a"](xx) * cs["a"](-xx)))
        say(f"  {c}: max|b^2 - a Ra| = {e:.1e}")


def check_table():
    """Воспроизведение строк таблицы из I42 (расщепление ближайшей пары)."""
    say("\n== Проверка 4: строки таблицы I42 (расщепление |lam-lam'|, ожидаемое из идеи) ==")
    rows = [("C16", 36.3, 2.36), ("C16", 108.9, 1.75), ("C16", 181.4, 3.06),
            ("M1", 14.3, 4.55), ("M1", 125.6, 11.10), ("M1", 237.0, 15.05)]
    for case, nu0, want in rows:
        lp, lm = ells(case)
        cand = enum_pairs(lp, lm, nu0 - 2, nu0 + 2, 400.0)
        cand.sort(key=lambda t: abs(t[2] - nu0) + 0.0 * abs(t[4]))
        best = []
        for n, m, v, vp, d in sorted(cand, key=lambda t: abs(t[4]))[:3]:
            c = .5 * (v * v + vp * vp)
            Rr = abs(d) / 2 + (12 if nu0 < 50 else 25)
            P = int(np.ceil(max(v, vp) * 1.2 / 3.0)) + 4
            roots, wind, _ = zeros_in_disc(case, c, Rr, P, M=64)
            r = sort_ev(roots[16])
            if r.size == 2 and abs(wind - 2) < .2:
                best.append((abs(r[0] - r[1]), v, vp, d, r))
        got = "; ".join(f"nu={v:.1f}, nu'={vp:.1f}, Delta={d:.2f}: split={s:.3f}, |Im|={abs(r[0].imag):.2f}" for s, v, vp, d, r in best)
        say(f"  {case}, nu~{nu0}: из идеи {want}; здесь: {got}")


def cheb_check(case, pairs_recs):
    """Независимый метод: плотная коллокация Чебышёва (Дирихле) для пар с nu<=150."""
    afun = CASES[case]["a"]
    from_E7 = None
    N_list = (1000, 1400)

    def cheb(N):
        k = np.arange(N + 1)
        t = np.cos(np.pi * k / N)
        c = np.ones(N + 1); c[0] = 2; c[-1] = 2
        c = c * (-1.0) ** k
        X = np.tile(t, (N + 1, 1)).T
        dX = X - X.T
        D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
        D = D - np.diag(D.sum(axis=1))
        return D, t
    sel = [r for r in pairs_recs if r.get("ok") and r["nu"] <= 150]
    if not sel:
        return None
    out = {}
    for N in N_list:
        D, t = cheb(N)
        D2 = D @ D
        Rm = np.eye(N + 1)[::-1]
        L = -(D2 + np.diag(afun(t)) @ Rm @ D2)[1:N, 1:N]
        ev = la.eigvals(L)
        out[N] = ev
    res = []
    for r in sel:
        lam = np.array([complex(*z) for z in r["lam"]])
        row = []
        for N in N_list:
            row.append(max(np.min(np.abs(out[N] - z)) for z in lam))
        res.append((r["nu"], row))
    return res


# ---------------- статистика ----------------
def slope(x, y):
    return float(np.polyfit(np.log(x), np.log(y), 1)[0])


def boot_slope(nu, X, nb=2000, seed=SEED, env=False):
    rng = np.random.default_rng(seed)
    n = len(nu)
    s = []
    for _ in range(nb):
        i = rng.integers(0, n, n)
        if len(set(i)) < 4:
            continue
        if env:
            bins = [(100, 300), (300, 800), (800, 2001)]
            pts = []
            for lo, hi in bins:
                m = (nu[i] >= lo) & (nu[i] < hi)
                if m.any():
                    pts.append((np.mean(np.log(nu[i][m])), np.log(X[i][m].max())))
            if len(pts) >= 2:
                pts = np.array(pts)
                s.append(np.polyfit(pts[:, 0], pts[:, 1], 1)[0])
        else:
            s.append(np.polyfit(np.log(nu[i]), np.log(X[i]), 1)[0])
    s = np.array(s)
    return float(np.percentile(s, 5)), float(np.percentile(s, 95))


def summarize(case, recs):
    good = [r for r in recs if r.get("ok") and np.isfinite(r.get("X_corr", np.nan))]
    say(f"\n--- {case}: пар в [{NU_MIN:.0f},{NU_MAX:.0f}] с |Delta|<={D_MAX:.0f}: {len(recs)}; обработано {len(good)}, "
        f"отброшено {len(recs)-len(good)} ---")
    say("    nu      nu'     Delta    Re lam1        Re lam2        |Im|    split  | X_mod  X_corr [lo,hi]   XY_corr  d1    d2   | "
        "d_res    d_K     | X_c/nu^1/3  /nu^1/2  /nu^2/3")
    for r in sorted(good, key=lambda r: r["nu"]):
        l1, l2 = r["lam"]
        say(f"  {r['nu']:7.1f} {r['nup']:7.1f} {r['Delta']:+7.2f} {l1[0]:14.4f} {l2[0]:14.4f} {r['imag']:6.2f} {r['split']:7.3f} | "
            f"{r['X_model']:6.2f} {r['X_corr']:6.2f} [{r['X_corr_lo']:5.2f},{r['X_corr_hi']:5.2f}] {r['XY_corr']:+9.2f} {r['d1']:+5.2f} {r['d2']:+5.2f} | "
            f"{r['d_res']:.1e} {r['d_K']:.1e} | {r['X_corr']/r['nu']**(1/3):6.3f} {r['X_corr']/r['nu']**.5:6.3f} {r['X_corr']/r['nu']**(2/3):6.3f}")
    bad = [r for r in recs if not r.get("ok")]
    for r in bad:
        say(f"  ОТБРОШЕНА nu={r['nu']:.1f}, nu'={r['nup']:.1f}, обмотки {[round(e['wind'],2) for e in r['res'].values()]}")
    if len(good) < 4:
        return {}
    nu = np.array([r["nu"] for r in good]); X = np.array([r["X_corr"] for r in good])
    Xm = np.array([r["X_model"] for r in good])
    tight = np.array([abs(r["Delta"]) <= D_TIGHT for r in good])
    say(f"  max d_res (между разрешениями, lam): {max(r['d_res'] for r in good):.2e}; max d_res между двумя последними: "
        f"{max(r['d_res_last'] for r in good):.2e}; max d_K: {max(r['d_K'] for r in good):.2e}")
    say(f"  max|Im lam|: {max(r['imag'] for r in good):.3f}; знак XY_corr<0 у {sum(r['XY_corr']<0 for r in good)} из {len(good)}")
    out = {}
    for lab, mask in ((f"все |Delta|<={D_MAX:.0f}", np.ones(len(good), bool)), ("|Delta|<=40", tight), ("nu>=300, все", nu >= 300)):
        if mask.sum() >= 4:
            sl = slope(nu[mask], np.maximum(X[mask], 1e-3))
            lo, hi = boot_slope(nu[mask], np.maximum(X[mask], 1e-3))
            say(f"  наклон log X_corr / log nu, {lab}: {sl:+.2f} (бутстреп 5-95%: [{lo:+.2f},{hi:+.2f}], n={int(mask.sum())})")
            out[lab] = (sl, lo, hi)
    bins = [(100, 300), (300, 800), (800, 2001)]
    pts = []
    for lo_, hi_ in bins:
        m = (nu >= lo_) & (nu < hi_)
        if m.any():
            say(f"  окно nu in [{lo_},{hi_}): n={int(m.sum())}, X_corr: медиана {np.median(X[m]):.2f}, максимум {X[m].max():.2f}, "
                f"минимум {X[m].min():.2f}; X_model: медиана {np.median(Xm[m]):.2f}, максимум {Xm[m].max():.2f}")
            pts.append((np.mean(np.log(nu[m])), np.log(X[m].max())))
    if len(pts) >= 2:
        pts = np.array(pts)
        pe = float(np.polyfit(pts[:, 0], pts[:, 1], 1)[0])
        lo, hi = boot_slope(nu, np.maximum(X, 1e-3), env=True)
        say(f"  наклон огибающей (максимум X_corr в окнах) : {pe:+.2f} (бутстреп 5-95%: [{lo:+.2f},{hi:+.2f}])")
        out["env"] = (pe, lo, hi)
    return out


def run_pairs(case):
    lp, lm = ells(case)
    pairs = enum_pairs(lp, lm, NU_MIN, NU_MAX, D_MAX)
    jobs = [(case, n, m, lp, lm) for n, m, v, vp, d in pairs]
    jobs.sort(key=lambda j: -max(j[1] * 1.0 / j[3], j[2] / j[4]))
    return jobs


def main_calc(cases):
    t0 = time.time()
    os.makedirs(DATA, exist_ok=True)
    alljobs = []
    for c in cases:
        lp, lm = ells(c)
        say(f"{c}: l+={lp:.10f}, l-={lm:.10f}, l+/l-={lp/lm:.8f}")
        alljobs += run_pairs(c)
    alljobs.sort(key=lambda j: -(j[1] * 1.0 / j[3]))
    say(f"всего задач (пар) {len(alljobs)}")
    recs = {c: [] for c in cases}
    with ProcessPoolExecutor(max_workers=min(18, os.cpu_count() or 4)) as ex:
        for rec in ex.map(pair_job, alljobs, chunksize=1):
            recs[rec["case"]].append(analyse_pair(rec))
    summ = {}
    for c in cases:
        summ[c] = summarize(c, recs[c])
        with open(os.path.join(DATA, f"pairs_{c}{SUF}.json"), "w", encoding="utf-8") as f:
            json.dump(recs[c], f, ensure_ascii=False, default=lambda o: None)
    say(f"\nвремя основного расчёта {time.time()-t0:.0f} c")
    return recs, summ


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "ALL"
    T0 = time.time()
    if which in ("CHECK", "ALL"):
        check_ell()
        w1 = check_half()
        w2 = check_integrators()
        say(f"\nПроверка 1: max |lam - lam_exact| = {w1:.2e} (допуск 1e-5 на самом мелком разрешении); проверка 2: {w2:.2e} (допуск 1e-8)")
        check_table()
        if not (w1 < 1e-5 and w2 < 1e-8):
            say("МЕТОД НЕ ПРОШЁЛ ПРОВЕРКУ: основной расчёт не запускается")
            sys.exit(1)
    if which in ("MAIN", "ALL"):
        cases = ["EVEN", "M1", "M2", "MAIN"]
        recs, summ = main_calc(cases)
        say("\n== Независимый метод: плотная коллокация Чебышёва, пары nu<=150 (max расстояние lam до ближайшего значения коллокации) ==")
        for c in cases:
            r = cheb_check(c, recs[c])
            if r:
                say(f"  {c}: " + "; ".join(f"nu={nu:.1f}: {row[0]:.1e}/{row[1]:.1e}" for nu, row in r) + "  (N=1000/1400)")
    say(f"\nполное время {time.time()-T0:.0f} c")
    if which == "ALL":
        with open(os.path.join(HERE, f"run{SUF}.log"), "w", encoding="utf-8") as f:
            f.write("\n".join(LOG))
