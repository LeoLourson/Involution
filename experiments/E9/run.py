# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11", "mpmath>=1.3"]
# ///
"""E9 (узел I40): счётная функция N(r)/r для L_a y = -y''(x) - a(x) y''(-x), y(+-1)=0,
против L(a)/pi и против индикатора Delta_a.
Метод 1: коллокация Чебышева-Лобатто, N = 800, 1000, 1200.
Метод 2: принцип аргумента для Delta_a(lambda) по стрельбе (RK4 с перенормировкой), два разрешения.
Аргумент командной строки: all (по умолчанию) | check | colloc | arg | indicator
"""
import sys
import time
import numpy as np
import scipy.linalg as sl
import mpmath as mp
from multiprocessing import Pool

K200 = 200
NS = (800, 1000, 1200)
SEED = 0  # случайных чисел в расчёте нет; зерно зафиксировано для воспроизводимости
np.random.seed(SEED)

CASES = {
    "a=0": lambda x: 0.0 * x,
    "a=1/2": lambda x: 0.5 + 0.0 * x,
    "a=1/2+x/4": lambda x: 0.5 + x / 4,
    "a=x+1/2": lambda x: x + 0.5,
    "a=x/2+0.1x|x|": lambda x: x / 2 + 0.1 * x * np.abs(x),
}
MAIN = ["a=1/2", "a=1/2+x/4", "a=x+1/2", "a=x/2+0.1x|x|"]


# ---------------------------------------------------------------- L(a)
def L_of(afun):
    def integrand(x):
        x = mp.mpf(x)
        p = mp.mpf(float(afun(float(x)))) * mp.mpf(float(afun(-float(x))))
        s = mp.sqrt(mp.mpc(p))
        return mp.re((1 + s) ** (-0.5) + (1 - s) ** (-0.5))
    mp.mp.dps = 25
    return float(mp.quad(integrand, [0, 0.5, 1]))


def L_exact_aconst(c):
    return (1 + c) ** -0.5 + (1 - c) ** -0.5


# ---------------------------------------------------------------- коллокация
def cheb(N):
    x = np.cos(np.pi * np.arange(N + 1) / N)
    c = np.hstack([2, np.ones(N - 1), 2]) * (-1) ** np.arange(N + 1)
    X = np.tile(x, (N + 1, 1)).T
    dX = X - X.T
    D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
    D -= np.diag(D.sum(axis=1))
    return D, x


def colloc_matrix(afun, N):
    D, x = cheb(N)
    D2 = D @ D
    RD2 = D2[::-1, :]  # (R D2 y)_j = y''(-x_j) = (D2 y)_{N-j}
    A = -D2 - afun(x)[:, None] * RD2
    return A[1:N, 1:N]


def colloc_eigs(afun, N, vectors=False):
    A = colloc_matrix(afun, N)
    if vectors:
        w, vl, vr = sl.eig(A, left=True, right=True)
        return A, w, vl, vr
    return A, sl.eig(A, right=False), None, None


def first_mu(w, k=K200 + 30):
    idx = np.argsort(np.abs(w))[:k]
    w = w[idx]
    return w, np.sqrt(np.abs(w))  # |sqrt(lambda)| = sqrt(|lambda|)


def match_err(wa, wb, k=K200):
    """max по первым k значениям wa расстояния до ближайшего значения wb (в lambda), и в |mu|."""
    r = []
    for l in wa[:k]:
        r.append(np.min(np.abs(wb - l)))
    return max(r)


# ---------------------------------------------------------------- стрельба
def shoot(lam, afun, n, nscale=100):
    """Delta_a(lam) = det[Phi1(1),Phi2(1)]_{(u,v)} для массива lam, через внешнее произведение
    Phi1^Phi2 (вторая составная матрица): прямое вычисление двух столбцов теряет точность, так как
    оба сносятся к быстрее растущей моде (ошибка округления растёт как e^{s l_max} против e^{s l_+}).
    Переменные X = (p, s, Q11, Q12, Q21, Q22), W=[[pJ,Q],[-Q^T,sJ]], W' = A W + W A^T, A=[[0,I],[B,0]], B=-lam M^{-1}.
    p = W_12 = Delta. RK4, n шагов; перенормировка положительным числом. Возврат (Delta/|Delta|, log|Delta|)."""
    lam = np.asarray(lam, dtype=complex)
    K = lam.size
    h = 1.0 / n
    xs = np.arange(2 * n + 1) * (h / 2)
    a1 = afun(xs)
    a2 = afun(-xs)
    d = 1.0 - a1 * a2
    m11 = 1.0 / d
    m12 = -a1 / d
    m21 = -a2 / d
    X = np.zeros((6, K), dtype=complex)
    X[2], X[3], X[4], X[5] = 1, -1, 1, -1
    ml = -lam
    logs = np.zeros(K)

    def f(X, i):
        p, s, q11, q12, q21, q22 = X
        B11 = ml * m11[i]
        B12 = ml * m12[i]
        B21 = ml * m21[i]
        B22 = B11
        return np.stack([q12 - q21,
                         B11 * q12 + B12 * q22 - B21 * q11 - B22 * q21,
                         B12 * p, s + B22 * p, -s - B11 * p, -B21 * p])

    for j in range(n):
        i = 2 * j
        k1 = f(X, i)
        k2 = f(X + (h / 2) * k1, i + 1)
        k3 = f(X + (h / 2) * k2, i + 1)
        k4 = f(X + h * k3, i + 2)
        X = X + (h / 6) * (k1 + 2 * k2 + 2 * k3 + k4)
        if (j + 1) % nscale == 0:
            sc = np.max(np.abs(X), axis=0)
            X = X / sc[None, :]
            logs += np.log(sc)
    D = X[0]
    ad = np.abs(D)
    return D / ad, np.log(ad) + logs


# --- обёртки для Pool (на верхнем уровне модуля)
def _afun(name):
    return CASES[name]


def _arg_job(args):
    name, R, nsteps, K = args
    th = np.pi * np.arange(K + 1) / K
    lam = R**2 * np.exp(1j * th)
    ph, lg = shoot(lam, _afun(name), nsteps)
    inc = np.angle(ph[1:] / ph[:-1])
    return name, R, nsteps, K, np.sum(inc) / np.pi, np.max(np.abs(inc)), ph[0], ph[-1]


def _window_job(args):
    """Максимум log|Delta| по окну |mu| in [r0,r0+W] вдоль луча arg mu = theta."""
    name, theta, r0, W, npts, nsteps = args
    r = r0 + W * np.arange(npts) / (npts - 1)
    mu = r * np.exp(1j * theta)
    ph, lg = shoot(mu**2, _afun(name), nsteps)
    return name, theta, r0, float(np.max(lg)), float(r[np.argmax(lg)])


# ---------------------------------------------------------------- точные спектры
def exact_mu_const(c, k=K200 + 60):
    lp, lm = (1 + c) ** -0.5, (1 - c) ** -0.5
    s1 = np.pi * (np.arange(k) + 0.5) / lp
    s2 = np.pi * (np.arange(1, k + 1)) / lm
    return np.sort(np.hstack([s1, s2]))


# ---------------------------------------------------------------- этапы
def stage_check(res):
    print("\n=== Проверка метода ===")
    # L(a) для постоянного a и значения из I40
    for nm, c in (("a=0", 0.0), ("a=1/2", 0.5)):
        print(f"L({nm}) mpmath = {L_of(CASES[nm]):.10f}, точное = {L_exact_aconst(c):.10f}")
    tab = {"a=1/2+x/4": 2.207748, "a=x+1/2": 1.978874, "a=x/2+0.1x|x|": 1.927806}
    for nm, v in tab.items():
        print(f"L({nm}) = {L_of(CASES[nm]):.6f}  (таблица I40: {v})")
    # Delta(a=0) = -sin(2 mu)/mu
    mu = np.array([3.0, 7.5 + 0.5j])
    ph, lg = shoot(mu**2, CASES["a=0"], 2000)
    ex = -np.sin(2 * mu) / mu
    print("a=0: |Delta_shoot| / |Delta_exact| =", np.exp(lg) / np.abs(ex), " фаза:", np.angle(ph / (ex / np.abs(ex))))
    # коллокация против точного спектра: a=0 и a=1/2
    for nm, c in (("a=0", 0.0), ("a=1/2", 0.5)):
        for N in NS:
            _, w, _, _ = colloc_eigs(CASES[nm], N)
            w, mu_c = first_mu(w)
            mu_ex = exact_mu_const(c)[:K200]
            e = np.max(np.abs(np.sort(mu_c[:K200]) - mu_ex) / mu_ex)
            print(f"{nm}: коллокация N={N}: max относительная разность |mu_k| по первым {K200} = {e:.2e}, "
                  f"max|Im lambda|/|lambda| = {np.max(np.abs(w[:K200].imag)/np.abs(w[:K200])):.1e}")
            res[(nm, "check", N)] = e


def stage_colloc(res):
    print("\n=== Коллокация: счётная функция ===")
    out = {}
    for nm in MAIN:
        t0 = time.time()
        L = L_of(CASES[nm])
        sets = {}
        for N in NS:
            vec = (N == NS[0])
            A, w, vl, vr = colloc_eigs(CASES[nm], N, vectors=vec)
            ws, mus = first_mu(w)
            sets[N] = (ws, mus)
            if vec:
                # невязки и обусловленность для первых 200 по модулю
                idx = np.argsort(np.abs(w))[:K200]
                resid = []
                cond = []
                nA = np.linalg.norm(A, 2)
                for i in idx:
                    v = vr[:, i]
                    ww = vl[:, i]
                    resid.append(np.linalg.norm(A @ v - w[i] * v) / (np.linalg.norm(v) * abs(w[i])))
                    cond.append(np.linalg.norm(v) * np.linalg.norm(ww) / abs(np.vdot(ww, v)))
                resid = np.array(resid)
                cond = np.array(cond)
                print(f"[{nm}] N={N}: невязка |Av-lv|/(|l||v|): max {resid.max():.1e}; "
                      f"кондиционность собств. значений kappa: max {cond.max():.2e}, медиана {np.median(cond):.2e}; "
                      f"||A||_2={nA:.2e}; невещественных среди 200: {int(np.sum(np.abs(w[idx].imag) > 1e-6*np.abs(w[idx])))}")
        d12 = match_err(sets[NS[0]][0], sets[NS[1]][0])
        d23 = match_err(sets[NS[1]][0], sets[NS[2]][0])
        print(f"[{nm}] L={L:.6f}, L/pi={L/np.pi:.6f}; разность множеств первых 200 lambda (max |dlambda|): "
              f"{NS[0]}-{NS[1]}: {d12:.2e}, {NS[1]}-{NS[2]}: {d23:.2e}")
        for N in NS:
            mus = sets[N][1]
            ws = sets[N][0]
            ks = np.arange(1, K200 + 1)
            r = mus[:K200]
            sel = (ks >= 50)
            fit = np.polyfit(r[sel], ks[sel] - 0.5, 1)
            wins = []
            for k1, k2 in ((50, 100), (100, 150), (150, 200)):
                wins.append((k2 - k1) / (r[k2 - 1] - r[k1 - 1]))
            print(f"  N={N}: r_50={r[49]:.2f}, r_100={r[99]:.2f}, r_150={r[149]:.2f}, r_200={r[199]:.2f}; "
                  f"N(r)/r при r_200: {200/r[199]:.5f}; наклоны окон (50-100,100-150,150-200): "
                  + ", ".join(f"{s:.5f}" for s in wins) + f"; регрессия k от r (k>=50): наклон {fit[0]:.5f}, сдвиг {fit[1]:.2f}")
        out[nm] = (L, sets)
        print(f"[{nm}] время {time.time()-t0:.0f} с")
        res[("colloc", nm)] = out[nm]
    return out


def stage_arg(res, colloc_out, pool):
    print("\n=== Принцип аргумента (стрельба) ===")
    tasks = []
    chosen = {}
    for nm in MAIN:
        L, sets = colloc_out[nm]
        mus = sets[NS[2]][1]
        for k in (20, 50, 100, 150, 200):
            # радиус R: середина наибольшего зазора |mu| среди номеров k-3..k+3 (из коллокации)
            lo = max(k - 4, 0)
            seg = mus[lo:k + 3]
            g = np.diff(seg)
            j = np.argmax(g)
            R = 0.5 * (seg[j] + seg[j + 1])
            Ncol = int(np.sum(mus < R))
            chosen[(nm, k)] = (R, Ncol)
            for fac in (1, 2):
                tasks.append((nm, R, int(50 * R * fac) + 1, int(12 * R * fac) + 1))
    t0 = time.time()
    rows = pool.map(_arg_job, tasks, chunksize=1)
    print(f"время {time.time()-t0:.0f} с")
    print("случай | k(цель) | R | N_colloc(<R) | N_arg res1 | N_arg res2 | max шаг фазы res1/res2 (рад)")
    d = {}
    for (nm, R, ns, K, cnt, mx, p0, p1) in rows:
        d.setdefault((nm, round(R, 9)), []).append((ns, K, cnt, mx, p0, p1))
    for nm in MAIN:
        for k in (20, 50, 100, 150, 200):
            R, Ncol = chosen[(nm, k)]
            (a, b) = sorted(d[(nm, round(R, 9))])[:2]
            print(f"{nm:16s} {k:4d} R={R:9.3f} N_colloc={Ncol:4d}  N_arg=({a[2]:9.4f},{b[2]:9.4f})  "
                  f"шаг=({a[3]:.2f},{b[3]:.2f})  Im-проверка Delta(R^2),Delta(-R^2) вещественны: "
                  f"{abs(a[4].imag):.0e},{abs(a[5].imag):.0e}")
            res[("arg", nm, k)] = (R, Ncol, a[2], b[2])
    return chosen


def stage_indicator(res, pool):
    print("\n=== Индикатор: вещественная ось и лучи ===")
    thetas = np.linspace(0, np.pi / 2, 19)
    r0s = (150.0, 210.0, 270.0)
    W = 12.0
    tasks = []
    for nm in MAIN:
        for th in thetas:
            for r0 in r0s:
                tasks.append((nm, th, r0, W, 80, 50 * int(r0 + W) + 1))
    t0 = time.time()
    rows = pool.map(_window_job, tasks, chunksize=1)
    print(f"время {time.time()-t0:.0f} с")
    tab = {}
    for (nm, th, r0, lm, rm) in rows:
        tab[(nm, round(th, 9), r0)] = lm
    summary = {}
    for nm in MAIN:
        L = L_of(CASES[nm])
        print(f"\n[{nm}] L={L:.6f}. theta, h(theta) по парам окон r0=150->210, 210->270 (разность макс. log|Delta|"
              f" / сдвиг r0), с поправкой gamma=1 (Delta ~ r^-1): h_raw1, h_raw2, h_corr")
        hs = []
        for th in thetas:
            m = [tab[(nm, round(th, 9), r0)] for r0 in r0s]
            h1 = (m[1] - m[0]) / 60.0
            h2 = (m[2] - m[1]) / 60.0
            hc = (m[2] - m[0]) / 120.0 + np.log((270 + W / 2) / (150 + W / 2)) / 120.0
            hs.append(hc)
            print(f"  {th:.4f}  {h1:.5f}  {h2:.5f}  {hc:.5f}   (L|sin|={L*np.sin(th):.5f})")
        hs = np.array(hs)
        dens = np.trapezoid(hs, thetas) / np.pi
        h0 = hs[0]
        rh = np.sqrt(L**2 + max(h0, 0) ** 2) / np.pi
        print(f"  h(0)={h0:.5f}; плотность (1/4pi)Int h по измеренному h (трапеции, 19 лучей) = {dens:.5f}; "
              f"ромб sqrt(L^2+h0^2)/pi = {rh:.5f}; L/pi = {L/np.pi:.5f}")
        summary[nm] = (h0, dens, rh, L / np.pi)
        res[("ind", nm)] = summary[nm]
    return summary


def stage_asym(res):
    print("\n=== Проверка (A) I40: log|Delta(is)| - sL + log s против log|c(a)| ===")
    ss = np.array([16.0, 24.0, 32.0])
    for nm in MAIN:
        af = CASES[nm]
        L = L_of(af)
        ph, lg = shoot((1j * ss) ** 2, af, 6000)
        a0 = float(af(np.array(0.0)))
        d0 = 1 - a0 * a0
        a1, a1m = float(af(np.array(1.0))), float(af(np.array(-1.0)))
        d1 = 1 - a1 * a1m
        c = 0.5 * np.sqrt(1 - a0) * (d1 / d0) ** 0.25
        print(f"{nm}: " + ", ".join(f"s={s:.0f}: {l - s*L + np.log(s):.4f}" for s, l in zip(ss, lg)) + f"; log|c| = {np.log(c):.4f}")


if __name__ == "__main__":
    stage = sys.argv[1] if len(sys.argv) > 1 else "all"
    t00 = time.time()
    np.set_printoptions(linewidth=160)
    res = {}
    if stage in ("all", "check"):
        stage_check(res)
        stage_asym(res)
    if stage in ("all", "colloc", "arg"):
        co = stage_colloc(res)
    if stage in ("all", "arg", "indicator"):
        with Pool(14) as pool:
            if stage in ("all", "arg"):
                stage_arg(res, co, pool)
            if stage in ("all", "indicator"):
                stage_indicator(res, pool)
    print(f"\nвесь расчёт: {time.time()-t00:.0f} с")
