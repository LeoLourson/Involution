# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11", "mpmath>=1.3"]
# ///
"""E10 (узел I43): L y = -y''(x) - a(x) y''(-x) на [-1,1], a = 1/2 + x/4, общие двухточечные условия
U_j = al1 y'(-1) + al0 y(-1) + be1 y'(1) + be0 y(1).
Метод 1: коллокация Чебышева-Лобатто (N1,N2,N3), обобщённая задача на собственные значения.
Метод 2: складывание на [0,1] в систему 2x2 w'' = -lambda M^{-1} w, стрельба (DOP853, rtol 1e-13),
определитель условий по lambda, секущие по rho от затравок метода 1 / нулей F.
Сравнение rho_k = sqrt(lambda_k) с нулями главной части F (шаг 4 идеи I43).
Аргументы: check | cases | all (по умолчанию); K=число собственных значений (по умолчанию 100).
"""
import sys
import warnings
warnings.filterwarnings('ignore')
sys.stdout.reconfigure(encoding='utf-8')
import time
import numpy as np
import scipy.linalg as sl
from scipy.integrate import quad, solve_ivp
from scipy.optimize import linear_sum_assignment

np.set_printoptions(linewidth=160)
SEED = 0  # случайных чисел нет


# ---------------------------------------------------------------- коэффициент и константы F
def make_consts(a):
    p = lambda x: a(x) * a(-x)
    sp = lambda x: np.sqrt(p(x))
    lp = quad(lambda t: (1 + sp(t)) ** -0.5, 0, 1, epsabs=1e-14, epsrel=1e-14)[0]
    lm = quad(lambda t: (1 - sp(t)) ** -0.5, 0, 1, epsabs=1e-14, epsrel=1e-14)[0]
    eps = np.sign(a(0.5))
    om_p = (1 + sp(1.0)) ** -0.5
    om_m = (1 - sp(1.0)) ** -0.5
    kap = eps * np.sqrt(a(-1.0) / a(1.0))
    return dict(lp=lp, lm=lm, L=lp + lm, d=lp - lm, om_p=om_p, om_m=om_m, kap=kap, eps=eps)


def AB(c, cond):
    """A, B для вида (1,0): U1 -> (al11, be11), U2 -> (al20, be20)."""
    al11, be11, al20, be20 = cond
    A = c['om_p'] * (be11 - c['kap'] * al11) * (be20 - c['kap'] * al20)
    B = c['om_m'] * (be11 + c['kap'] * al11) * (be20 + c['kap'] * al20)
    return A, B


def F_zeros(kind, c, cond, R, a_is_pos=True):
    """Нули F с Re rho >= 0 и |Re rho| <= R, массив комплексных, по возрастанию Re."""
    lp, lm, L, d = c['lp'], c['lm'], c['L'], c['d']
    if c['eps'] < 0:
        lp, lm = lm, lp
    z = []
    if kind == '00':
        z += [np.pi * (n - 0.5) / lp for n in range(1, 10 ** 5) if np.pi * (n - 0.5) / lp <= R]
        z += [np.pi * n / lm for n in range(1, 10 ** 5) if np.pi * n / lm <= R]
    elif kind == '11':
        z += [0.0]  # lambda=0 (y=const) для условий Неймана
        z += [np.pi * n / lp for n in range(1, 10 ** 5) if np.pi * n / lp <= R]
        z += [np.pi * (n - 0.5) / lm for n in range(1, 10 ** 5) if np.pi * (n - 0.5) / lm <= R]
    elif kind == '10':
        A, B = AB(c, cond)
        if c['eps'] < 0:
            A, B = B, A  # замена l+ <-> l- в таблице
        Fz = lambda r: A * np.sin(r * lp) * np.sin(r * lm) + B * np.cos(r * lp) * np.cos(r * lm)
        dF = lambda r: A * (lp * np.cos(r * lp) * np.sin(r * lm) + lm * np.sin(r * lp) * np.cos(r * lm)) \
            + B * (-lp * np.sin(r * lp) * np.cos(r * lm) - lm * np.cos(r * lp) * np.sin(r * lm))
        # затравки: сетка по Re с шагом ~ 0.25*pi/L и мнимые смещения
        res = []
        for x0 in np.arange(0.02, R + 1, 0.2 * np.pi / (lp + lm)):
            for y0 in (0.0, 0.5, -0.5, 1.5, -1.5):
                r = complex(x0, y0)
                for _ in range(60):
                    f, df = Fz(r), dF(r)
                    if df == 0:
                        break
                    s = f / df
                    r -= s
                    if abs(s) < 1e-14 * max(1, abs(r)):
                        break
                if abs(Fz(r)) < 1e-9 * (abs(A) + abs(B)) and r.real > 1e-6 and r.real <= R:
                    if all(abs(r - q) > 1e-7 for q in res):
                        res.append(r)
        z = res
    z = sorted(z, key=lambda r: (round(complex(r).real, 9), complex(r).imag))
    return np.array(z, dtype=complex)


# ---------------------------------------------------------------- метод 1: коллокация
def cheb(N):
    x = np.cos(np.pi * np.arange(N + 1) / N)
    c = np.hstack([2, np.ones(N - 1), 2]) * (-1) ** np.arange(N + 1)
    X = np.tile(x, (N + 1, 1)).T
    dX = X - X.T
    D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
    D -= np.diag(D.sum(axis=1))
    return D, x


def colloc(a, cond4, N, K):
    """cond4 = ((al1,al0,be1,be0) для U1, ... для U2). Возвращает rho_k (K штук, по |lambda|)."""
    D, x = cheb(N)
    D2 = D @ D
    R = np.eye(N + 1)[::-1]
    Lm = -D2 - np.diag(a(x)) @ R @ D2
    Bm = np.eye(N + 1)
    for row, (al1, al0, be1, be0) in zip((0, N), cond4):
        Lm[row, :] = 0
        Lm[row, :] += al1 * D[N, :] + be1 * D[0, :]
        Lm[row, 0] += be0
        Lm[row, N] += al0
        Bm[row, :] = 0
    w = sl.eig(Lm, Bm, right=False)
    w = w[np.isfinite(w)]
    w = w[np.abs(w) < 1e7]
    w = w[np.argsort(np.abs(w))]
    return np.sqrt(w[:K].astype(complex)), w[:K]


# ---------------------------------------------------------------- метод 2: стрельба
RTOL = 1e-13


def make_det(a, cond4, rtol=None):
    """Векторная версия: D(rho_array) -> (det, scale). Все lambda интегрируются одной системой."""
    rtol = RTOL if rtol is None else rtol
    (u1, u2) = cond4

    def D(rho):
        rho = np.atleast_1d(np.asarray(rho, dtype=complex))
        lam = rho ** 2
        n = len(lam)

        def f(x, Y):
            Y = Y.reshape(4, n)
            ax, am = a(x), a(-x)
            den = 1.0 - ax * am
            w1, w2, v1, v2 = Y
            return np.array([v1, v2, -lam * (w1 - ax * w2) / den, -lam * (-am * w1 + w2) / den]).reshape(-1)

        sols = []
        for y0 in ((1, 1, 0, 0), (0, 0, 1, -1)):
            Y0 = np.array([np.full(n, v, dtype=complex) for v in y0]).reshape(-1)
            s = solve_ivp(f, (0, 1), Y0, method='DOP853', rtol=rtol, atol=1e-14)
            sols.append(s.y[:, -1].reshape(4, n))
        vals = []
        for S in sols:
            w1, w2, v1, v2 = S
            vals.append([cc[0] * (-v2) + cc[1] * w2 + cc[2] * v1 + cc[3] * w1 for cc in (u1, u2)])
        m00, m10 = vals[0]
        m01, m11 = vals[1]
        det = m00 * m11 - m01 * m10
        scale = np.abs(m00 * m11) + np.abs(m01 * m10)
        return det, scale
    return D


def secant(Dfun, r0, tol=1e-11, itmax=30):
    """Секущие по rho для массива затравок; сошедшиеся элементы замораживаются."""
    r0 = np.atleast_1d(np.asarray(r0, dtype=complex))
    r1 = r0 + 1e-4
    f0 = Dfun(r0)[0]
    f1 = Dfun(r1)[0]
    active = np.ones(len(r0), dtype=bool)
    for _ in range(itmax):
        den = f1 - f0
        ok = active & (den != 0)
        step = np.zeros_like(r1)
        step[ok] = (f1[ok] * (r1[ok] - r0[ok]) / den[ok])
        step = np.where(np.abs(step) > 0.5, 0.5 * step / np.abs(step), step)
        r2 = r1 - step
        r0, f0 = np.where(active, r1, r0), np.where(active, f1, f0)
        r1 = np.where(active, r2, r1)
        f1 = np.where(active, Dfun(r1)[0], f1)
        active &= np.abs(r1 - r0) > tol
        if not active.any():
            break
    det, sc = Dfun(r1)
    dp = np.abs(Dfun(r1 + 0.02)[0])
    dm = np.abs(Dfun(r1 - 0.02)[0])
    return r1, np.abs(det) / np.maximum(dp, dm)


def fix_branch(r):
    """Главная ветвь rho = sqrt(lambda): Re rho >= 0, на мнимой оси Im rho > 0."""
    if abs(r.real) < 1e-9:
        return complex(0.0, abs(r.imag)) if abs(r.imag) > 1e-12 else complex(abs(r.real), r.imag)
    return -r if r.real < 0 else r


def polish(Dfun, seeds):
    r, rr = secant(Dfun, np.asarray(seeds, dtype=complex))
    return np.array([fix_branch(x) for x in r]), rr


# ---------------------------------------------------------------- сопоставление
def match(rho, zeros):
    """Сопоставление первых len(rho) значений с нулями F назначением; возвращает ближайшие нули."""
    K = len(rho)
    Z = zeros[: K + 15]
    C = np.abs(rho[:, None] - Z[None, :])
    i, j = linear_sum_assignment(C)
    return Z[j], np.abs(rho[i] - Z[j])


def gaps(zeros, upto):
    """Расстояние от каждого нуля до ближайшего другого нуля."""
    g = []
    for i, z in enumerate(zeros[:upto]):
        dd = np.abs(zeros - z)
        dd[i] = np.inf
        g.append(dd.min())
    return np.array(g)


# ---------------------------------------------------------------- прогон одного случая
def run_case(name, a, kind, cond4, cond10, K, Ns, extra_zero_kind=None, verbose_rows=True):
    t0 = time.time()
    c = make_consts(a)
    print(f"\n=== {name}  (вид {kind}) ===")
    print(f"l+={c['lp']:.10f} l-={c['lm']:.10f} L={c['L']:.10f} d={c['d']:.10f} "
          f"om+={c['om_p']:.8f} om-={c['om_m']:.8f} kappa={c['kap']:.8f} eps={c['eps']:+.0f}")
    if kind == '10':
        A, B = AB(c, cond10)
        gam = (A + B) / (B - A) if B != A else np.inf
        print(f"A={A:.8f} B={B:.8f} A-B={A - B:.3e} gamma={gam:.6f}  "
              f"|gamma|*cosh(pi d/(2L))={abs(gam) * np.cosh(np.pi * c['d'] / (2 * c['L'])):.6f}")
    # метод 1
    rhos = []
    for N in Ns:
        rr, ll = colloc(a, cond4, N, K + 5)
        rr = np.array([fix_branch(r) for r in rr])
        rr = rr[np.lexsort((rr.imag, np.round(rr.real, 9)))]
        rhos.append(rr)
        print(f"  коллокация N={N}: rho_1={rr[0]:.10f}, rho_{K}={rr[K - 1]:.8f}")
    for i in range(len(Ns) - 1):
        dm = np.abs(rhos[i][:K] - rhos[i + 1][:K])
        print(f"  max|rho(N={Ns[i]})-rho(N={Ns[i + 1]})| по первым {K}: {dm.max():.3e}; по k<=K/2: {dm[:K // 2].max():.3e}")
    # метод 2
    Dfun = make_det(a, cond4)
    pol, res = polish(Dfun, rhos[-1][:K])
    d_cp = np.abs(pol - rhos[-1][:K])
    print(f"  стрельба (полировка с затравок N={Ns[-1]}): max невязка |D|/scale = {res.max():.2e}, "
          f"max|rho_шт - rho_кол| = {d_cp.max():.3e} (k<=K/2: {d_cp[:K // 2].max():.3e})")
    # устойчивость порядка/уникальность
    uniq = np.min(np.abs(pol[:, None] - pol[None, :]) + np.eye(K) * 1e9)
    print(f"  min расстояние между различными найденными rho: {uniq:.3e}")
    pol = pol[np.lexsort((pol.imag, np.round(pol.real, 7)))]
    if kind == '10':
        small = np.abs(pol) < 1e-3
        if small.any():
            print(f"  собственные значения с |rho|<1e-3 (lambda=0, y=const удовлетворяет условиям): {small.sum()}; "
                  f"из сопоставления с нулями F исключены")
            pol = pol[~small]
            K = len(pol)
    # нули F
    zk = kind
    zeros = F_zeros(zk, c, cond10, pol.real.max() + 6)
    if len(zeros) < K:
        print(f"  нулей F в окне Re rho<={pol.real.max() + 6:.0f}: {len(zeros)} < K: сопоставление не делается "
              f"(F лишён члена e^(+-i rho L), нули не описывают спектр)")
        k = np.arange(1, K + 1)
        print("   k      Re rho_k    Im rho_k")
        for i in sorted(set(list(range(0, 12)) + list(range(12, K, max(1, K // 16))))):
            print(f"  {k[i]:4d} {pol[i].real:11.6f} {pol[i].imag:11.5f}")
        print(f"  время: {time.time() - t0:.1f} с")
        return dict(c=c, pol=pol)
    zm, err = match(pol, zeros)
    g = gaps(zeros, K + 15)
    # gap для сопоставленных нулей
    gz = np.array([g[np.argmin(np.abs(zeros - z))] for z in zm])
    k = np.arange(1, K + 1)
    print(f"  нулей F в окне: {len(zeros)}; сопоставлено {K}")
    if verbose_rows:
        print("   k      Re rho_k    Im rho_k   |rho-rho0|   k*|rho-rho0|   gap(F)   k*gap")
        idx = list(range(0, min(12, K))) + list(range(12, K, max(1, K // 16)))
        for i in sorted(set(idx)):
            print(f"  {k[i]:4d} {pol[i].real:11.6f} {pol[i].imag:11.3e} {err[i]:12.3e} {k[i] * err[i]:12.4f} "
                  f"{gz[i]:10.3e} {k[i] * gz[i]:8.3f}")
    # окна
    q = [(1, K // 4), (K // 4 + 1, K // 2), (K // 2 + 1, 3 * K // 4), (3 * K // 4 + 1, K)]
    print("  окна по k: max k*|drho|, max |drho|, max |Im rho|, min gap*k")
    for (lo, hi) in q:
        s = slice(lo - 1, hi)
        print(f"   k in [{lo:3d},{hi:3d}]: {np.max(k[s] * err[s]):9.4f}  {np.max(err[s]):9.3e}  "
              f"{np.max(np.abs(pol[s].imag)):9.3e}  {np.min(k[s] * gz[s]):8.3f}")
    # наибольшие k*err
    top = np.argsort(-(k * err))[:8]
    print("  наибольшие k*|drho|: k, rho_k, ближайший нуль F, k*err, gap(F), Im(нуля)")
    for i in sorted(top):
        print(f"   {k[i]:4d} {pol[i]:.6f} {zm[i]:.6f} {k[i] * err[i]:8.3f} {gz[i]:9.3e} {zm[i].imag:+.4f}")
    # группы нулей F (одиночное связывание, порог TAU) и симметрические функции внутри групп
    for TAU in (0.15, 0.5):
        group_stats(pol, zm, k, K, TAU)
    print(f"  время: {time.time() - t0:.1f} с")
    return dict(c=c, pol=pol, err=err, zeros=zeros, zm=zm, gz=gz)


def group_stats(pol, zm, k, K, TAU):
    zu = np.unique(np.round(zm, 12))
    order = np.argsort(zu.real + 1e-3 * zu.imag)
    zu = zu[order]
    lab = -np.ones(len(zu), dtype=int)
    ng = 0
    for i in range(len(zu)):
        if lab[i] < 0:
            stack = [i]
            lab[i] = ng
            while stack:
                u = stack.pop()
                for v in range(len(zu)):
                    if lab[v] < 0 and abs(zu[u] - zu[v]) < TAU:
                        lab[v] = ng
                        stack.append(v)
            ng += 1
    elab = np.array([lab[np.argmin(np.abs(zu - z))] for z in zm])
    sizes = np.bincount(lab)
    stat = {1: [], 2: [], 3: []}
    for gidx in range(ng):
        mem = np.where(elab == gidx)[0]
        zg = zu[lab == gidx]
        if len(mem) != len(zg) or len(mem) > 3:
            continue
        kk = k[mem].mean()
        s1 = abs(pol[mem].sum() - zg.sum())
        if len(mem) == 1:
            stat[1].append((kk, kk * s1, 0.0))
        elif len(mem) == 2:
            cz = zg.mean()
            s2 = abs((pol[mem[0]] - cz) * (pol[mem[1]] - cz) - (zg[0] - cz) * (zg[1] - cz))
            stat[2].append((kk, kk * s1, kk * s2))
        else:
            cz = zg.mean()
            e = lambda v: sum(v[i] * v[j] for i in range(3) for j in range(i + 1, 3))
            s2 = abs(e(pol[mem] - cz) - e(zg - cz))
            stat[3].append((kk, kk * s1, kk * s2))
    print(f"  группы нулей F (порог {TAU}): размеров 1/2/3: {sum(sizes == 1)}/{sum(sizes == 2)}/{sum(sizes == 3)}, всего {ng}")
    for m in (1, 2, 3):
        if stat[m]:
            arr = np.array(stat[m])
            half = arr[:, 0] > K / 2
            print(f"   размер {m}: n={len(arr)}; max k*|dsigma1|={arr[:, 1].max():.4f} (k>K/2: "
                  f"{arr[half, 1].max() if half.any() else float('nan'):.4f}); "
                  f"max k*|dsigma2(сдвиг)|={arr[:, 2].max():.4f} (k>K/2: {arr[half, 2].max() if half.any() else float('nan'):.4f})")


# ---------------------------------------------------------------- контроль метода
def check():
    print("##### ПРОВЕРКА МЕТОДА #####")
    # (a) a = 0, U1 = y'(1), U2 = y(-1): F = cos 2rho; rho = pi(n-1/2)/2
    a0 = lambda x: 0.0 * np.asarray(x, dtype=float)
    c0 = make_consts(lambda x: 1e-12 + 0 * np.asarray(x, dtype=float))
    # al1,al0,be1,be0
    cond4 = ((0, 0, 1, 0), (0, 1, 0, 0))
    rr, _ = colloc(a0, cond4, 120, 20)
    rr = np.sort(rr.real)
    ex = np.pi * (np.arange(1, 21) - 0.5) / 2
    print(f"a=0, y'(1)=0,y(-1)=0: коллокация N=120 vs pi(n-1/2)/2: max ошибка {np.max(np.abs(rr - ex)):.2e}")
    Dfun = make_det(a0, cond4)
    pol, res = polish(Dfun, ex + 0.05)
    print(f"   стрельба (затравка +0.05): max ошибка {np.max(np.abs(pol - ex)):.2e}, невязка {res.max():.1e}")
    print(f"   (константы при a->0: l+={c0['lp']:.6f} l-={c0['lm']:.6f} om={c0['om_p']:.6f} kappa={c0['kap']:.6f}; "
          f"A={AB(c0, (0, 1, 1, 0))[0]:.6f} B={AB(c0, (0, 1, 1, 0))[1]:.6f} -> F=cos 2rho)")
    # (b) постоянное a=1/2, Дирихле: точный спектр C3
    ac = lambda x: 0.5 + 0.0 * np.asarray(x, dtype=float)
    cc = make_consts(ac)
    zer = F_zeros('00', cc, None, 80)[:30]
    cond4 = ((0, 1, 0, 0), (0, 0, 0, 1))
    rr, _ = colloc(ac, cond4, 160, 30)
    rr = np.sort(rr.real)
    print(f"a=1/2 Дирихле: l+={cc['lp']:.8f} (точно {1 / np.sqrt(1.5):.8f}), l-={cc['lm']:.8f} (точно {1 / np.sqrt(.5):.8f})")
    print(f"   коллокация N=160, 30 значений vs серии C3: max ошибка {np.max(np.abs(rr - zer)):.2e}")
    pol, res = polish(make_det(ac, cond4), zer + 0.003)
    print(f"   стрельба: max ошибка {np.max(np.abs(np.sort(pol.real) - zer)):.2e}, невязка {res.max():.1e}")
    # (c) постоянное a=1/2, вид (1,0): F точна
    cond10 = (0.3, 1.0, 0.2, 1.0)  # al11, be11, al20, be20 -> порядок в AB: al11,be11,al20,be20
    al11, be11, al20, be20 = 0.0, 1.0, -3.0, 1.0
    cond4 = ((al11, 0, be11, 0), (0, al20, 0, be20))
    zer = F_zeros('10', cc, (al11, be11, al20, be20), 40)[:25]
    rr, _ = colloc(ac, cond4, 160, 25)
    rr = np.sort(rr.real)
    A, B = AB(cc, (al11, be11, al20, be20))
    print(f"a=1/2, вид (1,0) (y'(1)=0, y(1)-3y(-1)=0): A={A:.6f} B={B:.6f}; нулей F: {len(zer)}")
    n = min(len(zer), len(rr))
    print(f"   коллокация vs нули F: max ошибка {np.max(np.abs(rr[:n] - np.sort(zer.real)[:n])):.2e}")
    pol, res = polish(make_det(ac, cond4), np.sort(zer.real)[:n] + 0.003)
    print(f"   стрельба vs нули F: max ошибка {np.max(np.abs(np.sort(pol.real) - np.sort(zer.real)[:n])):.2e}, невязка {res.max():.1e}")
    # (d) a = -1/2 (eps=-1), Дирихле
    an = lambda x: -0.5 + 0.0 * np.asarray(x, dtype=float)
    cn = make_consts(an)
    zer = F_zeros('00', cn, None, 80)[:30]
    rr, _ = colloc(an, ((0, 1, 0, 0), (0, 0, 0, 1)), 160, 30)
    print(f"a=-1/2 Дирихле (eps=-1): коллокация vs серии с l+<->l-: max ошибка {np.max(np.abs(np.sort(rr.real) - zer)):.2e}")
    # (e) a = -1/2, вид (1,0)
    zer = F_zeros('10', cn, (al11, be11, al20, be20), 40)
    rr, _ = colloc(an, cond4, 160, 25)
    n = min(len(zer), 25)
    print(f"a=-1/2 вид (1,0): коллокация vs нули F: max ошибка {np.max(np.abs(np.sort(rr.real)[:n] - np.sort(zer.real)[:n])):.2e}")


# ---------------------------------------------------------------- основные случаи
def cases(K, Ns, which=None):
    a = lambda x: 0.5 + 0.25 * np.asarray(x, dtype=float)
    c = make_consts(a)
    print("\n##### ОСНОВНЫЕ СЛУЧАИ, a = 1/2 + x/4 #####")
    out = {}
    want = (lambda t: which is None or t in which)
    # 1: Дирихле
    if want('1'): out['1'] = run_case("1) Дирихле y(1)=y(-1)=0", a, '00', ((0, 1, 0, 0), (0, 0, 0, 1)), None, K, Ns)
    # 2: (1,1)  U1 = y'(1), U2 = y'(-1)
    if want('2'): out['2'] = run_case("2) Нейман y'(1)=y'(-1)=0", a, '11', ((0, 0, 1, 0), (1, 0, 0, 0)), None, K, Ns)
    # 3: (1,0): U1 = y'(1) (be11=1, al11=0), U2 = y(1)+t y(-1).
    # t выбрано до расчёта из условия A+B=0 при a=0 неудобно; берём правило: gamma(t) = (A+B)/(B-A),
    # t = -3 (даёт |gamma| заметно меньше 1 по предварительной формуле, см. README).
    for tag, t in (("3a", -3.0), ("3b", -6.0)):
        cond10 = (0.0, 1.0, t, 1.0)  # al11, be11, al20, be20
        if want(tag): out[tag] = run_case(f"{tag}) вид (1,0): U1=y'(1), U2=y(1)+({t})y(-1)", a, '10',
                            ((0, 0, 1, 0), (0, t, 0, 1)), cond10, K, Ns)
    # 3c: |gamma| > 1 (контрпример к условию D, проверка того, что нули F комплексные/сближаются)
    t = 2.0
    cond10 = (0.0, 1.0, t, 1.0)
    if want('3c'): out['3c'] = run_case(f"3c) вид (1,0), |gamma| близко к 1: U1=y'(1), U2=y(1)+({t})y(-1)", a, '10',
                         ((0, 0, 1, 0), (0, t, 0, 1)), cond10, K, Ns)
    # 4: (E)
    cond10 = (1.0, 1.0, -1.0, 1.0)
    if want('4'): out['4'] = run_case("4) (E): y'(1)+y'(-1)=0, y(1)-y(-1)=0", a, '10',
                        ((1, 0, 1, 0), (0, -1, 0, 1)), cond10, K, Ns)
    # 5: A=B: U1=y'(1), U2=y(1)+t y(-1), t = (om+ - om-)/(kappa (om+ + om-))
    t5 = (c['om_p'] - c['om_m']) / (c['kap'] * (c['om_p'] + c['om_m']))
    cond10 = (0.0, 1.0, t5, 1.0)
    # здесь al20 = t5 при y(-1), be20 = 1 при y(1); AB даёт (be20 - k al20) -> A, (be20 + k al20) -> B
    # нужно A=B: om+ (1 - k t) = om- (1 + k t)  => t = (om+ - om-)/(k (om+ + om-))
    if want('5'): out['5'] = run_case(f"5) A=B: U1=y'(1), U2=y(1)+({t5:.10f})y(-1)", a, '10',
                        ((0, 0, 1, 0), (0, t5, 0, 1)), cond10, K, Ns, verbose_rows=True)
    return out


def case5_growth(res, K):
    c = res['c']
    pol = res['pol']
    L, d = c['L'], c['d']
    cpl = pol[np.abs(pol.imag) > 1e-3]
    print(f"\n  Случай 5:комплексных rho_k {len(cpl)} из {len(pol)}; вещественных {len(pol) - len(cpl)}")
    print("  Рост Im rho_k (верхняя полуплоскость) против ln Re rho:")
    up = cpl[cpl.imag > 0]
    for lo, hi in ((0, 20), (20, 40), (40, 60), (60, 80), (80, 100)):
        sel = up[(up.real > 0)]
        sel = sel[(sel.real >= (lo / 100) * pol.real.max()) & (sel.real < (hi / 100) * pol.real.max())]
        if len(sel):
            print(f"   Re rho in [{lo / 100 * pol.real.max():6.1f},{hi / 100 * pol.real.max():6.1f}): n={len(sel):3d} "
                  f"Im min/mean/max = {sel.imag.min():.4f}/{sel.imag.mean():.4f}/{sel.imag.max():.4f}")
    sel = up[up.real > 0.3 * pol.real.max()]
    sl_, ic = np.polyfit(np.log(sel.real), sel.imag, 1)
    print(f"  регрессия Im = s ln Re + b по Re > 0.3 Re_max (n={len(sel)}): s={sl_:.4f}, b={ic:.4f}")
    print(f"  ориентиры: 1/L={1 / L:.4f}; 1/(L-|d|)={1 / (L - abs(d)):.4f} (= 1/(2 min l))")


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'all'
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    Ns = tuple(int(s) for s in sys.argv[3].split(',')) if len(sys.argv) > 3 else (400, 600, 800)
    T0 = time.time()
    if mode in ('check', 'all'):
        check()
    if mode in ('cases', 'all'):
        which = sys.argv[4].split(',') if len(sys.argv) > 4 else None
        out = cases(K, Ns, which)
        if '5' in out:
            case5_growth(out['5'], K)
    print(f"\nОбщее время: {time.time() - T0:.1f} с")
