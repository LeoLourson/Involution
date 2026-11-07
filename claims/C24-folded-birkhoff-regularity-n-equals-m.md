---
id: C24
title: Случай n=m второго порядка с общими двухточечными условиями — главная часть характеристического определителя, регулярность и асимптотика собственных значений с остатком o(1)
status: own-result
depends_on: [S50, I43]
checked_by: [referee 2026-10-26]
---

Линия G (общие двухточечные условия, раздел «Две линии исследования» в `claims/question.md`):
оператор $-y''(x)-a(x)y''(-x)$ без младших членов. Запись переносит идею I43 с поправками её
раздела «Критика» (2026-10-25): исправлена главная часть вида $(1,0)$ при $\varepsilon=-1$,
рассуждение Руше выписано по теореме 1 работы S50 без ссылки на формулу (8) её теоремы 2,
члены нулевого порядка в условиях первого порядка учтены в том же рассуждении. Остаток
$O(1/k)$, асимптотика собственных функций (утверждение (B) идеи) и оценка $O(k^{-1/2})$ в
случае Дирихле сюда не входят (раздел «Границы»).

## Постановка и обозначения

Уравнение на $[-1,1]$:

$$
-y''(x)-a(x)y''(-x)=\lambda y(x), \tag{1}
$$

условия

$$
U_j(y)=\alpha_{j1}y'(-1)+\alpha_{j0}y(-1)+\beta_{j1}y'(1)+\beta_{j0}y(1)=0,\qquad j=1,2, \tag{2}
$$

с комплексными коэффициентами. Собственное значение задачи (1), (2) — число $\lambda\in\mathbb C$, для
которого есть $y\in W^2_1(-1,1)$, $y\not\equiv0$, с (1) почти всюду и (2).

**Условия на краевые формы.** Формы $U_1,U_2$ линейно независимы и нормированы в смысле S48,
с. 645: порядок $\kappa_j\in\lbrace0,1\rbrace$ формы $U_j$ — наибольший порядок производной с
ненулевым коэффициентом, и сумму $\kappa_1+\kappa_2$ нельзя понизить, переходя к линейным
комбинациям. С точностью до перестановки $U_1,U_2$ вид $(\kappa_1,\kappa_2)$ есть $(0,0)$, $(1,1)$
или $(1,0)$; для вида $(0,0)$ коэффициенты при производных равны нулю, для $(1,0)$ — у $U_2$.
Главная часть $U_j^0(y)=\alpha_{j\kappa_j}y^{(\kappa_j)}(-1)+\beta_{j\kappa_j}y^{(\kappa_j)}(1)$ (S48,
формула (1.1)). Положим

$$
J_0=\alpha_{10}\beta_{20}-\beta_{10}\alpha_{20},\qquad J_1=\beta_{11}\alpha_{21}-\alpha_{11}\beta_{21}.
$$

**Гипотеза (H).** $a$ вещественна, $a\in W^1_1(-1,1)$, $\lvert a\rvert\ge m>0$ и
$p(x)=a(x)a(-x)\le\kappa<1$ (постоянная $\kappa$ не путается с порядками $\kappa_1,\kappa_2$:
у порядков всегда стоит индекс).

**Обозначения на $[0,1]$.** $\varepsilon=\operatorname{sign}a$ (шаг 1), $\sigma_\pm=1\pm\sqrt p$,
$\tau_\pm=\sigma_\pm^{-1/2}$, $t_\pm(x)=\int_0^x\tau_\pm$, $\ell_\pm=t_\pm(1)$, $L=\ell_++\ell_-$,
$d=\ell_+-\ell_-$, $\omega_\pm=\tau_\pm(1)$, $\tau^0_\pm=\tau_\pm(0)$; $\tau^0_\varepsilon$ означает
$\tau^0_+$ при $\varepsilon=1$ и $\tau^0_-$ при $\varepsilon=-1$. Далее
$k(x)=\varepsilon\sqrt{a(-x)/a(x)}$, $\varkappa=k(1)=\varepsilon\sqrt{a(-1)/a(1)}$,

$$
P_j^\pm=\beta_{j1}\mp\varkappa\alpha_{j1},\qquad Q_j^\pm=\beta_{j0}\pm\varkappa\alpha_{j0},
$$

$$
\mathcal A=\omega_+P_1^+Q_2^-=\omega_+(\beta_{11}-\varkappa\alpha_{11})(\beta_{20}-\varkappa\alpha_{20}),\qquad
\mathcal B=\omega_-P_1^-Q_2^+=\omega_-(\beta_{11}+\varkappa\alpha_{11})(\beta_{20}+\varkappa\alpha_{20}).
$$

**Главная часть $F$.** По виду условий и знаку $\varepsilon$:

| вид | $F$ при $\varepsilon=1$ | $F$ при $\varepsilon=-1$ | $\gamma_U$ |
| --- | --- | --- | --- |
| $(0,0)$ | $\cos\rho\ell_+\sin\rho\ell_-$ | $\sin\rho\ell_+\cos\rho\ell_-$ | $-8i\varkappa J_0$ |
| $(1,1)$ | $\sin\rho\ell_+\cos\rho\ell_-$ | $\cos\rho\ell_+\sin\rho\ell_-$ | $8i\omega_+\omega_-\varkappa J_1$ |
| $(1,0)$ | $\mathcal A\sin\rho\ell_+\sin\rho\ell_-+\mathcal B\cos\rho\ell_+\cos\rho\ell_-$ | $\mathcal A\cos\rho\ell_+\cos\rho\ell_-+\mathcal B\sin\rho\ell_+\sin\rho\ell_-$ | $4i\varepsilon$ |

Разложим $F(\rho)=\theta_+e^{i\rho L}+\theta_-e^{-i\rho L}+\theta_d^+e^{i\rho d}+\theta_d^-e^{-i\rho d}$
(шаг 8 показывает, что так можно, и даёт $\theta_-=\pm\theta_+$); положим $\theta=\theta_+$.

**Характеристический определитель.** $\Phi(x,\lambda)$ — матрица Коши ($\Phi(0,\lambda)=I$)
системы $X'=\begin{pmatrix}0&I\\-\lambda M^{-1}&0\end{pmatrix}X$ для $X=(w,w')$, где
$M(x)=\begin{pmatrix}1&a(x)\\a(-x)&1\end{pmatrix}$, и

$$
\Delta(\lambda)=\det\bigl(V_0+V_1\Phi(1,\lambda)\bigr),
$$

где строки $V_0$: $(1,-1,0,0)$, $(0,0,1,1)$, $0$, $0$; строки $V_1$: $0$, $0$,
$(\beta_{j0},\alpha_{j0},\beta_{j1},-\alpha_{j1})$, $j=1,2$. Функция
$G(\lambda)$ задана равенством $G(\rho^2)=\rho^{\kappa_1+\kappa_2-1}F(\rho)$ (шаг 13 показывает,
что $G$ — целая функция $\lambda$).

## Определение

Задача (1), (2) при (H) **регулярна**, если $\theta\ne0$. **Усиленно регулярна**, если она
регулярна, нули $F$ в полуплоскости $\operatorname{Re}\rho\ge0$ попарно отделены
($\inf\lvert\rho^0-\rho^{0\prime}\rvert>0$ по парам различных нулей) и все они, кроме конечного числа,
простые.

Определение проверяется по коэффициентам $U^0$ и по $a(\pm1)$, $\ell_\pm$; базисность в нём не
участвует. По шагу 10 регулярность совпадает с регулярностью задачи с условиями $U^0$ в смысле
S50 (определение, с. 798), а усиленная регулярность — с сильной регулярностью там же.

## Утверждение

Пусть выполнены (H) и условия на краевые формы.

1. (Складывание.) $\lambda$ — собственное значение задачи (1), (2) тогда и только тогда, когда
   $\Delta(\lambda)=0$; $\Delta$ — целая функция, $\Delta\not\equiv0$ при регулярности.
2. (Главная часть.) Существуют $c_\ast\ne0$ и функция $\eta$, голоморфная при $\rho\ne0$, такие что
   $$
   \rho^{1-\kappa_1-\kappa_2}\Delta(\rho^2)=c_\ast\bigl(F(\rho)+\eta(\rho)\bigr),\qquad
   \sup_{\lvert\rho\rvert\ge r}\lvert\eta(\rho)\rvert e^{-L\lvert\operatorname{Im}\rho\rvert}\to0\quad(r\to\infty),
   $$
   $$
   c_\ast=\frac{i\varepsilon\gamma_U\tau^0_\varepsilon}{4\lvert\varkappa\rvert\sqrt{\omega_+\omega_-\tau^0_+\tau^0_-}} .
   $$
   Это верно для полных условий $U=U^0+\rho^{-1}U^1$ (шаг 4), а $F$ зависит только от $U^0$.
   Определитель упрощённой задачи S50 (формула (7), с. 798) для условий $U^0$ равен $c_UF(\rho)$,
   $c_U\ne0$, в нормировке S50 и $c_U\rho^{N}F(\rho)$, $N=1+\kappa_1+\kappa_2$, в переменных
   $(w,w')$ с ненормированными формами $U^0_j$; $\theta_+$, $\theta_-$ с точностью до общего
   множителя $c_U\ne0$ — коэффициенты $c_1$, $c_0$ из (7) S50. Регулярность ($\theta\ne0$)
   выполнена всегда для видов $(0,0)$ и $(1,1)$ и равносильна $\mathcal A\ne\mathcal B$ для вида $(1,0)$.
3. (A, асимптотика собственных значений.) Пусть задача регулярна. Тогда:
   - существуют $h,R_0>0$: каждое собственное значение с $\lvert\lambda\rvert\ge R_0$ удовлетворяет
     $\lvert\operatorname{Im}\sqrt\lambda\rvert\le h$;
   - нули $\Delta$ и нули $G$, каждый повторённый по кратности нуля, можно занумеровать как
     $\lambda_k$, $\lambda_k^0$, $k\ge1$, так что $\sqrt{\lambda_k}-\sqrt{\lambda_k^0}\to0$ (ветвь
     $\operatorname{Re}\sqrt{\cdot}\ge0$); при больших $k$ число $\sqrt{\lambda_k^0}$ — нуль $F$ с
     $\operatorname{Re}\rho>0$ той же кратности;
   - если задача усиленно регулярна, то при больших $\lvert\lambda\rvert$ все нули $\Delta$ простые и
     собственные подпространства одномерны.
4. (C, Дирихле: $U_1=y(-1)$, $U_2=y(1)$.) Задача регулярна при любом $a$ из (H); нули $F$ — серии
   $\pi(n-\tfrac12)/\ell_+$ и $\pi n/\ell_-$ при $\varepsilon=1$, $\pi n/\ell_+$ и $\pi(n-\tfrac12)/\ell_-$
   при $\varepsilon=-1$, $n\in\mathbb Z$. Задача усиленно регулярна тогда и только тогда, когда
   $\ell_+/\ell_-=r/s$ — несократимая дробь с нечётным $s$ при $\varepsilon=1$ и с нечётным $r$ при
   $\varepsilon=-1$.
5. (D, вид $(1,0)$.) Пусть $\mathcal A\ne\mathcal B$ и $\gamma=\varepsilon(\mathcal A+\mathcal B)/(\mathcal B-\mathcal A)$.
   Если $\lvert\gamma\rvert\cosh(\lvert d\rvert r)<\sin(Lr)$ при некотором $r\in(0,\pi/(2L))$ — это следует из
   $\lvert\gamma\rvert\cosh(\pi d/(2L))<1$ (шаг 16), обратное неверно, — то каждый нуль $F$ лежит в одном из
   кругов радиуса $r$ вокруг $\pi(n-\tfrac12)/L$, $n\in\mathbb Z$, каждый такой круг содержит ровно
   один нуль, он простой, и задача усиленно регулярна. Если, кроме того, $\gamma\in\mathbb R$, то все нули
   $F$ вещественны.
6. (E, регуляризация отражением.) Для $U_1=y'(1)+y'(-1)$, $U_2=y(1)-y(-1)$ (вид $(1,0)$)
   $\mathcal A=\omega_+(1-\varkappa^2)$, $\mathcal B=\omega_-(1-\varkappa^2)$, и задача регулярна тогда и только
   тогда, когда $a(1)\ne a(-1)$. При $a=0$ (вне (H)) и при чётном $a$ из (H) каждое
   $\lambda\in\mathbb C$ — собственное значение.

**Отличие от идеи I43.** Главная часть вида $(1,0)$ при $\varepsilon=-1$ — по критике
($\cos\leftrightarrow\sin$ в каждом сомножителе), отсюда знак $\varepsilon$ в $\gamma$ пункта 5.
В (D) достаточно условия с $r$; оно следует из строгого неравенства $\lvert\gamma\rvert\cosh(\pi d/(2L))<1$ без запаса, но
вывод сужен до усиленной регулярности: остаток $O(1/k)$ не утверждается. В (A) нет второй
части идеи (группы из $\nu$ нулей, $O(k^{-1/\nu})$). В (C) нет оценки $O(k^{-1/2})$. Утверждение
(B) идеи не доказывается. В (E) добавлено: при чётном $a$ задача вырождена. Нормировка
главной части отличается от идеи: идея пишет $c\rho^N(F+o(\cdot))$ для определителя на
асимптотических решениях в переменных $(w,w')$, здесь $\Delta(\rho^2)$ построен по матрице Коши;
связь — шаг 9.

## Внешний вход

- S50 (А. А. Шкаликов, Матем. заметки 110:5 (2021), 796–800), теорема 1, с. 797; карточка S50,
  сверена (source-verifier 2026-10-26). Используется только асимптотическая фундаментальная матрица
  для системы $y'-A(x)y=\zeta B(x)y$ с диагональной $B$, условием (4) и $A\in L_1$, причём в шаге 6
  диагональ $A$ снята заменой, поэтому амплитудный множитель теоремы равен $I$ при обоих прочтениях
  напечатанного $\operatorname{diag}\lbrace e^{a_{jj}(x)}\rbrace$ (пометка карточки). Остаток в
  теореме 1 — $o(1)$, скорость не утверждается. Теоремы 2, 3, 6 S50 не используются. S50 —
  краткое сообщение без доказательств; доказательство теоремы 1 опирается на работу [5] из S50
  (Савчук–Шкаликов, Матем. сб. 211:11, 2020), карточки на неё нет.
- Четыре гипотезы, которые сверка S50 отметила как непроверенные в абзаце «Применимость к I43»
  карточки, проверены здесь: знакопостоянство и $p\ge m^2$ (шаг 1), строгая гиперболичность с
  явным запасом (шаг 5), нумерация под (4) с $s=2$ (шаг 5), абсолютная непрерывность $W$ и
  ограниченность $W^{-1}$ (шаг 5).
- Определение нормированных условий — S48, с. 645 (поиском по тексту источника; карточки на
  S48 нет). Определение только фиксирует класс условий, теоремы S48 не используются.
- Стандартные факты без ссылки на источник: целостность матрицы Коши по параметру; теорема
  Руше для ограниченной области с кусочно-гладкой границей; теорема Гурвица; неравенство
  Йенсена для числа нулей в круге; плотность $\lbrace m\alpha\rbrace$ по модулю $1$ при
  иррациональном $\alpha$ (Кронекер).
- Решения пользователя: младших членов в уравнении нет (раздел «Две линии исследования»
  постановки); других решений о внешних входах для этой записи не было.

## Доказательство

**Шаг 1 (свойства $a$).** $W^1_1(-1,1)\subset AC[-1,1]$, поэтому $a$ непрерывна и при
$\lvert a\rvert\ge m$ знакопостоянна: $a=\varepsilon\lvert a\rvert$. Отсюда
$p(x)=\lvert a(x)\rvert\lvert a(-x)\rvert\in[m^2,\kappa]$, $\sigma_-\ge1-\sqrt\kappa>0$,
$\sigma_+\le1+\sqrt\kappa<2$, $\sigma_+-\sigma_-=2\sqrt p\ge2m$. Функции $\sqrt p$, $\tau_\pm$ и
$k=\varepsilon(\lvert a(-x)\rvert/\lvert a(x)\rvert)^{1/2}$ абсолютно непрерывны на $[0,1]$: это
композиции абсолютно непрерывных функций со значениями в отрезке, отделённом от нуля, с
функциями, липшицевыми на этом отрезке. Далее
$(m/\lVert a\rVert_\infty)^{1/2}\le\lvert k\rvert\le(\lVert a\rVert_\infty/m)^{1/2}$, $k(0)=\varepsilon$,
$k(1)=\varkappa\ne0$, $\varkappa^2=a(-1)/a(1)$. Так как $\tau_+<\tau_-$ поточечно, $\ell_+<\ell_-$,
то есть $d<0$ и $0<\lvert d\rvert<L$.

**Шаг 2 (складывание).** Пусть $y\in W^2_1(-1,1)$ удовлетворяет (1) почти всюду. Положим
$w(x)=(y(x),y(-x))$, $x\in[0,1]$. Тогда $w\in W^2_1(0,1)^2$, $w_2'(x)=-y'(-x)$,
$w_2''(x)=y''(-x)$ почти всюду. Множество точек $x\in(0,1)$, где (1) нарушено в $x$ или в $-x$,
имеет меру нуль, поэтому почти всюду на $(0,1)$

$$
-w_1''-a(x)w_2''=\lambda w_1,\qquad -w_2''-a(-x)w_1''=\lambda w_2,\qquad\text{то есть}\quad -Mw''=\lambda w .
$$

$\det M=1-p\ge1-\kappa>0$, $M^{-1}$ непрерывна, так что $w''=-\lambda M^{-1}w$ почти всюду, $w''$
равна почти всюду непрерывной функции, и $w\in C^2[0,1]$. В нуле $w_1(0)=w_2(0)=y(0)$,
$w_1'(0)=y'(0)=-w_2'(0)$. В единице $y(1)=w_1(1)$, $y(-1)=w_2(1)$, $y'(1)=w_1'(1)$,
$y'(-1)=-w_2'(1)$, поэтому

$$
U_j(y)=\beta_{j0}w_1(1)+\alpha_{j0}w_2(1)+\beta_{j1}w_1'(1)-\alpha_{j1}w_2'(1). \tag{3}
$$

Обратно, если $w\in C^2[0,1]^2$ решает $w''=-\lambda M^{-1}w$ с $w_1(0)=w_2(0)$,
$w_1'(0)+w_2'(0)=0$, то $y(x)=w_1(x)$ при $x\ge0$, $y(x)=w_2(-x)$ при $x<0$ лежит в $C^1[-1,1]$
(значения и односторонние производные в нуле совпадают), $y'$ кусочно непрерывно
дифференцируема, поэтому $y\in W^2_\infty(-1,1)\subset W^2_1(-1,1)$, и (1) выполнено на каждой
половине. Отображение $y\mapsto w$ линейно и инъективно.

**Шаг 3 (утверждение 1).** Решения $w''=-\lambda M^{-1}w$ образуют четырёхмерное пространство:
$(w,w')(x)=\Phi(x,\lambda)(w(0),w'(0))$. Коэффициенты системы непрерывны по $x$ и линейны по
$\lambda$; последовательные приближения сходятся равномерно на $[0,1]\times\lbrace\lvert\lambda\rvert\le R\rbrace$,
поэтому $\Phi(x,\cdot)$ — целая `[стандартный факт]`. Условия в нуле и (3) записываются как
$(V_0+V_1\Phi(1,\lambda))(w(0),w'(0))=0$. По шагу 2 пространство собственных функций при данном
$\lambda$ изоморфно $\ker(V_0+V_1\Phi(1,\lambda))$, и $\lambda$ — собственное значение тогда и
только тогда, когда $\Delta(\lambda)=0$. Утверждение $\Delta\not\equiv0$ при регулярности — шаг 11:
$\lvert F(iy)\rvert\ge\tfrac12\lvert\theta\rvert e^{Ly}$ при больших $y$, а $\lvert\eta(iy)\rvert e^{-Ly}\to0$.

**Шаг 4 (переменные $Y$).** При $\rho\ne0$ положим $S_\rho=\operatorname{diag}(1,1,\rho^{-1},\rho^{-1})$,
$Y=S_\rho(w,w')=(w,w'/\rho)$. Тогда $Y'=\rho KY$, $K=\begin{pmatrix}0&I\\-M^{-1}&0\end{pmatrix}$, и
$Y_c(x,\rho)=S_\rho\Phi(x,\rho^2)S_\rho^{-1}$ — матрица Коши этой системы. Пусть
$\Lambda_\rho=\operatorname{diag}(1,\rho^{-1},\rho^{-\kappa_1},\rho^{-\kappa_2})$,
$\widetilde U_0=\Lambda_\rho V_0S_\rho^{-1}$, $\widetilde U_1=\Lambda_\rho V_1S_\rho^{-1}$. Прямой подсчёт:
строки $\widetilde U_0$ — $(1,-1,0,0)$, $(0,0,1,1)$, $0$, $0$; строка $2+j$ матрицы
$\widetilde U_1$ при $\kappa_j=1$ равна

$$
(0,0,\beta_{j1},-\alpha_{j1})+\rho^{-1}(\beta_{j0},\alpha_{j0},0,0)=:U_j^0+\rho^{-1}U_j^1,
$$

при $\kappa_j=0$ — $(\beta_{j0},\alpha_{j0},0,0)=:U_j^0$, $U^1_j=0$. Строки $U_j^0$ отвечают главным
частям $U_j^0(y)$ (после деления на $\rho^{\kappa_j}$). Положим
$\Delta_Y(\rho)=\det(\widetilde U_0+\widetilde U_1Y_c(1,\rho))$. Поскольку
$\widetilde U_0+\widetilde U_1Y_c(1,\rho)=\Lambda_\rho(V_0+V_1\Phi(1,\rho^2))S_\rho^{-1}$,

$$
\Delta_Y(\rho)=\det\Lambda_\rho\cdot\Delta(\rho^2)\cdot\det S_\rho^{-1}=\rho^{1-\kappa_1-\kappa_2}\Delta(\rho^2). \tag{4}
$$

**Шаг 5 (диагонализация; гипотезы S50).** При $\zeta=i\rho$ система $Y'=\rho KY$ есть
$Y'=\zeta BY$, $B=-iK$, то есть (1) S50 с $A=0$. Если $Me=\sigma e$, то
$K(e,i s\sigma^{-1/2}e)=is\sigma^{-1/2}(e,is\sigma^{-1/2}e)$, $s=\pm1$. Собственные векторы $M$:
$e_\pm=(1,\pm k)$, $Me_\pm=\sigma_\pm e_\pm$ (первая строка: $1\pm ak=1\pm\sqrt p$, так как
$ak=\varepsilon\lvert a\rvert\cdot\varepsilon\sqrt{p}/\lvert a\rvert$; вторая: $a(-x)\pm k=\sigma_\pm(\pm k)$
равносильно $a(-x)=ak^2$). Положим

$$
g_{\pm,s}=(e_\pm,\ is\tau_\pm e_\pm),\qquad Bg_{\pm,s}=s\tau_\pm g_{\pm,s}.
$$

Собственные значения $B$ упорядочены так:
$b_1=-\tau_-<b_2=-\tau_+<0<b_3=\tau_+<b_4=\tau_-$ (столбцы $g_{-,-},g_{+,-},g_{+,+},g_{-,+}$) —
условие (4) S50 с $s=2$. Запас (5) S50: $\tau_+\ge(1+\sqrt\kappa)^{-1/2}$, $\tau_-\le(1-\sqrt\kappa)^{-1/2}$ и
по теореме Лагранжа для $t\mapsto t^{-1/2}$ на $[1-\sqrt\kappa,1+\sqrt\kappa]$:
$\tau_--\tau_+\ge\tfrac12(1+\sqrt\kappa)^{-3/2}(\sigma_+-\sigma_-)\ge m(1+\sqrt\kappa)^{-3/2}$.

Пусть $W(x)$ — матрица со столбцами $g_{+,+},g_{+,-},g_{-,+},g_{-,-}$ (порядок столбцов ниже
везде такой; переход к порядку $b_1<\dots<b_4$ — перестановка, которая не меняет рассуждений).
Вычитая столбцы одного канала и переставляя, получаем
$\det W=4\tau_+\tau_-(\det(e_+,e_-))^2=16k^2\tau_+\tau_-$, так что
$\det W\ge16(m/\lVert a\rVert_\infty)(1+\sqrt\kappa)^{-1}>0$
равномерно ($k^2\ge m/\lVert a\rVert_\infty$, $\tau_-\ge\tau_+\ge(1+\sqrt\kappa)^{-1/2}$); в частности $\det W(0)=16\tau^0_+\tau^0_-$. Элементы $W$ абсолютно непрерывны (шаг 1),
$W^{-1}=\operatorname{adj}W/\det W$ ограничена и абсолютно непрерывна.

Строки $W^{-1}$. Левые собственные векторы $M$: $f_\pm=(1,\pm1/k)$, $f_\pm M=\sigma_\pm f_\pm$ (та же
проверка с заменой $a(x)\leftrightarrow a(-x)$, $1/k=\varepsilon\sqrt{a(x)/a(-x)}$), $f_\pm\cdot e_\pm=2$,
$f_\pm\cdot e_\mp=0$. Строка $W^{-1}$, отвечающая $g_{\pm,s}$, равна $\tfrac14(f_\pm,\ \mu^{-1}f_\pm)$ с
$\mu=is\tau_\pm$: её произведение на $g_{\pm,s}$ равно $1$, на $g_{\pm,-s}$ и на столбцы другого
канала — $0$.

Замена $Y=WZ$ даёт $Z'=AZ+\zeta\widehat BZ$, $\widehat B=\operatorname{diag}(b)$ в порядке столбцов,
$A=-W^{-1}W'\in L_1(0,1)$ (так как $W'\in L_1$, $W^{-1}$ ограничена). Диагональный элемент для
$g_{\pm,s}$:

$$
a_{\pm}:=-\tfrac14\bigl(f_\pm\cdot e_\pm'+\mu^{-1}(\mu e_\pm)'\cdot f_\pm\bigr)
=-\tfrac12f_\pm\cdot e_\pm'-\frac{\mu'}{2\mu}=-\frac{k'}{2k}-\frac{\tau_\pm'}{2\tau_\pm},
$$

поскольку $f_\pm\cdot e_\pm'=(\pm1/k)(\pm k')$ и $\mu'/\mu=\tau_\pm'/\tau_\pm$. Он вещественен и не
зависит от $s$ (поправка критики к шагу 3 идеи). Положим
$D_\pm(x)=\exp\int_0^xa_\pm=\bigl(\tau^0_\pm/(\lvert k(x)\rvert\tau_\pm(x))\bigr)^{1/2}$ (здесь $\lvert k(0)\rvert=1$) и
$\mathbf D=\operatorname{diag}(D_+,D_+,D_-,D_-)$.

**Шаг 6 (теорема 1 S50).** Замена $Z=\mathbf D\widetilde Z$ даёт
$\widetilde Z'-\widetilde A\widetilde Z=\zeta\widehat B\widetilde Z$ с
$\widetilde A=\mathbf D^{-1}A\mathbf D-\operatorname{diag}(a_+,a_+,a_-,a_-)$: так как $\mathbf D^{-1}\mathbf D'$ —
диагональ $A$, а $\mathbf D$ и $\widehat B$ диагональны. У $\widetilde A$ нулевая диагональ, элементы в
$L_1$ ($\mathbf D^{\pm1}$ непрерывны). Гипотезы теоремы 1 S50 (диагональная $\widehat B$, (4),
$\widetilde A\in L_1$) выполнены, амплитудный множитель теоремы равен $I$. По теореме 1 при $h=0$ в
каждой из полуплоскостей $\Pi_-=\lbrace\operatorname{Re}\zeta\ge0\rbrace=\lbrace\operatorname{Im}\rho\le0\rbrace$
и $\Pi_+=\lbrace\operatorname{Im}\rho\ge0\rbrace$ существует фундаментальная матрица
$\widetilde Z_a=(I+R)E$, $E=\operatorname{diag}(e^{\zeta p_j(x)})$, $p_j=\int_0^xb_j$, и
$\epsilon_0(r)=\sup\lbrace\lvert R(x,\rho)\rvert:x\in[0,1],\ \lvert\rho\rvert\ge r\rbrace\to0$ (отдельно в каждой
полуплоскости; берём максимум двух). Для столбца $(\pm,s)$: $\zeta p_j(x)=is\rho t_\pm(x)$. Значит,
$Y_a=W\mathbf D(I+R)E$ — фундаментальная матрица $Y'=\rho KY$, и её столбцы

$$
y_{\pm,s}(x,\rho)=\bigl(D_\pm(x)g_{\pm,s}(x)+r_{\pm,s}(x,\rho)\bigr)e^{is\rho t_\pm(x)},\qquad
\lvert r_{\pm,s}\rvert\le C_W\epsilon_0(\lvert\rho\rvert), \tag{5}
$$

где $C_W$ — оценка $\lvert W\mathbf D\rvert$ на $[0,1]$.

**Шаг 7 (главная часть определителя на $Y_a$).** Пусть $\mathfrak U_a(\rho)=\widetilde U_0Y_a(0)+\widetilde U_1Y_a(1)$
и $\mathfrak U^0(\rho)$ — та же матрица, в которой $r_{\pm,s}=0$ и $U_j^1=0$. Её строки 1, 2 — значения
форм $Y_1-Y_2$, $Y_3+Y_4$ на $g_{\pm,s}(0)$ ($D_\pm(0)=1$, $t_\pm(0)=0$), строки $2+j$ — значения $U_j^0$ на
$D_\pm(1)g_{\pm,s}(1)e^{is\rho\ell_\pm}$. Каждый элемент $\mathfrak U_a$ отличается от элемента
$\mathfrak U^0$ на $(o(1)+O(\rho^{-1}))e^{is\rho\ell_\pm}$ в строках точки $1$ и на $o(1)$ в строках точки
$0$, равномерно в $\Pi_\pm$; все элементы $\mathfrak U^0$, делённые на свой экспоненциальный множитель,
ограничены. Разложение Лапласа по строкам 1, 2: каждое слагаемое есть минор строк точки $0$
(ограничен) на минор строк точки $1$ по двум оставшимся столбцам, а последний содержит множитель
$e^{i\rho P}$, где $P$ — сумма показателей $s\ell_\pm$ двух различных столбцов, то есть
$P\in\lbrace0,\pm d,\pm L\rbrace$ и $\lvert P\rvert\le L$, $\lvert e^{i\rho P}\rvert\le e^{L\lvert\operatorname{Im}\rho\rvert}$. Отсюда

$$
\det\mathfrak U_a(\rho)=\det\mathfrak U^0(\rho)+\eta_1(\rho),\qquad
\lvert\eta_1(\rho)\rvert\le\epsilon_1(\lvert\rho\rvert)e^{L\lvert\operatorname{Im}\rho\rvert},\quad\epsilon_1(r)\to0. \tag{6}
$$

Вычислим $\det\mathfrak U^0$. На $g_{\pm,s}(0)=(1,\pm\varepsilon,is\tau^0_\pm,\pm is\tau^0_\pm\varepsilon)$:
$Y_1-Y_2=1\mp\varepsilon$, $Y_3+Y_4=is\tau^0_\pm(1\pm\varepsilon)$. При $\varepsilon=1$ строки точки $0$ по
столбцам $(+,+),(+,-),(-,+),(-,-)$ равны $(0,0,2,2)$ и $(2i\tau^0_+,-2i\tau^0_+,0,0)$; при $\varepsilon=-1$ —
$(2,2,0,0)$ и $(0,0,2i\tau^0_-,-2i\tau^0_-)$. На $g_{\pm,s}(1)=(1,\pm\varkappa,is\omega_\pm,\pm is\omega_\pm\varkappa)$:
$U_j^0=is\omega_\pm P_j^\pm$ при $\kappa_j=1$ и $U_j^0=Q_j^\pm$ при $\kappa_j=0$. Множители $D_\pm(1)$
вынесем позже.

При $\varepsilon=1$ заменим столбец $(+,-)$ суммой столбцов $(+,+)$ и $(+,-)$, а столбец $(-,-)$ —
разностью $(-,-)$ минус $(-,+)$; определитель не меняется. Строки точки $0$ становятся
$(0,0,2,0)$, $(2i\tau^0_+,0,0,0)$, а в строке $2+j$ во втором и четвёртом столбцах стоят
$\varphi_j=\sum_su^{+,s}_j$ и $\psi_j=u^{-,-}_j-u^{-,+}_j$, где $u^{\pm,s}_j$ — элементы строки до
замены (с множителями $D_\pm(1)$). Разложение по строкам 1, 2 даёт $4i\tau^0_+(\varphi_1\psi_2-\psi_1\varphi_2)$.
При $\varepsilon=-1$ заменяем $(+,-)$ на $(+,-)-(+,+)$ и $(-,-)$ на $(-,-)+(-,+)$, получаем
$-4i\tau^0_-(\varphi_1\psi_2-\psi_1\varphi_2)$ с $\varphi_j=u^{+,-}_j-u^{+,+}_j$, $\psi_j=\sum_su^{-,s}_j$.
Прямой подсчёт по формулам Эйлера (таблица — без множителей $D_\pm(1)$: истинные $\varphi_j$, $\psi_j$
равны табличным, умноженным на $D_+(1)$ и $D_-(1)$, так как столбцы одного канала несут в строках
точки $1$ один и тот же множитель):

| | $\varphi_j$, $\varepsilon=1$ | $\psi_j$, $\varepsilon=1$ | $\varphi_j$, $\varepsilon=-1$ | $\psi_j$, $\varepsilon=-1$ |
| --- | --- | --- | --- | --- |
| $\kappa_j=1$ | $-2\omega_+P_j^+\sin\rho\ell_+$ | $-2i\omega_-P_j^-\cos\rho\ell_-$ | $-2i\omega_+P_j^+\cos\rho\ell_+$ | $-2\omega_-P_j^-\sin\rho\ell_-$ |
| $\kappa_j=0$ | $2Q_j^+\cos\rho\ell_+$ | $-2iQ_j^-\sin\rho\ell_-$ | $-2iQ_j^+\sin\rho\ell_+$ | $2Q_j^-\cos\rho\ell_-$ |

В каждом слагаемом $\varphi_1\psi_2-\psi_1\varphi_2$ один множитель — из канала $+$, другой — из канала
$-$, поэтому множители $D_\pm(1)$ дают общий множитель $D_+(1)D_-(1)$, а $\varphi_j$, $\psi_j$ ниже — табличные.
Итак,

$$
\det\mathfrak U^0(\rho)=D_+(1)D_-(1)\cdot4i\varepsilon\tau^0_\varepsilon\cdot(\varphi_1\psi_2-\psi_1\varphi_2). \tag{7}
$$

**Шаг 8 (главная часть по видам).** Из таблицы шага 7:

- вид $(0,0)$: $\varphi_1\psi_2-\psi_1\varphi_2=-4i(Q_1^+Q_2^--Q_1^-Q_2^+)\cdot F$, и
  $Q_1^+Q_2^--Q_1^-Q_2^+=2\varkappa J_0$;
- вид $(1,1)$: $\varphi_1\psi_2-\psi_1\varphi_2=4i\omega_+\omega_-(P_1^+P_2^--P_1^-P_2^+)\cdot F$, и
  $P_1^+P_2^--P_1^-P_2^+=2\varkappa J_1$;
- вид $(1,0)$: при $\varepsilon=1$
  $\varphi_1\psi_2-\psi_1\varphi_2=4i(\omega_+P_1^+Q_2^-\sin\rho\ell_+\sin\rho\ell_-+\omega_-P_1^-Q_2^+\cos\rho\ell_+\cos\rho\ell_-)$,
  при $\varepsilon=-1$
  $\varphi_1\psi_2-\psi_1\varphi_2=-4i(\omega_+P_1^+Q_2^-\cos\rho\ell_+\cos\rho\ell_-+\omega_-P_1^-Q_2^+\sin\rho\ell_+\sin\rho\ell_-)$.

То есть $\varphi_1\psi_2-\psi_1\varphi_2=\gamma_UF$ с $F$ и $\gamma_U$ из таблицы постановки.
$\gamma_U\ne0$: $\varkappa\ne0$ (шаг 1); $J_0\ne0$ — это линейная независимость форм вида $(0,0)$;
$J_1\ne0$ для вида $(1,1)$ — иначе $(\alpha_{21},\beta_{21})=c(\alpha_{11},\beta_{11})$ (оба вектора ненулевые),
и $U_2-cU_1$ имеет порядок не выше $0$, что противоречит нормированности.

Тригонометрические формы: при $\varepsilon=1$
$\cos\rho\ell_+\sin\rho\ell_-=\tfrac12(\sin\rho L-\sin\rho d)$, $\sin\rho\ell_+\cos\rho\ell_-=\tfrac12(\sin\rho L+\sin\rho d)$,
а для $(1,0)$ $F=\tfrac12(\mathcal B-\mathcal A)\cos\rho L+\tfrac12(\mathcal A+\mathcal B)\cos\rho d$; при $\varepsilon=-1$ для
$(0,0)$, $(1,1)$ меняется только знак при $\sin\rho d$, а для $(1,0)$
$F=\tfrac12(\mathcal A-\mathcal B)\cos\rho L+\tfrac12(\mathcal A+\mathcal B)\cos\rho d$. Так как $0<\lvert d\rvert<L$ (шаг 1), четыре
частоты $\pm L,\pm d$ различны, и коэффициенты определены однозначно:
$\theta_+=-\theta_-=-i/4$ для $(0,0)$, $(1,1)$ и $\theta_+=\theta_-=\varepsilon(\mathcal B-\mathcal A)/4$ для $(1,0)$.
Отсюда последняя фраза утверждения 2. Для $(1,0)$
$F=\tfrac{\varepsilon(\mathcal B-\mathcal A)}2(\cos\rho L+\gamma\cos\rho d)$ с $\gamma$ из утверждения 5. Наконец, $F$ чётна для
$(1,0)$ и нечётна для $(0,0)$, $(1,1)$.

**Шаг 9 (утверждение 2).** $Y_a=Y_c\,C(\rho)$ с $C=Y_a(0,\rho)=W(0)(I+R(0,\rho))$ (так как
$\mathbf D(0)=E(0)=I$ и $Y_c(0)=I$), поэтому $\det\mathfrak U_a=\Delta_Y\det C$ и
$\det C=\det W(0)\det(I+R(0,\rho))=16\tau^0_+\tau^0_-(1+o(1))$. Множитель $C(\rho)$ может зависеть от
$\rho$ неголоморфно, но $\Delta_Y$ голоморфна при $\rho\ne0$ по (4). Из (6), (7) и шага 8

$$
\Delta_Y(\rho)=\frac{D_+(1)D_-(1)\cdot4i\varepsilon\tau^0_\varepsilon\gamma_UF(\rho)+\eta_1(\rho)}{16\tau^0_+\tau^0_-(1+o(1))}
=c_\ast\bigl(F(\rho)+\eta(\rho)\bigr),
$$

где $c_\ast=D_+(1)D_-(1)i\varepsilon\tau^0_\varepsilon\gamma_U/(4\tau^0_+\tau^0_-)$ — значение из утверждения 2
после подстановки $D_\pm(1)=(\tau^0_\pm/(\lvert\varkappa\rvert\omega_\pm))^{1/2}$, а
$\lvert\eta(\rho)\rvert\le\epsilon(\lvert\rho\rvert)e^{L\lvert\operatorname{Im}\rho\rvert}$, $\epsilon(r)\to0$: использована оценка
$\lvert F(\rho)\rvert\le C_Fe^{L\lvert\operatorname{Im}\rho\rvert}$, $C_F=2\lvert\theta\rvert+\lvert\theta_d^+\rvert+\lvert\theta_d^-\rvert$.
Функция $\eta=\Delta_Y/c_\ast-F$ голоморфна при $\rho\ne0$ и одна для обеих полуплоскостей. Вместе с
(4) это первая формула утверждения 2.

Связь с нормировкой идеи: определитель условий в переменных $(w,w')$ с ненормированными формами
на столбцах $X_a=S_\rho^{-1}Y_a$ равен $\det(V_0X_a(0)+V_1X_a(1))=\det\Lambda_\rho^{-1}\det\mathfrak U_a
=\rho^{N}\bigl(D_+(1)D_-(1)4i\varepsilon\tau^0_\varepsilon\gamma_UF+\eta_1\bigr)$, $N=1+\kappa_1+\kappa_2$.

**Шаг 10 (упрощённая задача S50; регулярность).** Для условий $U^0$ в переменных $Z$ задача имеет
вид (1), (2) S50 с постоянными матрицами $\widetilde U_0W(0)$ и $\widetilde U_1^0W(1)$. Упрощённая
задача заменяет $A$ его диагональю; её фундаментальная матрица в прочтении карточки S50 — $\mathbf DE$, и
определитель (7) S50 равен $\det(\widetilde U_0W(0)+\widetilde U_1^0W(1)\mathbf D(1)E(1))=\det\mathfrak U^0(\rho)=c_UF(\rho)$,
$c_U=D_+(1)D_-(1)4i\varepsilon\tau^0_\varepsilon\gamma_U\ne0$ (шаги 7, 8). В переменных $(w,w')$ с
ненормированными $U^0_j$ определитель умножается на $\det\Lambda_\rho^{-1}=\rho^N$, как в шаге 9.
Показатели в (7) S50 (в S50 они обозначены $J_0$, $J_1$; здесь $J^{S}_0$, $J^{S}_1$, чтобы не путать с минорами
$J_0$, $J_1$ краевых форм): $J^{S}_0=p_1(1)+p_2(1)=-L$, $J^{S}_1=L$, и $e^{\zeta J^S}=e^{i\rho J^S}$, поэтому $c_1$ и $c_0$
из (7) S50 равны $c_U\theta_+$ и $c_U\theta_-$, а $\lvert\theta_+\rvert=\lvert\theta_-\rvert$ (шаг 8). Значит, регулярность
S50 ($c_0c_1\ne0$ в обозначениях S50) равносильна $\theta\ne0$, полурегулярность невозможна. Сильная
регулярность S50 говорит о нулях той же функции $c_UF$ на всей плоскости; так как нули $F$
симметричны относительно $0$ (шаг 8) и лежат в полосе (шаг 11), а в ограниченной части полосы их
конечное число, она совпадает с усиленной регулярностью. Если бы амплитудный множитель
теоремы 1 S50 понимался буквально, $D_\pm(1)$ заменились бы другими положительными
множителями, зависящими только от канала; вывод $c_0c_1\ne0\iff\theta\ne0$ от этого не меняется.

**Шаг 11 (лемма о $F$).** Пусть $\theta\ne0$.

(i) Выберем $h_0\ge1$ с $\lvert\theta\rvert e^{-2Lh_0}+(\lvert\theta_d^+\rvert+\lvert\theta_d^-\rvert)e^{-(L-\lvert d\rvert)h_0}\le\tfrac12\lvert\theta\rvert$.
При $y=\operatorname{Im}\rho\ge h_0$ слагаемое $\theta_-e^{-i\rho L}$ имеет модуль $\lvert\theta\rvert e^{Ly}$,
остальные — не больше $\lvert\theta\rvert e^{-Ly}$ и $\lvert\theta_d^\pm\rvert e^{\lvert d\rvert y}$, поэтому
$\lvert F(\rho)\rvert\ge\tfrac12\lvert\theta\rvert e^{L\lvert y\rvert}$; при $y\le-h_0$ то же с $\theta_+$. Все нули $F$
лежат в полосе $\lvert\operatorname{Im}\rho\rvert<h_0$.

(ii) Для каждого $\delta>0$ существует $c_\delta>0$: $\lvert F(\rho)\rvert\ge c_\delta e^{L\lvert\operatorname{Im}\rho\rvert}$ при
$\operatorname{dist}(\rho,Z_F)\ge\delta$, $Z_F$ — множество нулей $F$. Вне полосы это (i). Пусть
$K_\delta=\lbrace\lvert\operatorname{Im}\rho\rvert\le h_0,\ \operatorname{dist}(\rho,Z_F)\ge\delta\rbrace$ и, от противного,
$\rho_n\in K_\delta$, $F(\rho_n)\to0$. Запишем $\rho_n=t_n+z_n$, $t_n=\operatorname{Re}\rho_n$. Переходя к
подпоследовательности, $z_n\to z_\ast$, $e^{i\omega t_n}\to u_\omega$, $\lvert u_\omega\rvert=1$, для четырёх
частот $\omega$. Тогда $F_n(\xi)=F(\xi+t_n)\to F_\ast(\xi)=\sum_\omega\theta_\omega u_\omega e^{i\omega\xi}$
равномерно на компактах, $F_\ast\not\equiv0$ (коэффициент при $e^{iL\xi}$ равен $\theta u_L\ne0$, экспоненты
с различными частотами линейно независимы) и $F_\ast(z_\ast)=\lim F(\rho_n)=0$. Но $F_n$ не имеет нулей
в круге $B(z_n,\delta)\supset B(z_\ast,\delta/2)$ при больших $n$, и по теореме Гурвица $F_\ast$ не имеет нулей
в $B(z_\ast,\delta/2)$ — противоречие. Значит, $\inf_{K_\delta}\lvert F\rvert>0$, и в полосе
$\lvert F\rvert\ge e^{-Lh_0}\inf_{K_\delta}\lvert F\rvert\cdot e^{L\lvert\operatorname{Im}\rho\rvert}$.

(iii) Существует $n_1$: в каждом прямоугольнике $[t,t+1]\times[-h_0,h_0]$ не больше $n_1$ нулей $F$ с
учётом кратности. Круг с центром $c_t=t+\tfrac12+i(h_0+1)$ радиуса $R_1=2h_0+2$ содержит прямоугольник;
неравенство Йенсена даёт число нулей в нём не больше
$\log\bigl(\max_{\lvert\rho-c_t\rvert=2R_1}\lvert F\rvert/\lvert F(c_t)\rvert\bigr)/\log2
\le\log\bigl(2C_Fe^{L(h_0+1+2R_1)}/(\lvert\theta\rvert e^{L(h_0+1)})\bigr)/\log2$ по (i), что не зависит от $t$.

**Шаг 12 (Руше по кластерам).** Положим $\delta_0=1/(8n_1)$, для $\delta\in(0,\delta_0]$ —
$O_\delta=\bigcup_{z\in Z_F}B(z,\delta)$; $\delta$-кластер — компонента связности $O_\delta$. Компонента
объединения кругов есть объединение кругов из компоненты графа пересечений (вершины — нули $F$,
рёбра — пересекающиеся круги). Объединение связного набора из $K$ кругов имеет вещественную проекцию
длины не больше $2\delta K$, и по (iii) $K\le n_1(2\delta K+1)$, откуда при $\delta\le1/(4n_1)$ $K\le2n_1$. Если бы
компонента графа содержала больше $2n_1$ вершин (в том числе бесконечно много), в ней нашёлся бы
связный подграф ровно из $2n_1+1$ вершин (дерево поиска в ширину из любой вершины, оборванное на
$2n_1+1$ вершинах), что противоречит оценке. Значит, кластер — объединение не более $2n_1$
кругов, его диаметр не больше $4\delta n_1\le\tfrac12$, граница — конечное число дуг окружностей, и на
границе $\operatorname{dist}(\rho,Z_F)\ge\delta$.

Пусть $\epsilon(r)$ из шага 9 и $r_\delta$ такое, что $\epsilon(r)<c_\delta$ при $r\ge r_\delta$.

(a) Если $\lvert\rho\rvert\ge r_\delta$ и $\operatorname{dist}(\rho,Z_F)\ge\delta$, то
$\lvert\Delta_Y(\rho)/c_\ast\rvert\ge\lvert F\rvert-\lvert\eta\rvert>0$. Все нули $\Delta_Y$ с $\lvert\rho\rvert\ge r_\delta$ лежат в
$O_\delta$, в частности в полосе $\lvert\operatorname{Im}\rho\rvert<h_0+\delta$; это первое утверждение (A) с
$h=h_0+\delta_0$, $R_0=r_{\delta_0}^2$.

(b) Если $\delta$-кластер $\mathcal G$ лежит в $\lbrace\lvert\rho\rvert>r_\delta\rbrace$, то на $\partial\mathcal G$
$\lvert\Delta_Y/c_\ast-F\rvert=\lvert\eta\rvert<c_\delta e^{L\lvert\operatorname{Im}\rho\rvert}\le\lvert F\rvert$, обе функции голоморфны на
$\overline{\mathcal G}$ ($0\notin\overline{\mathcal G}$), и по теореме Руше $\Delta_Y$ и $F$ имеют в $\mathcal G$ одинаковое
число нулей с учётом кратности.

**Шаг 13 (нумерация).** Функция $\rho^{\kappa_1+\kappa_2-1}F(\rho)$ целая и чётна: для $(0,0)$ $F$
нечётна и $F(0)=0$, для $(1,1)$ $F$ нечётна и умножается на $\rho$, для $(1,0)$ $F$ чётна. Поэтому
$G$ — целая функция $\lambda$. Функция $\Delta(\rho^2)$ тоже целая и чётна по $\rho$. Нули ненулевой
целой функции $\lambda$ кратности $q$ отвечают двум нулям $\pm\rho$ кратности $q$ её композиции с
$\rho^2$, нуль в $\lambda=0$ кратности $q$ — нулю кратности $2q$ в $\rho=0$.

Выберем $T\ge\max(r_{\delta_0},h_0)+1$ так, что прямая $\operatorname{Re}\rho=T$ не пересекает
$O_{\delta_0}$: отрезок $[t,t+1]$ пересекают вещественные проекции только кругов с центрами в
$[t-\delta_0,t+1+\delta_0]$, по (iii) их не больше $2n_1$ (два окна ширины $1$, так как $1+2\delta_0\le2$), и их
проекции — открытые интервалы суммарной длины не больше $4\delta_0n_1=\tfrac12<1$; они не покрывают отрезок. По симметрии $Z_F=-Z_F$ прямая $\operatorname{Re}\rho=-T$
тоже не пересекает $O_{\delta_0}$. Квадрат $Q=\lbrace\lvert\operatorname{Re}\rho\rvert<T,\ \lvert\operatorname{Im}\rho\rvert<T\rbrace$: на
$\partial Q$ $\lvert\rho\rvert\ge T\ge r_{\delta_0}$ и $\operatorname{dist}(\rho,Z_F)\ge\delta_0$ (горизонтальные стороны
лежат при $\lvert\operatorname{Im}\rho\rvert\ge h_0+1$). Тогда
$\lvert\Delta(\rho^2)-c_\ast\rho^{\kappa_1+\kappa_2-1}F\rvert=\lvert c_\ast\rvert\lvert\rho\rvert^{\kappa_1+\kappa_2-1}\lvert\eta\rvert<\lvert c_\ast\rho^{\kappa_1+\kappa_2-1}F\rvert$
на $\partial Q$, и по теореме Руше (для целых функций) числа нулей в $Q$ совпадают. Ввиду чётности
$\Delta$ и $G$ имеют поровну нулей в образе $\widehat Q=\lbrace\rho^2:\rho\in Q\rbrace$. Нули $\Delta(\rho^2)$ вне $Q$
имеют $\lvert\rho\rvert\ge T$, лежат в $O_{\delta_0}$ по 12(a), в полосе высоты $h_0+\delta_0<T$, значит
$\lvert\operatorname{Re}\rho\rvert>T$ и они лежат в $\delta_0$-кластерах из $\lbrace\operatorname{Re}\rho>T\rbrace$ или из
$\lbrace\operatorname{Re}\rho<-T\rbrace$; квадраты точек из $\lbrace\operatorname{Re}\rho>T\rbrace$ не лежат в $\widehat Q$.
Итак, нули $\Delta$ — это нули в $\widehat Q$ и квадраты нулей $\Delta_Y$ из «правых» кластеров
$\mathcal G\subset\lbrace\operatorname{Re}\rho>T\rbrace$, и так же для $G$ с нулями $F$ (кратности сохраняются, так
как $\rho\mapsto\rho^2$ локально биголоморфно при $\rho\ne0$). По 12(b) в каждом правом кластере
нулей поровну.

Пусть $\delta_q=\delta_02^{-q}$. Для правого $\delta_0$-кластера $\mathcal G$ положим $q(\mathcal G)$ —
наибольшее целое $q\in[0,\inf_{\mathcal G}\operatorname{Re}\rho]$ с $\mathcal G\subset\lbrace\operatorname{Re}\rho>r_{\delta_q}\rbrace$ ($q=0$
допустимо, так как $T>r_{\delta_0}$). При фиксированном $q$ все кластеры с
$\inf_{\mathcal G}\operatorname{Re}\rho>\max(q,r_{\delta_q})$ имеют $q(\mathcal G)\ge q$, то есть $q(\mathcal G)\to\infty$. Каждый $\delta_q$-кластер с центром в $\mathcal G$ содержится в $\mathcal G$; по
12(a) все нули $\Delta_Y$ из $\mathcal G$ лежат в $O_{\delta_q}$, по 12(b) в каждом $\delta_q$-кластере нулей
$\Delta_Y$ и $F$ поровну. Сопоставим нули внутри $\delta_{q(\mathcal G)}$-кластеров (расстояние не больше
$4\delta_{q(\mathcal G)}n_1$), нули в $\widehat Q$ — произвольно, и занумеруем пары в порядке возрастания
$\operatorname{Re}\mathcal G$. Получаем $\lvert\sqrt{\lambda_k}-\sqrt{\lambda_k^0}\rvert\le4n_1\delta_{q(\mathcal G_k)}\to0$, где
$\sqrt{\lambda_k}$ — точка правого кластера с $\operatorname{Re}>0$. Это второе утверждение (A).

**Шаг 14 (усиленная регулярность).** Пусть нули $F$ с $\operatorname{Re}\rho\ge0$ отделены числом
$\delta_s>0$ и просты при $\lvert\rho\rvert\ge R_s$. Возьмём $\delta<\min(\delta_0,\delta_s/2)$. Правые
$\delta$-кластеры с $\operatorname{Re}\rho>\max(T,R_s,r_\delta)$ — одиночные круги с одним простым нулём $F$; по
12(b) в каждом ровно один нуль $\Delta_Y$ кратности $1$, по (4) и локальной биголоморфности
$\rho\mapsto\rho^2$ соответствующий нуль $\Delta$ простой. Если бы $\operatorname{rank}(V_0+V_1\Phi(1,\lambda))\le2$, все
миноры порядка $3$ обращались бы в нуль, и производная определителя, равная сумме произведений
производных элементов на алгебраические дополнения, тоже была бы нулём. Значит, ранг равен $3$,
ядро одномерно, и по шагу 3 собственное подпространство одномерно. Это третье утверждение (A).

**Шаг 15 (C, Дирихле).** $U_1=y(-1)$, $U_2=y(1)$: вид $(0,0)$, $\alpha_{10}=\beta_{20}=1$, остальные
коэффициенты нули, $J_0=1$; по шагу 10 задача регулярна. Нули $\cos\rho\ell_+$ — $\pi(n-\tfrac12)/\ell_+$, нули
$\sin\rho\ell_-$ — $\pi n/\ell_-$, все простые; внутри серии шаг $\pi/\ell_\pm$. Пусть $\varepsilon=1$. Нули разных
серий совпадают, когда $(2n-1)/(2\ell_+)=m/\ell_-$, то есть $\ell_+/\ell_-=(2n-1)/(2m)$.

- $\ell_+/\ell_-=r/s$ несократима, $s$ нечётно: $(2n-1)s=2mr$ невозможно (слева нечётное число), и
  $\bigl\lvert\pi(n-\tfrac12)/\ell_+-\pi m/\ell_-\bigr\rvert=\pi\lvert(2n-1)s-2mr\rvert/(2s\ell_+)\ge\pi/(2s\ell_+)$, так как
  $\ell_-=s\ell_+/r$ и в числителе ненулевое целое. Нули простые и отделены числом
  $\min(\pi/(2s\ell_+),\pi/\ell_-)$: задача усиленно регулярна.
- $s$ чётно, $s=2s'$, тогда $r$ нечётно: при $m=s'(2j-1)$, $2n-1=r(2j-1)$, $j\ge1$, нули совпадают —
  бесконечно много двукратных нулей.
- $\ell_+/\ell_-=\alpha$ иррационально: $\bigl\lvert\pi(n-\tfrac12)/\ell_+-\pi m/\ell_-\bigr\rvert=(\pi/\ell_+)\lvert m\alpha-(n-\tfrac12)\rvert$, а
  дробные части $\lbrace m\alpha\rbrace$ бесконечно часто попадают в любой интервал около $\tfrac12$ (Кронекер),
  так что зазор между сериями сколь угодно мал при сколь угодно больших $m$.

При $\varepsilon=-1$ серии $\pi n/\ell_+$ и $\pi(m-\tfrac12)/\ell_-$ совпадают при $\ell_+/\ell_-=2n/(2m-1)$, и то же
рассуждение с ролями $r$ и $s$, поменянными местами, даёт критерий с нечётным $r$.

**Шаг 16 (D).** По шагу 8 $F=\tfrac{\varepsilon(\mathcal B-\mathcal A)}2H$, $H(\rho)=\cos\rho L+\gamma\cos\rho d$. Нули
$\cos\rho L$ — $z_n=\pi(n-\tfrac12)/L$, и $\cos(z_nL+u)=(-1)^n\sin u$. Для $\lvert u\rvert=w$, $u=x+iy$:
$\lvert\sin u\rvert^2=\sin^2x+\sinh^2y\ge\sin^2x+y^2$, а $s\mapsto\sin^2\sqrt s-s$ не возрастает на $[0,w^2]$
(производная $\sin(2\sqrt s)/(2\sqrt s)-1\le0$), откуда $\sin^2x+y^2\ge\sin^2w$ и $\lvert\sin u\rvert\ge\sin w$
при $w\le\pi/2$. На окружности $\lvert\rho-z_n\rvert=r$ имеем $\lvert\operatorname{Im}\rho\rvert\le r$ и

$$
\lvert\cos\rho L\rvert\ge\sin(Lr)>\lvert\gamma\rvert\cosh(\lvert d\rvert r)\ge\lvert\gamma\cos\rho d\rvert ,
$$

и по Руше в круге ровно один нуль $H$, простой. Из условия $\lvert\gamma\rvert<\sin(Lr)\le1$. На прямых
$\operatorname{Re}\rho=\pi n/L$: $\lvert\cos\rho L\rvert=\cosh(L\operatorname{Im}\rho)>\lvert\gamma\rvert\cosh(d\operatorname{Im}\rho)\ge\lvert\gamma\cos\rho d\rvert$, так
как $\lvert d\rvert<L$ и $\lvert\gamma\rvert<1$; на прямых $\lvert\operatorname{Im}\rho\rvert=Y$ при больших $Y$
$\lvert\cos\rho L\rvert\ge\sinh(LY)>\lvert\gamma\rvert\cosh(dY)$. По Руше в каждом прямоугольнике между
$\operatorname{Re}\rho=\pi(n-1)/L$ и $\pi n/L$ у $H$ ровно один нуль (как у $\cos\rho L$), а при $\lvert\operatorname{Im}\rho\rvert\ge Y$
нулей нет. Значит, все нули $H$ — по одному в кругах вокруг $z_n$. Различные нули удалены друг от
друга не меньше чем на $\pi/L-2r>0$: задача усиленно регулярна. Если $\gamma\in\mathbb R$, то $H$ вещественна на
вещественной оси, нуль в круге с вещественным центром вместе с сопряжённым лежит в том же круге и
единственен, поэтому вещественен; при невещественном $\gamma$ (коэффициенты (2) комплексные) это
неверно, контрпример — в рецензии. Достаточное условие: если $\lvert\gamma\rvert\cosh(\pi\lvert d\rvert/(2L))<1$, то
разность $\sin(Lr)-\lvert\gamma\rvert\cosh(\lvert d\rvert r)$ стремится к положительному пределу при
$r\to\pi/(2L)-0$ и положительна при $r$, близких к $\pi/(2L)$. Обратное не утверждается: условие с $r$
слабее.

**Шаг 17 (E).** $\alpha_{11}=\beta_{11}=1$, $\beta_{20}=1$, $\alpha_{20}=-1$, остальные нули; вид $(1,0)$ нормирован
($U_2$ порядка $0$ ненулевая, у $U_1$ есть производная). Тогда
$\mathcal A=\omega_+(1-\varkappa)(1+\varkappa)=\omega_+(1-\varkappa^2)$, $\mathcal B=\omega_-(1-\varkappa^2)$,
$\mathcal A-\mathcal B=(\omega_+-\omega_-)(1-\varkappa^2)$. $\omega_+<\omega_-$, так как $p(1)\ge m^2>0$, а
$\varkappa^2=a(-1)/a(1)=1$ ровно при $a(1)=a(-1)$. По шагу 10 регулярность равносильна $a(1)\ne a(-1)$.
Если $a$ чётна, то решение $y$ задачи Коши $-(1+a)y''=\lambda y$, $y(0)=1$, $y'(0)=0$ чётно (единственность
и чётность коэффициента), удовлетворяет (1) (так как $y''(-x)=y''(x)$) и условиям: $y'(1)+y'(-1)=0$,
$y(1)-y(-1)=0$. При $a=0$ то же с $y=\cos\rho x$.

**Проверка.** Скрипт `output/c24/check_constant.py` (стрельба DOP853 для $a=\varepsilon(\tfrac12+\tfrac x4)$,
$\varepsilon=\pm1$, все три вида, в $(1,0)$ и $(1,1)$ с ненулевыми членами $U^1$) сравнивает
$\rho^{1-\kappa_1-\kappa_2}\Delta(\rho^2)$ с $c_\ast F(\rho)$ при $\rho=R+1{,}5i$: отношение при $R=20,40,80$
отличается от $1$ не больше чем на $0{,}066$, $0{,}028$, $0{,}019$ во всех шести случаях. Это проверяет
таблицу $F$, $\gamma_U$ и постоянную $c_\ast$. Сравнение собственных значений с нулями $F$ для
$a=\tfrac12+\tfrac x4$ — опыт E10 (`experiments/E10/README.md`); там же наблюдения об остатке $c/k$ в случаях
(C), (D) и о росте $\operatorname{Im}\rho_k$ при $\mathcal A=\mathcal B$, которые эта запись не доказывает.

## Lean

Формализации нет. В библиотеке есть складывание для области Дирихле
(`memDirichletH2_iff_fold`, `MemDirichletH2.fold`, `MemFoldedDirichletH2.unfold`) и точечное
обращение матрицы $M$ (`reduction_under_product_bound`, `complex_reduction_under_product_bound`);
складывания с общими условиями (2) нет. В закреплённом Mathlib есть формула и неравенство Йенсена
(`AnalyticOnNhd.circleAverage_log_norm`, `AnalyticOnNhd.sum_divisor_le`) для шага 11(iii); теоремы Руше
и теоремы Гурвица поиском по `Mathlib/Analysis/Complex` не найдено. Не хватает: матрицы Коши
линейной системы, голоморфной по параметру; характеристического определителя; лемм о
экспоненциальных многочленах (шаг 11); теоремы Руше для области, ограниченной дугами. Теорема 1
S50 вошла бы гипотезой: «для диагональной $\widehat B$ с (4) и $\widetilde A\in L_1$ с нулевой диагональю
в каждой полуплоскости $\pm\operatorname{Re}\zeta\ge0$ существует фундаментальная матрица $(I+R)E$ с
$\sup_x\lvert R\rvert\to0$».

## Границы

- Остаток только $o(1)$. Оценка $\rho_k=\rho_k^0+O(1/k)$ при усиленной регулярности и асимптотика
  собственных функций $w_k=\sum C^{(k)}_{\pm,s}D_\pm e_\pm e^{is\rho_k^0t_\pm}+O(1/k)$ (утверждение (B) идеи)
  требуют леммы: при $a\in W^2_1$ остаток $R$ теоремы 1 S50 есть $O(1/\lvert\rho\rvert)$ равномерно по $x$.
  S50 её не даёт (скорость в теореме 1 не утверждается), теорема 6 S50 при $a\in W^1_p$ даёт лишь
  суммируемость $\sum\lvert\lambda_k-\lambda_k^0\rvert^{p'}$ и только для постоянных краевых матриц, то есть
  для $U^0$. Для $U\ne U^0$ асимптотику собственных функций надо выводить из ядра
  $\mathfrak U_a(\rho_k)$, а не из теорем 2, 6 S50. Открытый узел.
- Вторая часть (A) идеи (группы не более чем из $\nu$ нулей диаметра $o(1)$, остаток $O(k^{-1/\nu})$ и
  $O(1/k)$ для симметрических функций группы) опирается на ту же лемму и здесь не доказана; так же
  последняя фраза (D) идеи об остатке $O(1/k)$.
- (C): при иррациональном $\ell_+/\ell_-$ оценка $O(k^{-1/2})$ не следует из (A): группы диаметра $o(1)$ с
  фиксированным зазором не выделяются (критика I43). Нужны нижняя оценка
  $\lvert F(\rho)\rvert\ge c\prod_j\lvert\rho-\rho_j^0\rvert$ по двум ближайшим нулям в полосе и лемма об
  $O(1/\lvert\rho\rvert)$. Опыт E10 при $a=\tfrac12+\tfrac x4$ показывает остаток не больше $0{,}43/k$ и у
  сблизившихся пар, $k\le100$ (`experiments/E10/README.md`); как поведение при $k\to\infty$ это не доказано.
- Кратности. Нумерация в (A) идёт по кратностям нулей $\Delta$; их равенство алгебраическим
  кратностям собственных значений оператора в $L_2(-1,1)$ с областью
  $\lbrace y\in H^2:U_1y=U_2y=0\rbrace$ не доказано, и сам оператор в записи не построен. Простота в (A)
  при усиленной регулярности — простота нуля $\Delta$ и одномерность собственного подпространства;
  отсутствие присоединённых функций отсюда не выведено.
- Базисность не утверждается. Теорема 3 S50 говорит о базисе со скобками в $L_2(\mathbb C^4;[0,1])$
  для системы в переменных $Y$ с условиями $U^0$; перенос на корневые функции задачи (1), (2) в
  $L_2(-1,1)$ и на условия $U=U^0+\rho^{-1}U^1$ не проверен.
- Нерегулярный случай $\mathcal A=\mathcal B$ (вид $(1,0)$) не рассматривается; в (E) при $a(1)=a(-1)$
  $F\equiv0$, а при чётном $a$ спектр — вся плоскость. Рост $\operatorname{Im}\rho_k$ в опыте E10 (случай 5) —
  наблюдение без доказательства.
- Класс $a$: только знакопостоянные $a\in W^1_1$ с $p\le\kappa<1$. При смене знака $a$, при $p<0$ (C18,
  C23) или $p$, доходящем до $1$, гиперболичность (4) S50, а с ней и строгая гиперболичность (5), нарушается (корни $\pm\tau_\pm$
  перестают быть вещественными, различными или конечными), и шаги 5–6 не проходят. Задача Дирихле
  с $p$ любого знака — идеи I39, I40 (линия D).
- Младших членов в уравнении нет (решение пользователя); члены нулевого порядка в условиях
  первого порядка учтены (шаг 4). Условия — только двухточечные вида (2), нормированные и линейно
  независимые.
- Внешний вход — одна теорема краткого сообщения S50 без доказательства в самом сообщении.
- Идея-источник — I43 (с разделом «Критика» 2026-10-25); пометки сверки карточки S50 учтены в шагах
  1, 5.

**Рецензия (2026-10-26).**

Гипотезы: (H) — $a$ вещественна, $a\in W^1_1(-1,1)$, $\lvert a\rvert\ge m>0$, $p\le\kappa<1$; формы
$U_1,U_2$ линейно независимы и нормированы. Каждая гипотеза использована: вещественность и
$\lvert a\rvert\ge m$ — в шаге 1 (знакопостоянство, $p\ge m^2$, отделённость $k$), $W^1_1$ — в шагах 1, 5
($W$ абсолютно непрерывна, $A=-W^{-1}W'\in L_1$), $p\le\kappa$ — в шагах 2, 5 ($\det M>0$, вещественность
и запас $\tau_\pm$), нормированность — в шаге 8 ($\gamma_U\ne0$). Определение нормированных условий
сверено по текстовому слою S48, с. 645 (стр. файла 3): порядок формы, суммарный порядок, «нельзя
понизить линейными комбинациями», главная часть (1.1) — совпадает с записью. Карточка S50 сверена;
теорема 1 применяется в пределах гипотез: $\widehat B$ диагональна, (4) с $s=2$ после перестановки
столбцов, $\widetilde A\in L_1$ с нулевой диагональю, так что множитель $M$ теоремы равен $I$ при обоих
прочтениях. Зависимость условий от $\rho$ ($U^0+\rho^{-1}U^1$) теоремы 1 не касается: она входит
только в шаг 7, где учтена как $O(\rho^{-1})e^{is\rho\ell_\pm}$.

Замечания.

1. Утверждение 5 и шаг 16, «он вещественный». Довод опирается на вещественность $H$ на вещественной
   оси, а она есть только при $\gamma\in\mathbb R$; коэффициенты (2) комплексные, и $\gamma$ — дробно-линейная
   непостоянная функция, например, от $\alpha_{11}$ при $\beta_{11}=\beta_{20}=1$, $\alpha_{20}=0$, так что
   принимает невещественные значения. Контрпример: $L=1$, $d=-\tfrac12$, $\gamma=0{,}3i$, $r=1$ — условие
   $\lvert\gamma\rvert\cosh(\lvert d\rvert r)=0{,}338<\sin1=0{,}841$ выполнено, а нули $H$ у $z_1,z_2,z_3$ равны
   $1{,}5928+0{,}2095i$, $4{,}6904+0{,}2095i$, $7{,}8760-0{,}2095i$. Вес: ошибка. Требуется: оставить
   вещественность нулей только при $\gamma\in\mathbb R$; остальная часть (D) — один простой нуль в каждом
   круге, отделённость $\pi/L-2r$, усиленная регулярность — от этого не зависит и доказана.
2. Утверждение 5 и конец шага 16, «это равносильно $\lvert\gamma\rvert\cosh(\pi d/(2L))<1$». Верно только
   следствие «$\lvert\gamma\rvert\cosh(\pi\lvert d\rvert/(2L))<1\Rightarrow\exists r$». Обратный довод
   («$\sin(Lr)\le1$ и $\cosh$ возрастает») идёт в неверную сторону: из
   $\lvert\gamma\rvert\cosh(\lvert d\rvert r)<1$ при $r<\pi/(2L)$ не следует неравенство в точке $\pi/(2L)$,
   где $\cosh$ больше. Контрпример: $\lvert d\rvert/L=0{,}99$, $\lvert\gamma\rvert=1/\cosh(0{,}99\pi/2)$; тогда
   $\lvert\gamma\rvert\cosh(\pi\lvert d\rvert/(2L))=1$, а $\max_{0<x<\pi/2}(\sin x-\lvert\gamma\rvert\cosh(0{,}99x))=0{,}224>0$
   при $x=Lr\approx1{,}05$. Вес: ошибка (ложное утверждение о равносильности). Требуется: заменить
   «равносильно» на «следует из»; условие с $r$ слабее, и вывод (D) при нём доказан.
3. Шаг 13, выбор $T$. Проекции на отрезок $[t,t+1]$ дают не только круги с центрами в $[t,t+1]$
   (их не больше $n_1$), но и круги с центрами в $[t-\delta_0,t+1+\delta_0]$ — их не больше $2n_1$, и
   покрытая длина не больше $4\delta_0n_1=1$, а не $\tfrac12$. Вывод сохраняется: конечный набор открытых
   интервалов суммарной длины не больше $1$ не покрывает замкнутый отрезок длины $1$; проще взять
   $\delta_0=1/(8n_1)$. Вес: неточность.
4. Шаг 12, $K\le2n_1$. Рассуждение предполагает компоненту из конечного числа кругов. Для бесконечной
   компоненты надо взять связный подграф из $2n_1+1$ кругов (в бесконечном связном графе он есть) и
   получить то же противоречие. Вес: неточность.
5. Шаг 10, обозначения. $J_0=-L$, $J_1=L$ — показатели из (7) S50, а в постановке $J_0$, $J_1$ —
   миноры краевых форм; в одном тексте символ обозначает два объекта. Вес: неточность.
6. «Границы», абзац о классе $a$: «строгая гиперболичность (4)» — в S50 (4) есть гиперболичность, строгая
   — (5). Вес: неточность.

Остальные переходы проверены и обоснованы: складывание и обратное склеивание (шаг 2), формула (4),
строки $\widetilde U_0$, $\widetilde U_1$ (шаг 4), разложение Лапласа и оценка $\lvert P\rvert\le L$ (шаг 7),
переход от $\det\mathfrak U_a$ к $\Delta_Y$ через $C(\rho)=Y_a(0,\rho)$ (шаг 9), соответствие $c_0,c_1$ S50
коэффициентам $\theta_\mp$ (шаг 10), лемма 11 (i)–(iii) с кругом Йенсена (угол прямоугольника на
расстоянии $\sqrt{1/4+(2h_0+1)^2}<2h_0+2$), Руше по кластерам и счёт кратностей при $\rho\mapsto\rho^2$
(шаги 12–13), ранг $3$ через формулу Якоби (шаг 14), критерий (C) с обоими знаками $\varepsilon$ (шаг 15), (E)
вместе с чётным $a$ ($1+a>0$, так как $a^2\le\kappa<1$) и $a=0$ (шаг 17). Абзац «Границы» сверх
доказанного не заявляет, кроме замечания 6.

Пересчёт (`output/c24_referee/`). `sym_check.py` (SymPy): $\det W=16k^2\tau_+\tau_-$ со знаком; строки
$W^{-1}$ дают $W^{-1}W=I$; диагональ $-W^{-1}W'$ равна $-k'/(2k)-\tau_\pm'/(2\tau_\pm)$; $\det\mathfrak U^0$,
вычисленный прямо по столбцам $g_{\pm,s}$, совпадает с $D_+(1)D_-(1)\cdot4i\varepsilon\tau^0_\varepsilon\gamma_UF$ для
трёх видов при $\varepsilon=\pm1$ (таблица $F$, включая $(1,0)$ при $\varepsilon=-1$, и $\gamma_U$ верны); $c_\ast$ шага 9
после подстановки $D_\pm(1)$ равна формуле утверждения 2. `num_check.py`: стрельба DOP853 при
$a=\varepsilon(0{,}4+0{,}2x+0{,}1x^2)$ (не та функция, что в `output/c24/check_constant.py`) со случайными
комплексными коэффициентами, включая члены $U^1$: $\lvert\rho^{1-\kappa_1-\kappa_2}\Delta(\rho^2)/(c_\ast F(\rho))-1\rvert$ при
$\rho=R+1{,}5i$, $R=20,40,80$, убывает примерно как $1/R$ во всех шести случаях (наибольшее при $R=80$ —
$0{,}061$ для $(1,1)$, $\varepsilon=1$). `d_check.py`: контрпримеры замечаний 1, 2. Тригонометрические
разложения шага 8, $\theta_\pm$, $\gamma$ и неравенство $\lvert\sin u\rvert\ge\sin\lvert u\rvert$ шага 16 пересчитаны
вручную.

Вердикт: ошибка (замечания 1, 2 в утверждении 5; утверждения 1–4, 6 и в (D) существование и простота
нулей с усиленной регулярностью при условии с $r$ доказаны).

## Правки после рецензии (2026-10-26)

- Утверждение 5 и шаг 16: вещественность нулей $F$ оставлена только при $\gamma\in\mathbb R$ (замечание 1).
- Утверждение 5 и шаг 16: «равносильно» заменено на «следует из», обратный довод удалён (замечание 2).
- Шаг 13: подсчёт кругов, проекции которых пересекают $[t,t+1]$, по центрам в $[t-\delta_0,t+1+\delta_0]$;
  $\delta_0=1/(8n_1)$ в шаге 12, покрытая длина не больше $\tfrac12$ (замечание 3).
- Шаг 12: для компоненты с бесконечным или большим числом кругов взят связный подграф из $2n_1+1$
  вершин (замечание 4); диаметр кластера не больше $\tfrac12$.
- Шаг 10: показатели (7) S50 обозначены $J^{S}_0$, $J^{S}_1$ (замечание 5).
- «Границы»: (4) — гиперболичность, (5) — строгая гиперболичность (замечание 6).
- В «Отличии от идеи I43» формулировка о (D) согласована с правкой 2.

**Повторная рецензия (2026-10-26).**

Проверены правки по замечаниям 1–6 рецензии того же дня.

1. Замечание 1 устранено. В утверждении 5 и шаге 16 вещественность нулей оставлена только при
   $\gamma\in\mathbb R$; при этом $H(\bar\rho)=\overline{H(\rho)}$, и довод через единственность нуля в круге с
   вещественным центром верен. Остальная часть (D) вещественности не использует.
2. Замечание 2 устранено. Остаётся только следствие из $\lvert\gamma\rvert\cosh(\pi\lvert d\rvert/(2L))<1$ (предельный
   переход $r\to\pi/(2L)-0$ верен), обратное прямо названо неверным; абзац «Отличие от идеи I43»
   согласован.
3. Замечания 3, 4: шаги 12, 13 при $\delta_0=1/(8n_1)$ пересчитаны. В шаге 12 оценка
   $K\le n_1(2\delta K+1)$ для любого конечного связного набора кругов при $\delta\le1/(4n_1)$ даёт $K\le2n_1$;
   компонента с большим (в том числе бесконечным) числом вершин содержит связный набор ровно из
   $2n_1+1$ вершин (первые $2n_1+1$ вершин обхода в ширину связны и при бесконечной степени вершин),
   противоречие. Диаметр кластера не больше $2\delta K\le4\delta n_1\le\tfrac12$. В шаге 13 круги, чьи проекции
   пересекают $[t,t+1]$, имеют центры в отрезке длины $1+2\delta_0\le2$, их не больше $2n_1$, покрытая длина
   не больше $4\delta_0n_1=\tfrac12<1$, так что прямая $\operatorname{Re}\rho=T$ без пересечения с $O_{\delta_0}$ найдётся.
   Уменьшение $\delta_0$ согласовано с остальными местами: $h=h_0+\delta_0$, $R_0=r_{\delta_0}^2$, условие
   $T\ge\max(r_{\delta_0},h_0)+1>h_0+\delta_0$, $\delta_q=\delta_02^{-q}\le1/(4n_1)$ в уточнении шага 13 (оценка
   $4n_1\delta_q$ сохраняется) и $\delta<\min(\delta_0,\delta_s/2)$ в шаге 14.
4. Замечание 5 устранено: показатели (7) S50 обозначены $J^S_0$, $J^S_1$.
5. Замечание 6 устранено: в «Границах» (4) названа гиперболичностью, (5) — строгой.

Новых ошибок правки не внесли. Новых выкладок нет; пересчёт первой рецензии
(`output/c24_referee/`) к изменённым местам применим без изменений.

Вердикт: принято.
