---
id: C26
title: Случай n=m с общими двухточечными условиями при a∈W²₁ — остаток O(1/ρ) фундаментальной системы, Δ−Δ⁰=O(ρ^{N−1}e^{L|Im ρ|}), ρ_k=ρ_k⁰+O(1/k) и асимптотика собственных функций при усиленной регулярности
status: own-result
depends_on: [C24, S54]
checked_by: [referee 2026-11-05]
---

Линия G (общие двухточечные условия, раздел «Две линии исследования» в `claims/question.md`):
оператор $-y''(x)-a(x)y''(-x)$ без младших членов. Запись уточняет C24: остаток $o(1)$ теоремы 1
S50 заменяется остатком $O(1/\rho)$ по теореме 1.2 работы S54, что закрывает пробел раздела
«Критика» идеи I43 об $O(1/\lvert\lambda\rvert)$ при $a\in W^2_1$. Определения регулярности и
усиленной регулярности — из C24 и здесь не меняются; остаток $O(1/k)$ — отдельное следствие при
более гладком $a$, а не часть определения.

## Условия

- (H2) $a$ вещественна, $a\in W^2_1(-1,1)$, $0<p(x)=a(x)a(-x)<1$ при всех $x\in[-1,1]$.
- Формы $U_1,U_2$ из (2) C24 линейно независимы и нормированы (C24, «Условия на краевые формы»).

Обозначения $\varepsilon$, $\sigma_\pm$, $\tau_\pm$, $t_\pm$, $\ell_\pm$, $L$, $d$, $\varkappa$, $k(x)$, $F$, $\theta$,
$\Phi$, $\Delta$, $\Delta_Y$, $S_\rho$, $\Lambda_\rho$, $W$, $g_{\pm,s}$, $f_\pm$, $\mathbf D$, $D_\pm$, $c_\ast$, $c_U$,
$\mathfrak U_a$, $\mathfrak U^0$, $N=1+\kappa_1+\kappa_2$ — как в C24. Порядок столбцов везде
$(+,+),(+,-),(-,+),(-,-)$.

## Утверждение

Пусть выполнены (H2) и условия на формы. Тогда выполнена гипотеза (H) C24, и:

1. (Фундаментальная система.) Для любого $h\ge0$ существуют $r_1>0$ и фундаментальная матрица
   $Y_a(x,\rho)$ системы $Y'=\rho KY$ в полуплоскости $\Pi^h_+=\lbrace\operatorname{Im}\rho\ge-h\rbrace$ (и своя в
   $\Pi^h_-=\lbrace\operatorname{Im}\rho\le h\rbrace$) вида
   $$
   Y_a(x,\rho)=W(x)\mathbf D(x)\bigl(I+\mathcal E(x,\rho)\bigr)E(x,\rho),\qquad
   E=\operatorname{diag}\bigl(e^{is\rho t_\pm(x)}\bigr),\qquad
   \sup_{x\in[0,1]}\lvert\mathcal E(x,\rho)\rvert\le\frac{C}{\lvert\rho\rvert}\quad(\lvert\rho\rvert\ge r_1).
   $$
2. (Определитель.) Функция $\eta=\Delta_Y/c_\ast-F$ из утверждения 2 C24 удовлетворяет
   $$
   \lvert\eta(\rho)\rvert\le\frac{C}{\lvert\rho\rvert}e^{L\lvert\operatorname{Im}\rho\rvert},\qquad\lvert\rho\rvert\ge r_1,
   $$
   то есть $\rho^{1-\kappa_1-\kappa_2}\Delta(\rho^2)-c_\ast F(\rho)=O(\lvert\rho\rvert^{-1}e^{L\lvert\operatorname{Im}\rho\rvert})$. В
   нормировке идеи I43 (определитель условий в переменных $(w,w')$ на столбцах $X_a=S_\rho^{-1}Y_a$,
   $\Delta_X=\det(V_0X_a(0)+V_1X_a(1))$) это
   $\Delta_X(\rho)-\Delta^0(\rho)=O(\lvert\rho\rvert^{N-1}e^{L\lvert\operatorname{Im}\rho\rvert})$, где
   $\Delta^0=c_U\rho^NF$ — определитель упрощённой задачи S50 для условий $U^0$ (утверждение 2 C24).
3. (Собственные значения.) Если задача усиленно регулярна (определение C24), то в нумерации
   утверждения 3 C24
   $$
   \rho_k=\rho_k^0+O(1/k),\qquad\lambda_k-\lambda_k^0=O(1).
   $$
4. (Собственные функции.) При усиленной регулярности для каждого большого $k$ существует вектор
   $C^{(k)}\in\ker\mathfrak U^0(\rho_k^0)$, $\lvert C^{(k)}\rvert=1$, такой что собственная функция $y_k$
   задачи (1), (2) C24 при $\lambda_k$ (единственная с точностью до множителя) после нормировки
   множителем удовлетворяет равномерно по $x\in[0,1]$
   $$
   \begin{pmatrix}y_k(x)\\ y_k(-x)\end{pmatrix}=\sum_{\pm,s}C^{(k)}_{\pm,s}D_\pm(x)e_\pm(x)e^{is\rho_k^0t_\pm(x)}+O(1/k),
   $$
   $$
   \frac1{\rho_k}\begin{pmatrix}y_k'(x)\\ -y_k'(-x)\end{pmatrix}=\sum_{\pm,s}C^{(k)}_{\pm,s}\,is\tau_\pm(x)D_\pm(x)e_\pm(x)e^{is\rho_k^0t_\pm(x)}+O(1/k),
   $$
   и главная часть не мала: её значение в $x=0$ (вектор $W(0)C^{(k)}$) по норме не меньше
   $\lVert W(0)^{-1}\rVert^{-1}>0$.

**Отличие от идеи I43.** Утверждение (B) идеи доказано с гипотезой $a\in W^2_1$, внесённой по
критике, в классе (H2), то есть при $p$ без нулей. Вектор $C^{(k)}$ берётся из ядра
$\mathfrak U^0(\rho_k^0)$ — матрицы главных частей $U^0$ на главных членах столбцов; члены $U^1$ входят
только в остаток. Последняя фраза (D) идеи (остаток $O(1/k)$ при условии (D)) следует из пункта 3,
так как условие (D) даёт усиленную регулярность (утверждение 5 C24). Вторая часть (A) идеи (группы
из $\nu$ нулей, $O(k^{-1/\nu})$) и оценка $O(k^{-1/2})$ в (C) не доказываются (раздел «Границы»).

## Внешний вход

- S54 (А. П. Косарев, А. А. Шкаликов, Матем. заметки 116:6 (2024), 923–940), теорема 1.1, с. 926–927,
  с формулами (1.13), (1.15), (1.16), (1.17) и замечанием 1.1, с. 927; соглашение (1.3), с. 924. Карточка S54,
  сверена (source-verifier 2026-11-05). Используется при $m=1$ в виде следствия карточки:
  $Y=M(I+O(\lvert\lambda\rvert^{-1}))E$ равномерно по $x$ в секторе; само следствие выписано в шаге 3 из
  (1.15)–(1.17). Проверка всех гипотез для сложенной системы — шаг 2.
- C24 (своя запись, рецензия 2026-10-26, вердикт «принято» после правок): утверждения 1–3, шаги 4, 5, 7–14.
- Стандартные факты: $W^1_1(0,1)\subset AC[0,1]$ и $W^1_1(0,1)$ — алгебра; цепное правило для
  $\varphi\circ u$ с $u\in W^2_1$ и $\varphi\in C^2$ на отрезке значений $u$; принцип минимума модуля для
  голоморфной функции без нулей; формула Якоби для производной определителя;
  $A\operatorname{adj}A=\det A\cdot I$.
- Решения пользователя: младших членов в уравнении нет (постановка, линия G). Других решений о
  внешних входах для этой записи не было.

## Доказательство

**Шаг 1 ((H2) влечёт (H) C24).** $a\in W^2_1(-1,1)\subset W^1_1(-1,1)\subset C[-1,1]$, $p$ непрерывна на
компакте, поэтому $0<p_{\min}\le p\le\kappa:=p_{\max}<1$. Если $a(x_0)=0$, то $p(x_0)=0$; значит, $a$ не
обращается в нуль и $\lvert a\rvert\ge m>0$. Гипотеза (H) C24 выполнена, и все утверждения C24
применимы. На $[0,1]$ функции $a\vert_{[0,1]}$, $a(-\cdot)\vert_{[0,1]}$ лежат в $W^2_1(0,1)$, отсюда
$p\in W^2_1(0,1)$ (алгебра: $(uv)''=u''v+2u'v'+uv''$, где $u',v'\in W^1_1\subset C$). Положим
$\varphi_\pm(t)=(1\pm\sqrt t)^{-1/2}$, $\psi(t)=\sqrt t$, $\chi(t)=1/t$; они бесконечно гладки на
$[p_{\min},\kappa]$, $[\,m/\lVert a\rVert_\infty,\lVert a\rVert_\infty/m\,]$, $[m,\lVert a\rVert_\infty]$
соответственно. Для $u\in W^2_1$ и $\varphi\in C^2$ на отрезке значений $u$:
$(\varphi\circ u)'=\varphi'(u)u'$, где $\varphi'(u)\in W^1_1$ (её производная $\varphi''(u)u'\in L_1$) и
$u'\in W^1_1$, так что $\varphi\circ u\in W^2_1$. Значит, $\tau_\pm=\varphi_\pm\circ p\in W^2_1(0,1)$,
$1/\tau_\pm\in W^2_1$, $\lvert a\rvert^{-1}=\chi\circ\lvert a\rvert\in W^2_1$,
$k=\varepsilon\,\psi\bigl(a(-x)/a(x)\bigr)\in W^2_1$, $1/k\in W^2_1$.

**Шаг 2 (гипотезы S54 для сложенной системы).** По шагам 4, 5 C24 замена $Y=WZ$ переводит
$Y'=\rho KY$ в
$$
Z'-B_0(x)Z=\rho\,\widehat A(x)Z,\qquad B_0=-W^{-1}W',\qquad
\widehat A=\operatorname{diag}(i\tau_+,-i\tau_+,i\tau_-,-i\tau_-).
$$
Это (1.1) S54 с $m=1$, $\lambda_{S54}=\rho$, $A=\widehat A$, $B_1=0$, $C=0$. Проверяем гипотезы.

(a) (1.3), $a_j\in W^1_1$: $\pm i\tau_\pm\in W^2_1\subset W^1_1$ (шаг 1).

(b) (1.3), $b^1_{jk}\in L_1$: $B_1=0$.

(c) (1.4): $C=0$, $\upsilon\equiv0$.

(d) (1.3), $b^0_{jk}\in W^1_1$ при всех $j,k$ (в частности $b^0_{jj}\in L_1=W^0_1$). По шагу 5 C24 строка
$W^{-1}$, отвечающая столбцу $(\pm,s)$, равна $\tfrac14(f_\pm,\ \mu^{-1}f_\pm)$, $f_\pm=(1,\pm1/k)$,
$\mu^{-1}=-is/\tau_\pm$; столбец $W'$, отвечающий $(\pm',s')$, равен
$g_{\pm',s'}'=\bigl(e_{\pm'}',\ is'(\tau_{\pm'}e_{\pm'})'\bigr)$, $e_{\pm'}'=(0,\pm'k')$,
$(\tau_{\pm'}e_{\pm'})'=(\tau_{\pm'}',\ \pm'(\tau_{\pm'}k)')$. Каждый элемент
$W^{-1}W'$ — сумма произведений функций из набора $1$, $1/k$, $1/\tau_\pm$ (лежат в $W^2_1$ по шагу 1) на
функции $k'$, $\tau_\pm'$, $(\tau_\pm k)'$, которые лежат в $W^1_1$, так как $k,\tau_\pm,\tau_\pm k\in W^2_1$.
Поскольку $W^1_1(0,1)$ — алгебра, $B_0\in W^1_1$ поэлементно. Именно здесь нужна гипотеза
$a\in W^2_1$: при $a\in W^1_1$ элементы $B_0$ лишь из $L_1$, и (1.3) нарушено для $b^0_{jk}$, $j\ne k$.
Это и есть условие $T^{-1}T'\in W^1_1$ карточки S54 при $T=W$.

(e) (1.12) и (1.10). Разности $a_j-a_k$ по парам столбцов:
$$
\begin{aligned}
&(+,+)-(+,-)=2i\tau_+,\quad (+,+)-(-,+)=-i(\tau_--\tau_+),\quad (+,+)-(-,-)=i(\tau_++\tau_-),\\
&(+,-)-(-,+)=-i(\tau_++\tau_-),\quad (+,-)-(-,-)=i(\tau_--\tau_+),\quad (-,+)-(-,-)=2i\tau_-
\end{aligned}
$$
(и противоположные для обратного порядка пары). Каждая разность равна $e^{i\eta_{jk}}\varrho_{jk}$ с
$\eta_{jk}\in\lbrace\pi/2,3\pi/2\rbrace$ и $\varrho_{jk}\in\lbrace2\tau_+,2\tau_-,\tau_++\tau_-,\tau_--\tau_+\rbrace$. Все $\varrho_{jk}\in W^2_1\subset W^1_1$
и положительны при всех $x\in[0,1]$: $\tau_\pm>0$, а $\tau_--\tau_+\ge m(1+\sqrt\kappa)^{-3/2}>0$ (шаг 5 C24,
использует $p\ge m^2$). Отсюда (1.10) с $\delta=\min_x\min_{jk}\varrho_{jk}>0$.

(f) Условие Биркгофа (1.8)–(1.9) на дуге $[\theta_0,\theta_1]=[0,\pi]$:
$\operatorname{Re}\bigl(e^{i\theta}\cdot\pm i\varrho_{jk}\bigr)=\mp\varrho_{jk}\sin\theta$ сохраняет знак при всех
$\theta\in[0,\pi]$ и всех $x$ (нестрого; на концах дуги равно нулю, что (1.9) допускает:
«сохраняет знак»). Сектор теоремы 1.1 с $\kappa_{S54}=h$:
$\Lambda_h=\lbrace-he^{i\pi/2}+re^{i\theta}:r\ge0,\ \theta\in[0,\pi]\rbrace=\lbrace\operatorname{Im}\rho\ge-h\rbrace=\Pi^h_+$;
по замечанию 1.1 S54 то же в $-\Lambda_h=\Pi^h_-$. Шаг 3 опирается на теорему 1.2 S54, которой (1.8) не нужно: её гипотезы (1.3), (1.4), (1.12) проверены в (a)–(e), а при $\eta_{jk}\in\lbrace\pi/2,3\pi/2\rbrace$ её секторы $\Lambda^\iota_h$ — те же полуплоскости $\Pi^h_\pm$.

**Шаг 3 (утверждение 1).** По теореме 1.2 S54 при $m=1$ в $\Pi^h_+$ есть фундаментальная матрица
$Z(x,\rho)=M_S(x)\bigl(I+\rho^{-1}R_1(x)+\rho^{-1}\mathcal R(x,\rho)\bigr)E(x,\rho)$, где по (1.13)
$E=\operatorname{diag}\bigl(\exp(\rho\int_0^x a_j)\bigr)=\operatorname{diag}\bigl(e^{is\rho t_\pm(x)}\bigr)$ и
$M_S=\operatorname{diag}\bigl(\exp\int_0^xb^0_{jj}\bigr)$. Диагональ $B_0=-W^{-1}W'$ — это функции $a_\pm$ шага 5 C24
(обозначение C24, не элементы $\widehat A$), поэтому $M_S=\mathbf D$. По (1.17) можно взять
$r^1_{jk}=q^0_{jk}/(a_k-a_j)$ при $j\ne k$, где $Q_0=\mathbf D^{-1}(B_0-D_0)\mathbf D\in W^1_1\subset C$ (шаг 2(d);
$\mathbf D^{\pm1}\in W^1_1$, так как $a_\pm\in W^1_1$) и $\lvert a_k-a_j\rvert\ge\delta$ (шаг 2(e)), так что $r^1_{jk}$
ограничены; $r^1_{jj}$ — первообразная функции из $L_1$ (при $B_1=0$ второй интеграл (1.17) равен нулю),
ограничена. По (1.22) (того же вида, что (1.16)) $\lvert\mathcal R(x,\rho)\rvert\le K(\Upsilon(\rho)+\lvert\rho\rvert^{-1})$, $\Upsilon\to0$ равномерно
при $\rho\to\infty$ в $\Pi^h_+$; выберем $r_1$ с $\lvert\mathcal R\rvert\le1$ при $\lvert\rho\rvert\ge r_1$. Положим
$\mathcal E=\rho^{-1}(R_1+\mathcal R)$: $\lvert\mathcal E\rvert\le(\sup\lvert R_1\rvert+1)/\lvert\rho\rvert$. Тогда
$Y_a=WZ=W\mathbf D(I+\mathcal E)E$ — фундаментальная матрица $Y'=\rho KY$. То же в $\Pi^h_-$ по замечанию 1.1
(с теми же $R_1$). Это утверждение 1. Столбцы:
$$
y_{\pm,s}(x,\rho)=\bigl(D_\pm(x)g_{\pm,s}(x)+r_{\pm,s}(x,\rho)\bigr)e^{is\rho t_\pm(x)},\qquad
\lvert r_{\pm,s}\rvert\le C_W\frac{C}{\lvert\rho\rvert}, \tag{1}
$$
$C_W=\sup\lvert W\mathbf D\rvert$; это (5) C24 с $\epsilon_0(r)=C/r$. Здесь использовано, что
$\mathcal E E$ имеет столбцы $\mathcal E_{\cdot,j}e^{\rho\int a_j}$, так как $E$ диагональна.

**Шаг 4 (утверждение 2).** Повторим шаг 7 C24 с (1) вместо (5) C24. Строки точки $0$ матрицы
$\mathfrak U_a$: $\widetilde U_0Y_a(0)=\widetilde U_0W(0)(I+\mathcal E(0,\rho))$ (так как $\mathbf D(0)=E(0)=I$),
их элементы отличаются от элементов $\mathfrak U^0$ на $O(1/\lvert\rho\rvert)$. Строки точки $1$: элемент
в строке $2+j$ и столбце $(\pm,s)$ равен
$\bigl((U^0_j+\rho^{-1}U^1_j)\cdot(D_\pm(1)g_{\pm,s}(1)+r_{\pm,s}(1,\rho))\bigr)e^{is\rho\ell_\pm}=
\bigl(U^0_j\cdot D_\pm(1)g_{\pm,s}(1)+O(1/\lvert\rho\rvert)\bigr)e^{is\rho\ell_\pm}$. Разложение Лапласа по строкам
1, 2: каждое слагаемое — минор строк точки $0$ (элементы ограничены, разность с минором $\mathfrak U^0$
есть $O(1/\lvert\rho\rvert)$) на минор строк точки $1$ по двум оставшимся столбцам, равный
$(m^0+O(1/\lvert\rho\rvert))e^{i\rho P}$, $P\in\lbrace0,\pm d,\pm L\rbrace$, $\lvert e^{i\rho P}\rvert\le e^{L\lvert\operatorname{Im}\rho\rvert}$
(шаг 7 C24). Произведение двух величин вида «ограниченная $+O(1/\lvert\rho\rvert)$» отличается от
произведения главных частей на $O(1/\lvert\rho\rvert)$. Итак, вместо (6) C24
$$
\det\mathfrak U_a(\rho)=\det\mathfrak U^0(\rho)+\eta_1(\rho),\qquad\lvert\eta_1(\rho)\rvert\le\frac{C}{\lvert\rho\rvert}e^{L\lvert\operatorname{Im}\rho\rvert}. \tag{2}
$$
По шагу 9 C24 $\det\mathfrak U_a=\Delta_Y\det C(\rho)$, $C(\rho)=Y_a(0,\rho)=W(0)(I+\mathcal E(0,\rho))$, поэтому
$\det C=d_0(1+\beta(\rho))$, $d_0=16\tau^0_+\tau^0_-$, $\lvert\beta\rvert\le C/\lvert\rho\rvert$. По (7), (8) C24
$\det\mathfrak U^0=c_UF$, $c_U=d_0c_\ast$ (сравнение формулы $c_\ast$ шага 9 C24 с $c_U$ шага 10 C24). Отсюда
$$
\eta=\frac{\Delta_Y}{c_\ast}-F=\frac{c_UF+\eta_1}{c_\ast d_0(1+\beta)}-F=\frac{\eta_1/c_U-\beta F}{1+\beta},
$$
и при $\lvert\rho\rvert\ge r_1$, $\lvert\beta\rvert\le\tfrac12$, с $\lvert F\rvert\le C_Fe^{L\lvert\operatorname{Im}\rho\rvert}$ (шаг 9 C24) получаем
$\lvert\eta\rvert\le C\lvert\rho\rvert^{-1}e^{L\lvert\operatorname{Im}\rho\rvert}$. Функция $\eta$ одна и та же для обеих полуплоскостей
и совпадает с $\eta$ C24 (она определена через $\Delta_Y$, не через $Y_a$); оценка верна в
$\Pi^h_+\cup\Pi^h_-=\mathbb C$. С (4) C24 это первая формула утверждения 2.

Нормировка идеи: по шагу 9 C24 $\Delta_X=\det\Lambda_\rho^{-1}\det\mathfrak U_a=\rho^N(c_UF+\eta_1)$, а
$\Delta^0=\rho^Nc_UF$ (утверждение 2 C24), так что $\Delta_X-\Delta^0=\rho^N\eta_1=O(\lvert\rho\rvert^{N-1}e^{L\lvert\operatorname{Im}\rho\rvert})$
по (2). (Определитель $\Delta_X$ зависит от выбора $Y_a$ через множитель $\det C$; оценка верна для $Y_a$
шага 3.)

**Шаг 5 (нижняя оценка $F$ у простого нуля).** Пусть задача усиленно регулярна: нули $F$ с
$\operatorname{Re}\rho\ge0$ отделены числом $\delta_s>0$ и просты при $\lvert\rho\rvert\ge R_s$. Нули $F$ симметричны
относительно $0$ (шаг 8 C24) и лежат в полосе $\lvert\operatorname{Im}\rho\rvert<h_0$ (шаг 11(i) C24). Зафиксируем
$\delta<\min(\delta_0,\delta_s/2)$ ($\delta_0$ из шага 12 C24) и $c_\delta$ из шага 11(ii) C24. Пусть $\rho^0$ — нуль $F$ с
$\operatorname{Re}\rho^0>R_s+2\delta$. В круге $\overline{B}(\rho^0,\delta)$ других нулей нет (нули с $\operatorname{Re}\ge0$ отделены
$\delta_s>2\delta$, нули с $\operatorname{Re}<0$ далеко), $\rho^0$ простой, и $g(\rho)=F(\rho)/(\rho-\rho^0)$ голоморфна и
не обращается в нуль в $\overline B(\rho^0,\delta)$. На окружности $\lvert\rho-\rho^0\rvert=\delta$ имеем
$\operatorname{dist}(\rho,Z_F)\ge\min(\delta,\delta_s-\delta)=\delta$, поэтому
$\lvert g\rvert\ge c_\delta e^{L\lvert\operatorname{Im}\rho\rvert}/\delta\ge c_\delta/\delta$. По принципу минимума модуля
$\lvert g\rvert\ge c_\delta/\delta$ во всём круге. Так как в круге $\lvert\operatorname{Im}\rho\rvert\le h_0+\delta$,
$$
\lvert F(\rho)\rvert\ge c_1\lvert\rho-\rho^0\rvert e^{L\lvert\operatorname{Im}\rho\rvert},\qquad c_1=\frac{c_\delta}{\delta}e^{-L(h_0+\delta)},\qquad
\lvert\rho-\rho^0\rvert\le\delta, \tag{3}
$$
и $\lvert F'(\rho^0)\rvert=\lvert g(\rho^0)\rvert\ge c_\delta/\delta\ge c_1$. Постоянные не зависят от $\rho^0$.

**Шаг 6 (утверждение 3).** Нумерация C24 (шаг 13) сопоставляет нули внутри
$\delta_{q(\mathcal G)}$-кластеров, $\delta_{q(\mathcal G)}\to0$. При больших $k$ имеем $\delta_{q(\mathcal G_k)}\le\delta$, а
$\delta$-кластер правее $\max(T,R_s,r_\delta)$ — одиночный круг $B(\rho_k^0,\delta)$, в котором ровно один нуль
$\Delta_Y$ (шаг 14 C24); он и есть $\rho_k=\sqrt{\lambda_k}$. Значит, $\lvert\rho_k-\rho_k^0\rvert<\delta$ и
$F(\rho_k)=-\eta(\rho_k)$. По (3) и утверждению 2
$$
c_1\lvert\rho_k-\rho_k^0\rvert e^{L\lvert\operatorname{Im}\rho_k\rvert}\le\lvert F(\rho_k)\rvert=\lvert\eta(\rho_k)\rvert\le\frac{C}{\lvert\rho_k\rvert}e^{L\lvert\operatorname{Im}\rho_k\rvert},
\qquad\text{откуда}\quad\lvert\rho_k-\rho_k^0\rvert\le\frac{C}{c_1\lvert\rho_k\rvert}.
$$
Связь с номером: по шагу 11(iii) C24 в каждом окне $[t,t+1]\times[-h_0,h_0]$ не больше $n_1$ нулей $F$,
поэтому число нулей $F$ с $T<\operatorname{Re}\rho\le t$ не больше $n_1(t-T+1)$, и с конечным числом $N_Q$ нулей
в $\widehat Q$ получаем $k\le N_Q+n_1(\operatorname{Re}\rho_k^0+1)$. Отсюда $\lvert\rho_k\rvert\ge\operatorname{Re}\rho_k^0-\delta\ge ck$ при
больших $k$ и $\rho_k-\rho_k^0=O(1/k)$. Наконец, так как $\lvert\rho_k^0\rvert\le\lvert\rho_k\rvert+\delta$,
$$
\lvert\lambda_k-\lambda_k^0\rvert=\lvert\rho_k-\rho_k^0\rvert\lvert\rho_k+\rho_k^0\rvert\le\frac{C}{c_1\lvert\rho_k\rvert}\bigl(2\lvert\rho_k\rvert+\delta\bigr)\le C'.
$$
Это утверждение 3.

**Шаг 7 (невырожденность главной матрицы в нуле $F$).** Пусть $h=h_0+1$, полоса
$\Sigma=\lbrace\lvert\operatorname{Im}\rho\rvert\le h\rbrace\subset\Pi^h_+$; возьмём $Y_a$ шага 3 в $\Pi^h_+$, так что одна и та же
матрица $\mathfrak U_a$ служит на всей полосе. Элементы $\mathfrak U^0(\rho)$ в $\Sigma$: в строках точки $0$ —
постоянные, в строках точки $1$ — $u\,e^{is\rho\ell_\pm}$ с постоянными $u$; поэтому при $\rho\in\Sigma$
$$
\lvert\mathfrak U^0_{ij}(\rho)\rvert\le C_0,\qquad\Bigl\lvert\frac{d}{d\rho}\mathfrak U^0_{ij}(\rho)\Bigr\rvert\le C_0,\qquad
\lvert\mathfrak U^0_{ij}(\rho)-\mathfrak U^0_{ij}(\rho')\rvert\le C_0\lvert\rho-\rho'\rvert
$$
($\lvert e^{is\rho\ell}\rvert\le e^{hL}$, $\ell\le L$). По формуле Якоби
$\frac{d}{d\rho}\det\mathfrak U^0=\sum_{i,j}\frac{d\mathfrak U^0_{ij}}{d\rho}\operatorname{cof}_{ij}$, и $\det\mathfrak U^0=c_UF$. Для нуля
$\rho_k^0$ из шага 6 по шагу 5 $\lvert c_UF'(\rho_k^0)\rvert\ge\lvert c_U\rvert c_1$, поэтому
$\sum_{i,j}\lvert\operatorname{cof}_{ij}(\mathfrak U^0(\rho_k^0))\rvert\ge\lvert c_U\rvert c_1/C_0$, и найдётся столбец $j_k$
матрицы $\operatorname{adj}\mathfrak U^0(\rho_k^0)$ (столбец $j$ сопряжённой матрицы состоит из алгебраических
дополнений строки $j$) с
$$
\lvert v_k^0\rvert\ge c_2:=\frac{\lvert c_U\rvert c_1}{16C_0},\qquad v_k^0:=\operatorname{adj}\mathfrak U^0(\rho_k^0)\,e_{j_k}.
$$
Так как $\mathfrak U^0\operatorname{adj}\mathfrak U^0=\det\mathfrak U^0\cdot I=0$ в $\rho_k^0$, вектор $v_k^0$ лежит в
$\ker\mathfrak U^0(\rho_k^0)$; к тому же $\lvert v_k^0\rvert\le C_3$ (дополнения — многочлены от ограниченных элементов).

**Шаг 8 (вектор ядра полной матрицы).** Положим $v_k=\operatorname{adj}\mathfrak U_a(\rho_k)\,e_{j_k}$. По шагу 4
$\det\mathfrak U_a(\rho_k)=\Delta_Y(\rho_k)\det C(\rho_k)=0$, поэтому $\mathfrak U_a(\rho_k)v_k=0$. Элементы:
$\lvert\mathfrak U_a(\rho_k)-\mathfrak U^0(\rho_k)\rvert\le C/\lvert\rho_k\rvert$ (шаг 4, без экспоненциального множителя, так как в $\Sigma$
он ограничен) и $\lvert\mathfrak U^0(\rho_k)-\mathfrak U^0(\rho_k^0)\rvert\le C_0\lvert\rho_k-\rho_k^0\rvert$, так что
$\lvert\mathfrak U_a(\rho_k)-\mathfrak U^0(\rho_k^0)\rvert\le C/k$ по шагу 6. Элементы $\operatorname{adj}$ — многочлены
степени $3$ от элементов, ограниченных в совокупности, поэтому $\lvert v_k-v_k^0\rvert\le C/k$, и при
больших $k$ $\lvert v_k\rvert\ge c_2/2$.

**Шаг 9 (утверждение 4).** Пусть $X=(w,w')$, $w(x)=(y(x),y(-x))$ для собственной функции $y$ при
$\lambda_k$. По шагам 2, 3 C24 $X(0)\in\ker(V_0+V_1\Phi(1,\lambda_k))$, и по утверждению 3 C24 при больших $k$
ядро одномерно. Решение $Y_k(x)=Y_a(x,\rho_k)v_k$ системы $Y'=\rho_kKY$ удовлетворяет условиям:
$\widetilde U_0Y_k(0)+\widetilde U_1Y_k(1)=\mathfrak U_a(\rho_k)v_k=0$; оно ненулевое ($Y_a$ фундаментальна, $v_k\ne0$),
поэтому $S_\rho^{-1}Y_k$ — ненулевое решение задачи в переменных $(w,w')$ (шаг 4 C24:
$\widetilde U_0+\widetilde U_1Y_c=\Lambda_\rho(V_0+V_1\Phi)S_\rho^{-1}$ и $\Lambda_\rho$ обратима), и с точностью до множителя
$Y_k=(w_k,w_k'/\rho_k)$, где $w_k$ — сложенная собственная функция. По (1)
$$
Y_k(x)=\sum_{\pm,s}(v_k)_{\pm,s}\bigl(D_\pm(x)g_{\pm,s}(x)+r_{\pm,s}(x,\rho_k)\bigr)e^{is\rho_kt_\pm(x)}.
$$
Замены с остатком $O(1/k)$ равномерно по $x\in[0,1]$: $r_{\pm,s}=O(1/\lvert\rho_k\rvert)=O(1/k)$ при
$\lvert e^{is\rho_kt_\pm}\rvert\le e^{hL}$; $\lvert e^{is\rho_kt}-e^{is\rho_k^0t}\rvert\le t\lvert\rho_k-\rho_k^0\rvert e^{hL}=O(1/k)$ при
$t\le L$; $v_k=v_k^0+O(1/k)$; $D_\pm g_{\pm,s}$ ограничены. Получаем
$Y_k(x)=\sum(v^0_k)_{\pm,s}D_\pm g_{\pm,s}e^{is\rho_k^0t_\pm}+O(1/k)$. Делим на $\lvert v_k^0\rvert\in[c_2,C_3]$ и
полагаем $C^{(k)}=v_k^0/\lvert v_k^0\rvert\in\ker\mathfrak U^0(\rho_k^0)$; остаток остаётся $O(1/k)$. Первые две
компоненты $g_{\pm,s}$ — $e_\pm$, последние две — $is\tau_\pm e_\pm$, а $w_k=(y_k(x),y_k(-x))$,
$w_k'=(y_k'(x),-y_k'(-x))$; это две формулы утверждения 4. Значение главной части в $x=0$:
$\sum C^{(k)}_{\pm,s}g_{\pm,s}(0)=W(0)C^{(k)}$ ($D_\pm(0)=1$, $t_\pm(0)=0$), и
$\lvert W(0)C^{(k)}\rvert\ge\lVert W(0)^{-1}\rVert^{-1}$.

## Lean

Формализации нет, и в библиотеке нет объектов, на которые опирались бы шаги: матрицы Коши
системы, голоморфной по параметру, характеристического определителя, асимптотической
фундаментальной матрицы. Складывание есть только для области Дирихле (`memDirichletH2_iff_fold`,
`MemDirichletH2.fold`, запись C24). Шагам 7, 8 нужны сопряжённая матрица (`Matrix.adjugate`,
`Matrix.mul_adjugate`) и производная определителя, шагу 5 — принцип максимума модуля, применённый к
$1/g$; имена в закреплённой версии Mathlib не проверялись. Пространств $W^2_1$ с цепным правилом (шаг 1)
в библиотеке нет. Теорема 1.2 S54 вошла бы
гипотезой: «для $\widehat A$ с (1.12), $B_0\in W^1_1$, $B_1=0$ в $\operatorname{Im}\rho\ge-h$ существует
фундаментальная матрица $\mathbf D(I+\mathcal E)E$ с $\sup_x\lvert\mathcal E\rvert\le C/\lvert\rho\rvert$ при $\lvert\rho\rvert\ge r_1$».
Вместе с ней гипотезами вошли бы утверждения 2, 3 C24 (сами не формализованы).

## Границы

- Класс $a$: $a\in W^2_1$ и $0<p<1$ всюду, без нулей $p$. При $a\in W^1_1\setminus W^2_1$ нарушается
  $b^0_{jk}\in W^1_1$ (шаг 2(d)), и S54 неприменима; остаётся $o(1)$ C24. В нулях $p$ нарушаются (1.10) и
  (1.12) ($\tau_-=\tau_+$), это идея I42. При $p<0$ или $p\to1$ — как в «Границах» C24.
- Утверждения 3, 4 требуют усиленной регулярности, то есть отделённости нулей $F$ числом
  $\delta_s>0$: постоянная $c_1$ шага 5 пропорциональна $c_\delta/\delta$ при $\delta<\delta_s/2$, и без зазора
  оценка (3) не равномерна. Это согласуется с идеей I37: для остатка $O(1/k)$ у собственной функции
  нужна отделённость $d\ge c>0$. Задача Дирихле при иррациональном $\ell_+/\ell_-$ (утверждение 4 C24) не
  усиленно регулярна, и для неё пункты 3, 4 не доказаны; оценка $O(k^{-1/2})$ там по-прежнему открыта
  (нужна нижняя оценка $\lvert F\rvert$ через два ближайших нуля). Утверждение 2 от регулярности не зависит.
- Вторая часть (A) идеи I43 (группы из $\nu$ нулей, $O(k^{-1/\nu})$, симметрические функции с
  $O(1/k)$) здесь не доказывается, хотя утверждение 2 даёт для неё оценку остатка; нужна лемма о
  нижней оценке $F$ через произведение по группе, аналог шага 5.
- Связь номера с нулём: доказано только $k\le C\operatorname{Re}\rho_k^0$ (шаг 6), этого хватает для $O(1/k)$ и
  $\lambda_k-\lambda_k^0=O(1)$; обратная оценка $\lvert\rho_k^0\rvert\le Ck$ не доказывается.
- Вектор $C^{(k)}$ определён через ядро $\mathfrak U^0(\rho_k^0)$; одномерность этого ядра доказана
  (ранг $3$ по шагу 7), так что $C^{(k)}$ единствен с точностью до множителя с модулем $1$. Явных формул для
  $C^{(k)}$ по видам условий нет.
- Базисность, кратности как алгебраические кратности оператора и отсутствие присоединённых функций
  не утверждаются (как в C24). Остаток $O(1/k)$ у собственных функций — равномерная оценка на $[0,1]$ в
  сложенных переменных, то есть на $[-1,1]$ для $y_k$ и $y_k'/\rho_k$.
- Младших членов в уравнении нет (решение пользователя); члены $U^1$ условий учтены в шагах 4, 8.
- Идея-источник — I43 (утверждения (A), (B), (D) и раздел «Критика» 2026-10-25); карточка S54.

**Рецензия (2026-11-05).**

Гипотезы: (H2) — $a$ вещественна, $a\in W^2_1(-1,1)$, $0<p<1$ всюду на $[-1,1]$; формы $U_1,U_2$ нормированы и независимы. Пункты 3, 4 — дополнительно при усиленной регулярности. Выводы: остаток $\mathcal E=O(1/\lvert\rho\rvert)$ равномерно по $x\in[0,1]$ в $\Pi^h_\pm$; $\eta=O(\lvert\rho\rvert^{-1}e^{L\lvert\operatorname{Im}\rho\rvert})$ на всей плоскости при $\lvert\rho\rvert\ge r_1$; $\rho_k-\rho_k^0=O(1/k)$; равномерная на $[0,1]$ асимптотика сложенных собственных функций с остатком $O(1/k)$.

1. Шаг 2(f), пометка [пробел] и абзац «Границы» о нестрогом знаке в (1.8). Вес: неточность. Запасной путь из самой записи замыкает шаг. По карточке S54 (сверка «совпадает») теорема 1.2 требует только (1.3), (1.4) и (1.12), а их проверяют пункты (a)–(e). При $\eta_{jk}\in\lbrace\pi/2,3\pi/2\rbrace$ критические лучи $\arg\rho=\pi/2-\eta_{jk}$ лежат на вещественной оси, поэтому секторы $\Lambda^\iota_h$ — это $\lbrace\operatorname{Im}\rho\ge-h\rbrace$ и $\lbrace\operatorname{Im}\rho\le h\rbrace$. Матрицы $R_1$ берутся по (1.17) независимо от сектора, оценка (1.22) того же вида, что (1.16). Требуется опереть шаг 3 прямо на теорему 1.2, а пометку и пункт «Границ» убрать или переписать как замечание. Пробела в выводе нет.

Других замечаний нет. Проверено по шагам:
- шаг 1: композиции $\varphi\circ u$ с $\varphi\in C^2$ на отрезках значений, отделённых от особенностей. Знак $a$ постоянен, поэтому $\lvert a\rvert\in W^2_1$;
- шаг 2(d): $B_0\in W^1_1$ — произведения функций из $W^2_1$ на производные функций из $W^2_1$;
- шаг 2(e): шесть разностей $a_j-a_k$ и их аргументы;
- шаг 3: $M_S=\mathbf D$, поскольку диагональ $-W^{-1}W'$ равна $a_\pm$ из C24, шаг 5. Ограниченность $R_1$ — по (1.17);
- шаг 4: в столбце $\mathcal EE$ стоит экспонента своего столбца, а в минорах строк точки $1$ — общий множитель $e^{i\rho P}$ с $\lvert P\rvert\le L$;
- шаг 5: принцип минимума модуля для $g=F/(\rho-\rho^0)$. Диск не содержит других нулей: зазор $\delta_s>2\delta$ и $\operatorname{Re}\rho^0>R_s+2\delta$;
- шаг 6: оценка $k\le N_Q+n_1(\operatorname{Re}\rho_k^0+1)$ по окнам шага 11(iii) C24;
- шаг 7: формула Якоби, $16$ дополнений, столбец $\operatorname{adj}$, ранг $3$;
- шаги 8, 9: $\rho_k$ лежит в полосе $\Sigma\subset\Pi^h_+$ (так как $\lvert\operatorname{Im}\rho_k\rvert<h_0+\delta\le h$), отсюда отсутствие экспоненциального множителя. Липшицевость $\operatorname{adj}$, оценка $\lvert e^{is\rho t}-e^{is\rho^0t}\rvert\le L e^{hL}\lvert\rho-\rho^0\rvert$ при $t\le L$. Одномерность ядра (утверждение 3 C24) даёт совпадение $S_\rho^{-1}Y_k$ со сложенной собственной функцией с точностью до множителя.

Зависимости: C24 принята рецензией 2026-10-26 и применяется в пределах (H), которую даёт шаг 1. Карточка S54 сверена, вердикт «совпадает».

Пересчёт в SymPy:
- тождество $\frac{c_UF+\eta_1}{c_\ast d_0(1+\beta)}-F=\frac{\eta_1/c_U-\beta F}{1+\beta}$ при $c_U=d_0c_\ast$;
- строки $W^{-1}$ из шага 2(d): $\tfrac14(f_\pm,\mu^{-1}f_\pm)$ с $\mu=is\tau_\pm$ дают $W^{-1}W=I$;
- $\det W=16k^2\tau_+\tau_-$.

Вручную: $d_0c_\ast=c_U$ по формулам шагов 9, 10 C24.

Вердикт: принято (с неточностью 1).
