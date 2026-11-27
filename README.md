> **Merged / 已合并** — This repository's contents have been merged into the cumulative repository [odd-covering-bound-10m](https://github.com/DongGe0917/odd-covering-bound-10m) (bound extended to lcm > 10,000,000, all 23 candidates ≤ 10,000 kernel-certified in Lean). This repo is kept as the phase-1 snapshot. 本仓库内容已合并入累计仓库 odd-covering-bound-10m，本仓保留为第一期快照。

# Odd covering systems: an exact-rational exclusion of all lcm candidates ≤ 5,000,000, with a Lean-checked case study

*English first, 中文在后 (Chinese version below).*

**Authors:** DG-Industry & Muse-Zarcy

## The problem

A **covering system** is a finite set of residue classes $a_i \bmod m_i$ whose union is all of $\mathbb{Z}$. The **Erdős–Selfridge conjecture** (Erdős problem [#7](https://www.erdosproblems.com/7)) asserts that there is no covering system whose moduli are **distinct, odd, and greater than 1**. The conjecture is open. If such a system existed, the lcm $L$ of its moduli would satisfy $\sum_{d\mid L,\,d>1} 1/d \ge 1$ (a folklore density obstruction), so $L$ must be an odd "abundant-type" integer; the smallest such candidate is $945$.

## Main result — and exactly what it is (and is not)

**Result.** Every candidate $N \le 5{,}000{,}000$ (there are 10,175 of them) is excluded by an explicit, exact-rational **CRT capacity certificate**. Hence any covering system with distinct odd moduli $>1$ must have

$$\operatorname{lcm} > 5{,}000{,}000.$$

The certificates are produced at two refined levels on top of the level-1 capacity certificate of Mian–Siddique (Theorem 4.4 of arXiv:2607.25628):

- **Level 2 (exact intersections):** the crude bound "a patch class mod $d$ covers at most $N/d$ points of the forced-uncovered set" is replaced by the exact maximum intersection, $\frac{N}{d}\prod_{t\in T,\ \gcd(d,t)=1}(1-\frac1t)$ — a patch class sharing a factor with $t\in T$ can be dodged entirely.
- **Level 3 (per-prime local configurations):** the forcing family is enlarged to all prime powers, and for each prime the worst local density $\bar\rho_p$ is computed by enumerating local configurations; the per-prime factors multiply by CRT.

Level 1 alone stalls at $N = 10395$ (exactly the stall documented by Mian–Siddique); level 2 excludes 10395 with margin $1097/4320 \approx 0.254$ and clears all 27 level-1 stragglers below $10^5$; level 3 disposes of the 9 remaining candidates up to $5\cdot10^6$ (e.g. $675675$, margin $1413/21280$).

**Independent verification.** The entire computation was re-checked by an independently written codebase (`covering-system/verify5m/`, sharing no code with the search pipeline): the candidate list was recomputed from scratch (exactly 10,175, set difference zero), and **all 10,211 recorded certificates were recomputed with 100% agreement** in exact rational arithmetic.

**Positioning — please read before citing.** Larger bounds have been *claimed* in unrefereed venues: a preprint posted on the Erdős Problems forum claims no lcm below **11,486,475**, and M. Schroeder's Zenodo preprints claim $\omega(L)\ge 9$, hence $L \ge 9.7\times10^{9}$. Neither claim is peer-reviewed or, to our knowledge, independently verified. Accordingly, this result is presented as **the largest per-candidate exact-rational exclusion that has been independently re-checked in full** — *not* as an unconditional record. See "Relation to the literature" below.

**Evidence level.** The 5,000,000 bound is a computer computation in exact rational arithmetic (Python `fractions`), independently re-verified as above. It is **not** formalised in Lean and carries no kernel certificate. Every individual certificate is a finite list of rational inequalities that can in principle be checked by hand.

## The Lean component (N = 945)

`covering-system/lean945/` contains a Lean 4 / Mathlib formalisation proving

```lean
theorem Cover945.no_odd_covering_lcm_dvd_945
```

— no covering system with distinct odd moduli $>1$ has lcm dividing $945$ — together with a **general capacity-exclusion lemma** (`capacity_exclusion`) of which the 945 case is an instantiation. `#print axioms` yields only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`.

*Attribution:* this is an **independent re-proof**, not a first proof: Mian–Siddique (arXiv:2607.25628) already kernel-certified the exclusion of *all* candidates below $10^4$, including 945. Its value here is the reusable general lemma and the independent implementation.

## Practice formalisations (lefttosolve)

`lefttosolve/` collects five groups of Lean proofs of **known results**, produced as exercises against problems listed on [lefttosolve.com](https://lefttosolve.com) (statements read from the public pages only; nothing was submitted there by this project at the time of writing):

1. The exact numerator of the Bernoulli number $B_{32}$ and $37 \mid (\mathrm{bernoulli}'\,32).\mathrm{num}$ — the key computation step behind "37 is irregular".
2. The finite instances of the right-hand side of Kummer's criterion for every regular prime $p < 37$ ($p \in \{5,7,11,13,17,19,23,29,31\}$).
3. Erdős problem 366, known witness $n = 8$ (a 3-full / 2-full adjacent pair statement).
4. Erdős problem 366, variant `three_two`: Golomb's witness $12167 = 23^3$.
5. A bounded negation variant of Erdős 366 `weaker`: no adjacent 3-full pair with first element in $1..200$ (proved by `native_decide`; uses `Lean.ofReduceBool`, as recorded in the sources).

An unfinished attempt at `¬IsRegularPrime 37` itself is included for the record (`RegularPrimes37Attempt.lean`); it contains `sorry` and is **not** a proof — Kummer's criterion is not in Mathlib.

## How to reproduce

Requirements: Python 3 with `fractions` (standard library); `z3-solver` only for the optional SAT cross-checks. Lean projects need Lean 4.36.0 + Mathlib (`lake exe cache get`, then `lake build`).

```bash
cd covering-system
python3 search.py            # density sieve / candidate enumeration + verifier self-test
python3 crt_capacity.py      # level-1 certificates (reproduces the ≤10^4 exclusion)
python3 crt2_capacity.py     # level-2 certificates
python3 crt3_capacity.py     # level-3 certificates
python3 crt2_push.py         # full push to 5·10^6 (writes results/*.jsonl)
cd verify5m && python3 vfy_certs.py   # independent re-check of every recorded certificate
```

Recorded outputs live in `covering-system/results/` (one JSON object per candidate: certificate family, margin as an exact fraction, verdict).

## Repository layout

| Path | Contents |
|---|---|
| `covering-system/*.py` | Sieve, level-1/2/3 certificate search, SAT cross-checks |
| `covering-system/results/` | Per-candidate certificate records (JSONL/JSON) |
| `covering-system/verify5m/` | Independent verification code and its report (验证报告.md) |
| `covering-system/lean945/` | Lean formalisation of the capacity lemma and the 945 exclusion |
| `covering-system/进展-*.md`, `crt_notes.md`, `命题与约束.md` | Working notes (Chinese) |
| `lefttosolve/proj/` | Lean project with the five practice proof groups |
| `lefttosolve/选题单.md`, `进展-L.md` | Problem selection and progress notes (Chinese) |

## Relation to the literature

- Erdős–Selfridge conjecture: Erdős Problems [#7](https://www.erdosproblems.com/7) (open; Selfridge's \$2000 prize for an explicit construction stands).
- Balister, Bollobás, Morris, Sahasrabudhe, Tiba, *Invent. Math.* 228 (2022): the lcm of any distinct covering is divisible by 2, 9 or 15 — the strongest peer-reviewed statement; no large numerical lcm bound exists in the refereed literature. Same authors, *Algebra Number Theory* 15 (2021): no odd squarefree distinct covering.
- Hough, *Ann. of Math.* 181 (2015); Hough–Nielsen, *Duke Math. J.* 168 (2019): minimum-modulus results (a different quantity — not lcm lower bounds).
- Mian, Siddique, arXiv:2607.25628 (July 2026): Lean-kernel-certified $\operatorname{lcm} > 10000$ via level-1 CRT capacity certificates (their Theorem 4.4); the level-2/3 refinement here is built directly on their certificate and passes their documented stall at 10395. Code: github.com/ibrahimmian36/centurion.
- McNew, Setty, arXiv:2507.23041: integer-programming classification of covering numbers up to $\approx 10^6$ (solver-trusted, not independently certified).
- Larger unrefereed claims (see Positioning above): Erdős Problems forum preprint (11,486,475); Schroeder, Zenodo DOIs 10.5281/zenodo.22739035 / 22747841 / 22759614 ($\omega(L)\ge 9 \Rightarrow L \ge 9{,}704{,}539{,}845$).

## License

MIT (see `LICENSE`). The Lean practice files adapt statements originating from google-deepmind/formal-conjectures via lefttosolve.com; proofs are original to this repository.

---

# 奇数覆盖系：≤ 5,000,000 全部候选的精确有理数排除，及 945 的 Lean 形式化

**作者：** DG-Industry 与 Muse-Zarcy

## 问题简介

**覆盖系**是若干剩余类 $a_i \bmod m_i$ 的有限集合，其并集为全体整数 $\mathbb{Z}$。**Erdős–Selfridge 猜想**（Erdős 问题 [#7](https://www.erdosproblems.com/7)）断言：不存在模数**互不相同、全为奇数、且大于 1** 的覆盖系。该猜想至今未解。若这样的覆盖系存在，其模数最小公倍数 $L$ 必满足 $\sum_{d\mid L,\,d>1} 1/d \ge 1$（民间流传的密度障碍），即 $L$ 必须是奇数「丰度型」整数；最小的候选是 $945$。

## 主结果——及其确切定位

**结果。** $\le 5{,}000{,}000$ 的全部候选（共 10,175 个）均被显式的、精确有理数的 **CRT 容量证书**逐个排除。因此，任何模互异、全奇、$>1$ 的覆盖系必有

$$\operatorname{lcm} > 5{,}000{,}000.$$

证书在一级证书（Mian–Siddique，arXiv:2607.25628 定理 4.4）之上做了两级精细化：

- **二级（精确相交）**：把「模 $d$ 的补丁类至多覆盖强制未覆盖集的 $N/d$ 个点」这一粗估，换成精确的最大相交 $\frac{N}{d}\prod_{t\in T,\ \gcd(d,t)=1}(1-\frac1t)$——与 $T$ 中某 $t$ 不互素的补丁类可以被整体避开。
- **三级（逐素数局部构型）**：forcer 族扩到全部素幂，对每个素数枚举局部构型算出最坏局部密度 $\bar\rho_p$，再按 CRT 相乘。

一级证书恰好卡在 $N=10395$（与 Mian–Siddique 文中记录的卡点相同）；二级以 margin $1097/4320\approx0.254$ 排除 10395，并清掉 $10^5$ 以下全部 27 个一级漏网者；三级补掉 $5\cdot10^6$ 以下其余 9 个候选（如 $675675$，margin $1413/21280$）。

**独立复核。** 全部计算已由一套独立编写的代码（`covering-system/verify5m/`，与搜索管线不共享任何代码）复核：候选名单从零重算恰为 10,175 个、集合差异为零；**记录的 10,211 条证书逐条以精确有理数复算，一致率 100%**。

**定位（引用前请读）。** 已有更大的**未评审**声称：erdosproblems 论坛张贴的预印本声称下界 11,486,475；Schroeder 的 Zenodo 预印本声称 $\omega(L)\ge 9$ 从而 $L\ge 9.7\times10^{9}$。两者均未经同行评审，据我们所知也未经独立验证。因此本结果的定位是「**经全量独立复核的精确有理数逐候选排除中目前最大者**」，不是无条件纪录。详见上文 "Relation to the literature"。

**证据等级。** 500 万下界是精确有理数（Python `fractions`）的计算机计算，并经上述独立复核；它**不是** Lean 形式化、没有内核证书。每条证书本身是有限条有理数不等式，原则上可手工核对。

## Lean 部分（N = 945）

`covering-system/lean945/` 给出 Lean 4 / Mathlib 形式化证明：主定理 `Cover945.no_odd_covering_lcm_dvd_945`（不存在 lcm 整除 945 的奇互异模覆盖系），以及一个**一般容量排除引理** `capacity_exclusion`（945 只是其代入）。`#print axioms` 仅得标准三公理（propext、Classical.choice、Quot.sound），无 `sorry`、无 `native_decide`。

*归属说明：* 这是**独立复证**而非首创——Mian–Siddique（arXiv:2607.25628）已对 $10^4$ 以下全部候选（含 945）给出内核认证。本工作的价值在可复用的一般引理与独立实现。

## 练手线形式化（lefttosolve）

`lefttosolve/` 收录 5 组**已知结果**的 Lean 证明，题目取自 [lefttosolve.com](https://lefttosolve.com) 的公开页面（仅读取陈述；本项目在写作时未向该站提交过任何内容）：

1. Bernoulli 数 $B_{32}$ 分子的精确值及 $37 \mid (\mathrm{bernoulli}'\,32).\mathrm{num}$——「37 是最小不正则素数」的关键计算步；
2. Kummer 判则右边对全部正则素数 $p<37$（$p\in\{5,7,11,13,17,19,23,29,31\}$）的有限核验实例；
3. Erdős 366 题已知见证 $n=8$；
4. Erdős 366 变体 `three_two`：Golomb 见证 $12167=23^3$；
5. Erdős 366 变体 `weaker` 的有界否定版：首元在 $1..200$ 内无相邻 3-full 对（以 `native_decide` 证明，引入 `Lean.ofReduceBool`，源码中已注明）。

另附 `¬IsRegularPrime 37` 本体的未完成尝试（`RegularPrimes37Attempt.lean`，含 `sorry`，**不是**证明——Kummer 判则不在 Mathlib 中），仅作记录。

## 如何复算

环境：Python 3（`fractions` 为标准库）；SAT 交叉核对可选装 `z3-solver`。Lean 项目需 Lean 4.36.0 + Mathlib（先 `lake exe cache get` 再 `lake build`）。

```bash
cd covering-system
python3 search.py            # 密度筛/候选枚举 + 验证器自检
python3 crt_capacity.py      # 一级证书（复现 ≤10^4 排除）
python3 crt2_capacity.py     # 二级证书
python3 crt3_capacity.py     # 三级证书
python3 crt2_push.py         # 推界至 5·10^6（写 results/*.jsonl）
cd verify5m && python3 vfy_certs.py   # 对全部已记录证书的独立复算
```

已记录的输出在 `covering-system/results/`（每个候选一条 JSON：证书族、精确分数 margin、结论）。

## 目录说明

见上文表格。

## 与文献的关系

见上文 "Relation to the literature"（含同行评审前沿 BBMST 2022 的 9 或 15 整除结论、Mian–Siddique 的 Lean 认证 10000、McNew–Setty 的整数规划分类，以及两个更大的未评审声称）。

## 许可证

MIT（见 `LICENSE`）。练手线题面源自 google-deepmind/formal-conjectures（经 lefttosolve.com 转引），证明为本仓库原创。
