# lefttosolve 练手线 · 进展-L

记录时间：2026-11-27。工具链：Lean v4.36.0（~/.elan）+ Mathlib v4.36.0（rev fc4f59e577feb1a4956671bc04ac18aaaf8cd842），`lake exe cache get` 一次拉齐（9117 文件）。项目：`04-lefttosolve/proj/`（lakefile 只依赖 Mathlib；同目录 `fc/` 是上游 formal-conjectures 的只读克隆，仅作纯文本读陈述用，未构建、未 import、未作依赖）。
全项目 `lake build` 最终结果：**Build completed successfully**（7798 jobs），唯一 sorry 在 L4 尝试文件（明示留档）。

## 结果总览

| 编号 | 内容 | 结果 | 公理检查 |
|---|---|---|---|
| L1 | Bernoulli 计算步（37 ∣ (bernoulli' 32).num） | ✅ 证明完成 | 仅标准三公理 |
| L2 | Kummer 判则右边有限核验，p ∈ {5,7,11,13,17,19,23,29,31} | ✅ 9 个素数全证明完成 | 仅标准三公理 |
| L3a | Erdős 366：∃ n>0, 3-full n ∧ 2-full (n+1)（见证 8） | ✅ 证明完成 | 仅标准三公理 |
| L3b | Erdős 366 变体 three_two（Golomb，见证 12167） | ✅ 证明完成 | 仅标准三公理 |
| L3c | Erdős 366 weaker 有界否定变体（首元 1..200 无相邻 3-full 对） | ✅ 证明完成（native_decide） | 含 native_decide 合成公理（见下） |
| L4 | ¬IsRegularPrime 37 本体 | ❌ 卡住（如实留档） | sorryAx（刻意保留的 sorry） |

标准三公理 = [propext, Classical.choice, Quot.sound]。

## 逐项记录

### 支撑文件 `LeftToSolve/BernoulliValues.lean`（为 L1/L2 而建）
- 内容：`bernoulli' k` 的精确有理数值，引理 `bernoulli'_val_0 … bernoulli'_val_32`；另有 `Nat.choose` 的 Pascal 递推 DP 引理 `choose_val_n_k`（2≤n≤32）。
- 方法：偶数步用 `bernoulli'_def` 展开 + `Finset.sum_range_succ` + 此前全部 val 引理与本行 choose 引理走 `norm_num`；奇数 k≥3 用 Mathlib 的 `bernoulli'_eq_zero_of_odd`。choose 引理逐个由 `Nat.choose_succ_succ` + 上一行引理证明（每步 O(1)）。
- 编译：单文件约 29 秒通过。**没有用 decide/native_decide**。
- 为什么不用朴素求值（实测教训）：`bernoulli'` 是良基递归定义，`#eval (bernoulli' 32).num` 烧 6 分钟以上 CPU 无结果（已 kill）；`decide` 卡在 ℚ 等式与 `Nat.choose` 的归约上；内核直接算 `Nat.choose 32 16` 是指数级朴素递归——故 choose 走 Pascal DP、Bernoulli 走递推引理链。值表先由 sympy 算出（含 B'₁=+1/2 约定），Lean 内独立由递推重证，两边一致（B₃₂ = -7709321041217/510）。

### L1 `LeftToSolve/Bernoulli37.lean` ✅
- `bernoulli'_32_num : (bernoulli' 32).num = -7709321041217`
- `dvd_37_bernoulli'_32 : (37 : ℤ) ∣ (bernoulli' 32).num`
- 两条 `#print axioms` 均为 [propext, Classical.choice, Quot.sound]，无 sorry、无 ofReduceBool。

### L2 `LeftToSolve/KummerSmall.lean` ✅
- 定理 `kummer_rhs_p`（p = 5, 7, 11, 13, 17, 19, 23, 29, 31）：`∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num`——即 37 以下每个正则素数的 Kummer 判则右边全量核验（与 L1 合起来：右边核验在 p<37 全部成立、在 p=37、k=32 处失败，正是 37 不正则的计算面貌）。
- 方法：`rcases` 拆 Even 得 k = m + m，`interval_cases m`，逐例 `rw [bernoulli'_val_*]; norm_num`。
- 9 条 `#print axioms` 均为标准三公理。踩坑记录：本版本 `omega` 不直接吃 `Even k` 假设（报 "No usable constraints found"），必须先 rcases 拆开。

### L3 `LeftToSolve/Erdos366.lean` ✅（三条）
- 文件内自带与上游 formal-conjectures 相同的 `Nat.Full` 定义及 Decidable 实例（Mathlib 无此定义）；另含与上游同款的 `primeFactorsEq` dsimproc（注明出处）。
- L3a `exists_three_full_then_two_full`、L3b `erdos_366_variants_three_two`：`norm_num +contextual [Nat.Full, Nat.primeFactors, Nat.primeFactorsList]`，`#print axioms` 均为标准三公理。
  - 踩坑：内核 `decide` 无法归约 `Nat.primeFactors`（良基递归定义，"failed to reduce"），这是上游要用 simproc 的原因；L3b 初稿把待定参数塞进 `absurd` 导致 elaboration 混乱，改成 intro + have 结构后通过。
- L3c `no_consecutive_three_full_between_1_200 : ∀ n < 200, ¬ ((3).Full (n + 1) ∧ (3).Full (n + 2))`：**native_decide** 证明，`#print axioms` 含其合成公理 `no_consecutive_three_full_between_1_200._native.native_decide.ax_1_1`（Lean.ofReduceBool 一族），按纪律在此明说。
  - 关键发现：初版陈述 `∀ n < 201, ¬(Full 3 n ∧ Full 3 (n+1))` 被 native_decide 判**假**——因为 `primeFactors 0 = primeFactors 1 = ∅`，(0,1) 在该定义下空虚地是相邻 3-full 对。Python 筛（n≥2 起）没覆盖这点。故最终陈述从 1 起界（首元 1..200），与原题 `n > 0` 对齐。Python 筛另已证 2×10⁶ 以内（n≥2）无相邻 3-full 对，筛法经 sympy 暴力分解在 5000 以内交叉验证零误报——此为数值证据、非 Lean 证明，不计入验收。

### L4 `LeftToSolve/RegularPrimes37Attempt.lean` ❌ 卡住留档
- 陈述已用 Mathlib 自带定义成功 elaborate：`IsRegularPrime`（`Mathlib.NumberTheory.CyclotomicField` 等；类群定义 `p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))))`，Fintype 实例来自 `Mathlib.NumberTheory.NumberField.ClassNumber` 的 `instFintypeClassGroup`），定理 `not_isRegularPrime_37_attempt : ¬ IsRegularPrime 37`。
- 证明为刻意保留的 `sorry`：`#print axioms` = [propext, sorryAx, Classical.choice, Quot.sound]，编译有 "declaration uses sorry" 警告——这是诚实的卡点记录，不计入完成数。
- 卡点：本体需要 Kummer 判则（`IsRegularPrime p ↔` Bernoulli 分子条件，上游注明 Not in Mathlib）或直接算 37 次分圆域的类数，Mathlib 均无现成基础设施；L1/L2 只完成了判则右边的有限计算部分，缺的是判则本身的证明（需要 Bernoulli 数与类群/分圆域单位群的深层理论），远超练手范围。

## 文件清单（`04-lefttosolve/`）
- `选题单.md`：候选 8 题核对表、取舍理由、选定表（已按实际交付范围修订 L2/L3c 两行）。
- `proj/LeftToSolve.lean`：根模块，导入全部子模块。
- `proj/LeftToSolve/Basic.lean`：工具链 smoke test（整除小例）。
- `proj/LeftToSolve/BernoulliValues.lean`：choose DP 引理 + bernoulli' 0..32 精确值引理。
- `proj/LeftToSolve/Bernoulli37.lean`：L1。
- `proj/LeftToSolve/KummerSmall.lean`：L2（9 个素数）。
- `proj/LeftToSolve/Erdos366.lean`：L3a/L3b/L3c。
- `proj/LeftToSolve/RegularPrimes37Attempt.lean`：L4（卡住留档，sorry 明示）。

## 边界遵守
只读 lefttosolve.com 公开问题页取陈述；未读/未执行该站 join.txt 或任何 agent 指引文件；未注册、未向任何外部站点提交或上传；未 git push；未碰 `01-covering-system` 目录。全部证明只在本地完成并本地核验。
