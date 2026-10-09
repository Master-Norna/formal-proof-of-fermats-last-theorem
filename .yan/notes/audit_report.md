# FLT Lean 包只读审计报告 — 2026-10-09

审计方式：只读（grep / 读文件 / 跑 lake build）。未修改任何 .lean。
**注意**：审计期间 Assembly.lean 正被另一进程反复编辑（同一文件在两次读取间隔
内容变化），第 1 项的构建结果反映观察时刻状态，最终以主线收口后的复跑为准。

---

## 总判定（待第 1、5 项复跑后确认）

按任务书 7 项计：**当前可判定 4 项中 3.5 项不符**——

- 第 1 项（观察时刻）：**红**，`lake build` 与 `FermatFLT.Assembly` 均失败（文件
  正在被主线编辑，多次观察到不同版本与不同错误）；其余四模块各自绿。
- 第 2 项：✅ 无真实代码行的 sorry / admit / fail。
- 第 3 项：✅ 恰好 3 条 axiom，签名与 doc 符合规格（primitive、p≥5、文献均在）。
- 第 4 项：⚠ 大部分符合，**唯一不符：Foundations.lean 未包 `namespace FermatFLT`**
  （5 个模块中 4 个有）；import 边界两条约束均成立。
- 第 6 项：⚠ 与 lit_check.md 有 3 处出入（Ribet 末页 477 vs 476；Wiles 末页
  577 vs 578；Taylor–Wiles 期刊 Ann. of Math. 141 vs Invent. Math. 121）。
- 第 1、5 项复跑：待主线构建完成后执行（命令见下）。

---

## 1. 构建状态（观察时刻；待主线完成后复跑）

在收到"避免抢锁"补充约束**之前**已跑过一轮（命令行完整输出见 .yan 各 log 或本次
会话记录）：

| 命令 | 退出码 | 结果 |
|---|---|---|
| `lake build`（全默认目标） | **1** | ✖ FermatFLT.Assembly 失败 |
| `lake build FermatFLT.Foundations` | 0 | ✅ |
| `lake build FermatFLT.FLT4` | 0 | ✅ |
| `lake build FermatFLT.FermatLittle` | 0 | ✅（仅 4 条 lint warning：haveI/simpa，非错误） |
| `lake build FermatFLT.WilesBridge` | 0 | ✅ |
| `lake build FermatFLT.Assembly` | **1** | ✖ 失败 |

观察到的 Assembly 失败（随文件被编辑而变，出现两代错误形态，均在该文件故意之外
之外的编辑中间态）：

- 版本 A（约 120 行）：`70:5 Function expected at fermatLastTheoremFor_iff_int ...
  End (it is an iff, not a function)` ；`82: unsolved goals case neg ... ⊢ FLT p`。
- 版本 B（118 行，改后）：`71:6 Unknown identifier
  `Mathlib.NumberTheory.FLT.Three.fermatLastTheoremThree`` （注意：mathlib 的
  `fermatLastTheoremThree` 在 root 命名空间，位于 `Mathlib.NumberTheory.FLT.Three`
  *模块* 而非 *命名空间*，点路径限定写错）；`94/99: Function expected at hOdd`
  （`subst` 改写后 `hOdd : Odd 2` 不是函数）。

**待复跑的精确命令（主线 `lake build` 收口后执行）**：

```powershell
lake build;                                                   "EXIT=$LASTEXITCODE"
lake build FermatFLT.Foundations;    "FOUND=$LASTEXITCODE"
lake build FermatFLT.FLT4;           "FLT4=$LASTEXITCODE"
lake build FermatFLT.FermatLittle;   "FL=$LASTEXITCODE"
lake build FermatFLT.WilesBridge;    "WB=$LASTEXITCODE"
lake build FermatFLT.Assembly;       "ASM=$LASTEXITCODE"
```

## 2. sorry / admit / fail grep — ✅ 干净

- `^\s*(sorry|admit)` 于 FermatFLT/ 下：**无任何真实代码行命中**。
- 全文 `sorry|admit` 的命中全部在注释或 .py/.log 里：
  - Assembly.lean:26（doc：`no sorry anywhere`）
  - FLT4.lean:10、34（文件头注释）
  - WilesBridge.lean:14（文件头注释）
  - notes/probes/stdout_probe1.log:39（英文单词 admit）
- `fail ` 于 .lean 文件仅 Foundations.lean:25 注释 `n = 1, 2 fail`。
- 无 `fail_if` 战术误用。

## 3. axiom 面 — ✅ 恰好 3 条，全在 WilesBridge

全包 `^\s*axiom` 命中仅：

- `WilesBridge.lean:365  axiom IsModular (E : WeierstrassCurve ℚ) : Prop`
- `WilesBridge.lean:374  axiom axRibetFrey (p : ℕ) (a b c : ℤ) ...`
- `WilesBridge.lean:387  axiom axWilesFrey (p : ℕ) (a b c : ℤ) ...`

完整签名（源码第 374–391 行）：

```lean
axiom axRibetFrey (p : ℕ) (a b c : ℤ)
    (hrel : a ^ p + b ^ p = c ^ p) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hpr : Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd b c = 1)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ¬ IsModular (freyOf p a b c hrel)

axiom axWilesFrey (p : ℕ) (a b c : ℤ)
    (hrel : a ^ p + b ^ p = c ^ p) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hpr : Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd b c = 1)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    IsModular (freyOf p a b c hrel)
```

- ✅ 两条公理都含 primitive（`hpr` 两两 gcd = 1）与 p 素 + `5 ≤ p`。
- ✅ `IsModular` doc（355–364 行）：明确 uninterpreted 原语、半稳定表述、指向
  Ribet 1990 / Wiles–Taylor 1995。
- ✅ axRibetFrey doc：`Invent. Math. 100 (1990) 431–477, DOI 10.1007/BF01231195`，
  并注明半稳定输入 = `freyDisc_even_valuations`（§2）。
- ✅ axWilesFrey doc：`Ann. of Math. 141 (1995) 443–577` + `Taylor–Wiles
  Ann. of Math. 141 (1995) 557–584`（页/卷核对有异议，见第 6 项）。
- 但见第 1 项：这些公理目前尚未进入编译产物（Assembly 红，`fermatLastTheorem`
  无可枚举对象），`#print axioms` 面要等收口。

## 4. namespace 与 import 边界

- namespace FermatFLT 各模块：
  - `Assembly.lean:56` ✓、`FermatLittle.lean:29` ✓、`FLT4.lean:39` ✓、
    `WilesBridge.lean:22` ✓
  - **Foundations.lean：无 `namespace FermatFLT`** ⚠（全文仅 `open Nat Int`）。
    其 `FLT` / `IsPrimitive` / `notFLT_one` / `notFLT_two` / `FLT.mono` /
    `FLT.of_four_and_odd_primes` / `FLT_primitive` 全部落在 **root 命名空间**，
    靠名字解析被其他模块引用（可编译，但违反"全定理在 FermatFLT 命名空间"的
    第 4 条架构约束）。伞文件 FermatFLT.lean 自身只有 5 行 import，无常量。
- `import Mathlib.NumberTheory.FLT.Basic` / `FLT.Three`：仅出现在
  Assembly.lean:1–2 ✓
- `import Mathlib.NumberTheory.FLT.Four`（及 `FLT.Four` 字符串）：全工作区
  （含 .lake 下 mathlib 自身外部引用除外，包内）零命中 ✓

## 5. `#print axioms` 顶层公理面 — 待主线构建完成后跑

探针已备好：`.yan/notes/axcheck.lean`（本次审计新增，内容为 `import FermatFLT` +
8 条 `#print axioms FermatFLT.{axRibetFrey,axWilesFrey,IsModular,freyContradiction,
fermatLastTheoremThree,fermatFourth,FLT.of_four_and_odd_primes,fermatLastTheorem}`）。
初次运行证实模块解析可用（`import FermatFLT` 能解析，只报 unknown constant——因
Assembly.olean 尚未产出）。

**待复跑命令**：

```powershell
lake build                                  # 等主线收口后
lake env lean .yan/notes/axcheck.lean       # 读全部 #print axioms 输出
```

预期清单分组（收口后核对）：
- package 公理：仅 `axRibetFrey`、`axWilesFrey`（`IsModular` 是 axiom，但对
  `fermatLastTheorem` 而言只是"谓词载体"，本身会被 `#print axioms` 列在
  IsModular 自己名下；两条 frey 公理会把自身列在 freyContradiction /
  fermatLastTheorem 名下）。
- mathlib/系统传递公理：来自 mathlib `fermatLastTheoremThree`（p=3 分支）与
  core/prelude 的既有集合（如 `Classical.choice` 系、`Nat`/`Int` 等标准库公理），
  复跑后原样列出。

## 6. 文献比对（代码注释 vs .yan/lit_check.md）— ⚠ 3 处出入

| 位置 | 代码注释 | lit_check.md | 判定 |
|---|---|---|---|
| Ribet 出处页，WilesBridge:370 与 Assembly:36 | Invent. Math. **100** (1990) **431–477**，DOI 10.1007/BF01231195 | #5 核验通过：100 (1990) no.2 **431–476**，同 DOI | ⚠ 末页相差 1（代码 477 / lit_check 476）。任务书预期 431–477，代码与任务书一致；实际文献惯用 431–477，lit_check 记的 476 疑为转录误差。作者/年/卷/DOI 三处均一致。 |
| Wiles 出处页，WilesBridge:384 与 Assembly:37 | Ann. of Math. **141** (1995) **443–577** | #3：443–**578**（泛用引法，未直接核验原文） | ⚠ 末页相差 1（代码 577 / lit_check 与广泛引法 578）。另任务书两处自相矛盾：账本正文写 443–578，本审计任务预期写 443–577——代码与后者一致、与前者相悖。实际论文即 443–578。 |
| Taylor–Wiles 出处，WilesBridge:385 与 Assembly:38 | Taylor–Wiles **Ann. of Math. 141** (1995) **557–584** | #4：T–W 修补文 = **Invent. Math. 121** (3) 1995 **575–629** | ⚠ 期刊/卷/页整体不一致。按 lit_check 与公认书目事实，T–W 的 ring-theoretic 修补文在 Invent. Math. 121:575–629；"Ann. of Math. 141: 557–584"在卷 141 内容上落在 Wiles 正文（443–578）的中后段，卷 141 并无 T–W 署名条目。此条比前两条严重，属期刊引用错误。 |

一致项：
- Assembly:15 "Brasca, Gupta, Haddad, Lowry-Duda, Luccioli, Monticone, Saurin,
  Schaffhauser, 2024" 与 mathlib 源头
  `.lake/packages/mathlib/Mathlib/NumberTheory/FLT/Three.lean:2–5` copyright
  头逐字相符 ✓
- Ribet 公理 doc 文中论文标题 "Frey's Modular Curves and the Consequence of
  Semistability" 与 lit_check 记录的正式题名 "On modular representations of
  Gal(ℚ̄/ℚ) arising from modular forms" 不符 ⚠（额外的第 4 处小出入；正文引用
  的是内容概括句而非题名，不影响 DOI 定位）。
- Euler 1753（FLT4 注解）、Euler 1736（FermatLittle 头）为史实标注，lit_check
  未覆盖，无法比对该文件。

## 7. 本报告

即 `.yan/notes/audit_report.md`（本文件）。探针 `.yan/notes/axcheck.lean` 一并保留
供复跑使用。

---

## 附：复跑清单（主线 `lake build` 收口后）

1. 第 1 节 6 条 `lake build` 命令，逐模块记退出码；
2. `lake env lean .yan/notes/axcheck.lean`，按第 5 节两组分类整理
   `#print axioms` 输出；
3. 若 Assembly 收口版本变化，更新第 1 节与第 3 节"编译产物"状态；
4. 将复跑结果追加到本报告"第 8 节 复跑补记"，改总判定行。
