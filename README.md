# 费马大定理 · Lean 4 形式化

把 **FLT（n ≥ 3）** 逐行机器核验：不是复述人类证明，而是让 Lean kernel
一道一道检查本仓库里的推理。按真实人类路线分三段——
**Euler 1753（n=4 无限下降）· Euler–Kummer 1775（n=3，ℤ[ζ₃] 下降）·
Wiles–Taylor–Ribet 1990/95（Frey 曲线 + 半稳定模性）**——
其中前两段与 Frey 桥的全部机械部分由本包自证，两段人类重定理按**公理登记**，
公理间的每一步推理全部机器核验。

```
fermatLastTheorem : ∀ n, 3 ≤ n → FLT n
  ← FLT.of_four_and_odd_primes
      ├ FLT 4 = fermatFourth          (本包自证，Euler 无限下降)
      └ 奇素数支 oddPrimeBranch:
          ├ p = 3 → flutter（FLT 3）  (已证明依赖：mathlib 机器证明的
          │                          Euler–Kummer ℤ[ζ₃] 无限下降)
          └ p ≥ 5 → Frey 矛盾          (本包自证桥 + 公理 ×2)
```

`FLT n`：不存在非零整数 `a b c` 使 `a^n + b^n = c^n`。

---

## 依赖分类（本工程的核心纪律）

三类依赖**全程分开标注**，结论只从这三类流出。

### 第一类 · 已证明的依赖（机器核验过的外部库）

产自 mathlib v4.34.1（本项目 `lake update` 钉住的版本；本机 `.lake/packages/
mathlib` 可逐字可读，随 lean-toolchain 一并载入验证）：

| 依赖 | 数学内容 | 尺度 | 出处 |
|---|---|---|---|
| `Mathlib.NumberTheory.FLT.fermatLastTheoremThree` | **FLT(3) 完整**：case 1（mod 9 初等）+ case 2（ℤ[ζ₃] 无穷下降） | 机器证明定理 | Brasca, Gupta, Haddad, Lowry-Duda, Luccioli, Monticone, Saurin, Schaffhauser, 2024（`Mathlib/NumberTheory/FLT/Three.lean`，772 行） |
| `fermatLastTheoremFor_iff_int` | ℤ 陈述 ↔ ℕ 陈述等价（桥梁） | 机器证明定理 | 同上 `Basic.lean` |
| `PythagoreanTriple.coprime_classification'` | 本素 Pythagorean 三元组参数化（FLT(4) 的骨架） | 机器证明 | `Mathlib/NumberTheory/PythagoreanTriples` |
| `IsCyclotomicExtension.Rat.Three.*` | ℤ[ζ₃] 环、λ=η−1 除尽系、Kummer 引理特例（案例只读路线图用） | 机器证明 | `Mathlib/NumberTheory/NumberField/Cyclotomic/Three` |
| `WeierstrassCurve` 不变量群 | b₂/b₄/b₆/b₈、Δ=0↔退化、1728Δ=c₄³−c₆²、j、twoTorsion 多项式 | 机器定义+引理 | `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass` |
| ZMod/Units、Int.GCD、factorization、Pow 算术群 | 初等算术 | 机器证明 | mathlib data/ringtheory |

**引用边界**：`import Mathlib.NumberTheory.FLT.Basic | Three` **只允许**出现在
`Assembly.lean`（p=3 支），且**严禁** `import …FLT.Four`（n=4 必须本包自证）。

### 第二类 · 本包自证（每行经 Lean kernel 核验，零 `sorry`）

| 模块 | 行数 | 内容 |
|---|---|---|
| `Foundations.lean` | 60 | `FLT`/`IsPrimitive` 定义、n=1,2 反例、单调性、**`of_four_and_odd_primes` 归约**（n≥3 ⟸ FLT 4 + 所有奇素数 p≥3，经 mathlib 的 `four_dvd_or_exists_odd_prime_…` 分解） |
| `FLT4.lean` | ~310 | **Euler 无限下降**：最小化解→奇偶归一→`coprime_classification'` 两连→`sq_of_gcd_eq_one` ×4→更小的 `j⁴+k⁴=i²` 解→矛盾。全程 Pythagorean×gcd 器械，无 FLT import |
| `FermatLittle.lean` | 145 | 费曼小定理自证四步：单位判据 → `card_units`+`pow_card_eq_one`（有限群元件的群阶次幂为 1）→ ℕ 形 → ℤ 形（ZMod 余元链） |
| `WilesBridge.lean` | ~427 | **Frey 桥**：§1 Frey 模型代数不变量（`Δ = 16·(s·t·(s+t))²` **完全平方**、c₄=16(s²+st+t²)、2-扭零点 {0,−s,t}）；§2 扁平估值形与 **`freyDisc_even_valuations`：Δ₀ 的每个素因子 v_q 都是偶数**（`Nat.factorization_pow` 逐点字），非退化→`IsElliptic`、j 不变量；§3 **自证的原始化解降格** `existsPrimitiveCounter`（|c| 最小化 + `pow_dvd_pow_iff` 三次链）；§5 公理登记 + **`freyContradiction`：p≥5 的一行矛盾 `hribet hwiles`** |
| `Assembly.lean` | ~115 | `flutter : FLT 3`（桥接已证依赖）、`oddPrimeBranch`（3/≥5 分支）、**`fermatLastTheorem : ∀ n, 3 ≤ n → FLT n`** |

### 第三类 · 暂假性依赖（axiom，人民出版社要承担的部分）

全包**恰好三**条 `axiom`（`FermatFLT/WilesBridge.lean` §5），可
`#print axioms FermatFLT.fermatLastTheorem` 枚举：

| 名称 | 陈述 | 人类出处（已核验书目） |
|---|---|---|
| `IsModular (E : WeierstrassCurve ℚ) : Prop` | uninterpreted 原语：E 在 ℚ 上"模"（ℓ-进伽罗华表示来自 Hecke 特征形式）——Lean 暂无关于模性的形式化机身可挂靠 | — |
| `axRibetFrey` | 素数 p≥5 的**原始解**反例的 Frey 曲线，**非模** | **Ribet**, *On modular representations of Gal(Q̄/Q) arising from modular forms*, **Invent. Math. 100 (1990), no. 2, 431–476**（DOI 10.1007/BF01231195，MR 1047143）——半稳定输入前半段，由本包 §2 的偶估值记录机器化 |
| `axWilesFrey` | 同上条件下的 Frey 曲线，**是模的** | **Wiles**, *Modular Elliptic Curves and Fermat's Last Theorem*, **Ann. of Math. (2) 141 (1995), no. 3, 443–551**（MR 1333035）；1993 年空档由 **Taylor–Wiles**, *Ring-theoretic Properties of Certain Hecke Algebras*, **Ann. of Math. (2) 141 (1995), no. 3, 553–572**（MR 1333036）填充 |

> 书目以 mathlib 自带 `docs/references.bib`（`Wiles-FLT`、`Taylor-Wiles-FLT` 条目）与
> `.yan/lit_check.md`（两轮独立来源交叉核验）为准；此前仓内 3 处页/志误已修正。

三条公理是**紧贴人类证明边界的 parenthetical 化**：mathe rubric 的 Ribet 降阶、
Wiles–Taylor 半稳定模性定理都是活着的数学工程（Imperial College 的
[FLT Lean 项目](https://github.com/ImperialCollegeLondon/FLT) 至今把它作为
未竟地形），本包把它们作为**已出版人类定理**登记，并把「命题 → 公理 → 命题」
全链做成 machine-checked。

---

## 复现

```powershell
# 工具链已捕：lean 4.34.1（lean-toolchain），依赖 mathlib v4.34.1（lake-manifest）
lake update                # 首挖：克隆 mathlib + 下载 olean 缓存（已做过）
lake build                 # 编全部目标（约数分钟，缓存时 <1 分钟）
```

逐目名构建：`lake build FermatFLT.Foundations` 等；顶层公理面：
`#print axioms FermatFLT.fermatLastTheorem`。

## 目录

```
FermatFLT.lean            # 伞文件：import 五模块
FermatFLT/Foundations.lean
FermatFLT/FLT4.lean
FermatFLT/FermatLittle.lean
FermatFLT/WilesBridge.lean
FermatFLT/Assembly.lean
.yan/账本.md              # 工程台账（工程决断/固化 API/坑录）
.yan/lit_check.md         # 文献核验清单（两轮交叉来源）
.yan/notes/audit_report.md# 终检报告（子代理，只读审计）
```

## 诚实边界（哪些**没有**变成机器检查）

- `axRibetFrey` / `axWilesFrey` 的**证明本体**（上 callable 的四篇论文）——
  人类证明，本仓只登记其精确 published 陈述。
- `IsModular` 的语义本身（uninterpreted）：一旦未来出现模性形式化机身，
  两条公理可以挂接其精确定义并重推内建。
- FLT(3) 使用 mathlib 的机器证明（Brasca 等 2024），本仓**没有**从零重写它
  （用户裁决：已证明的依赖不必复证——用户可在具体验证后改判）。
