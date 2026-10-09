# Wiles 路线 · 模块规划（2026-10-08，接棒稿）

## 环境事实
- Lean 4.34.1（leanprover--lean4 通道），mathlib v4.34.1（pinned），3092 模块，每文件 15s 级。
- lakefile.toml（Lake 5.0 风格）；mathlib import 全名可用。
- 现有模块：Foundations.lean（FLT 陈述/n=1,2/单调性）、FLT4.lean（自证 Euler 下降）、FermatLittle.lean（②核心通行中）。
- 硬约束：无 sorry/admit/fail；FLT 部分不引 Mathlib.NumberTheory.FLT.*；公理仅限 Wiles/Taylor-Wiles + Ribet 两条（各自带人类证明出处）。

## WilesBridge.lean 规划
1. Frey 曲线构造（ℚ 上 WeierstrassCurve）：
   - 由 (a,b,c,p)（a^p+b^p=c^p, primitive, p 奇素数）构造
     标准 Wiles 参数化（E: y² = x(x - a^p)(x + b^p) 的 a₁..a₆ 系数）。
   - 配套计算（必须机器合成）：判别式、2-扭子群、j 不变量（用 c₄/Δ）。
2. 半稳定性公理（Ribet-Serre 标准）：E 在 ℚ 上半稳定。
3. Ribet 公理：半稳定 + 关键条件（如导子、p-torsion 等）→ 非模。
4. Wiles-Taylor 公理：所有半稳定椭圆曲线都模（半稳定模性 = 关键成品）。
5. 矛盾定理：假设 FLT 假（存在 primitive 反例）→ 构造 E（半稳定）→ 由 Ribet 非模 ∩ Wiles 全模 → 矛盾。
   即 frey_lift_to_contradiction :¬FLT p（p 奇素数）。

## Assembly.lean 规划
- 合缝：fermatLastTheorem = ∀ n ≥ 3, FLT n。
  已知 Foundations.of_four_and_odd_primes 需要 hfour : FLT 4 与 hop : ∀ p.Prime → Odd p → FLT p。
  · hfour := fermatFourth（自证）。
  · hop 由 frey_lift_to_contradiction 给出（对每个奇素数 p 单独给出 FLT p）。
- 最终陈述用 #print axioms 枚举恰好两条（Wiles-Taylor, Ribet）。

## 执行纪律（已核实的坑，不要再踩）
- 「非标 region / noncomputable / lemma / def / section 混排」会导致 Let: 位置错。
- Edit_file 需要 old 在文件里逐字唯一出现；改多段时分多步。
- 编译确认：先读当前文件再改；别叠补丁；每次 build 后读最新 error 再决定下一步。
- 公理计数：只有最终定理的 api 下才检查 axiom 引用（避免依赖链条混乱误查）。
- mmcid（mathlib）导数/桥梁要看 mathlib 源码确认名字（别猜）。
