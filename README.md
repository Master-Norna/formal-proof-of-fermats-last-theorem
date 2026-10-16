# Formal Proof of Fermat's Last Theorem

一次基于 **qwen3.8:27B** 自主、独立推进 **35 小时** 的实验：尝试使用 Lean 4 和 mathlib 形式化证明费马大定理。

**目前尚未完成完整证明。核心的 `p ≥ 5` 部分仍依赖两条未经本项目证明的公理。**

## 已完成

- `n = 4` 情形的无限下降证明移植。
- `n = 3` 情形与 mathlib 已有证明的桥接。
- 一般 `n ≥ 3` 到 `n = 4` 和奇素数指数情形的归约。
- 反例到原始解的互素约化。
- Frey 曲线的构造，以及判别式、非退化性等基础性质的验证。

另包含费马小定理的形式化证明。

## 尚未完成

`FermatFLT/WilesBridge.lean` 中的两条核心公理承担了 `p ≥ 5` 情形的关键结论：

- `axRibetFrey`：假设原始反例对应的 Frey 曲线非模。
- `axWilesFrey`：假设同一条 Frey 曲线是模的。

二者导出矛盾，从而完成顶层命题的拼接，但其证明本体尚未形式化。此外，`IsModular` 也以 `axiom` 声明，目前只是没有具体定义的模性谓词占位。因此，源码中共有三条 `axiom` 声明：一个谓词占位和两条数学假设。

顶层定理 `FermatFLT.fermatLastTheorem` 的构建通过，仅表示 Lean 检查了这些假设下的推导，不能视为已经完成费马大定理的完整形式化证明。这里的模性、降阶等深层理论仍待实现。

## 构建与公理检查

工具链：Lean `4.34.1`；依赖：mathlib `v4.34.1`。版本由 `lean-toolchain` 和 `lake-manifest.json` 固定。

安装 elan 并进入项目目录后运行：

```sh
lake exe cache get
lake build
lake env lean FermatFLT/Check.ax.lean
```

最后一条命令输出主要定理的类型及公理依赖，包括顶层定理的 `#print axioms` 结果。

## 主要文件

| 文件 | 内容 |
| --- | --- |
| `FermatFLT/Foundations.lean` | 定义与一般指数归约 |
| `FermatFLT/FLT4.lean` | `n = 4` 无限下降 |
| `FermatFLT/FermatLittle.lean` | 费马小定理 |
| `FermatFLT/WilesBridge.lean` | 原始解互素约化、Frey 曲线与公理接口 |
| `FermatFLT/Assembly.lean` | `n = 3` 桥接与顶层定理拼接 |
| `FermatFLT/Check.ax.lean` | 定理类型与公理依赖检查 |

仓库保留实验过程中的笔记和探查记录；这些历史材料中的结论以当前源码和实际公理检查结果为准。
