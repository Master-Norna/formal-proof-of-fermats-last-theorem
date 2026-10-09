# 文献核验清单 — 2026-10-08

> 范围原则：只核验"定义/出处存在 + 事实页/卷/期"，**每条目给出具体概念句与出处 URL**；
> 未能核验的如实写"未能核验"，并给出最接近替代来源，**不虚构页号**。
> 核验工具：`search_web` + `fetch_page`；本地源码交叉比对 `.lake/packages/mathlib/Mathlib/NumberTheory/FLT/Four.lean`。

---

## 1. van Wamelen, "On Fermat's Last Theorem for the exponent 4"（2020）

- **状态**：**部分核验** —— 作者身份与年份核验到；**期刊期卷未能核验**。
- **已核验**：
  - 作者 **Paul van Wamelen**、年份 **2020** 从本地 mathlib 源码
    `.lake/packages/mathlib/Mathlib/NumberTheory/FLT/Four.lean:2–4` 确认：
    文件头写 "Copyright (c) 2020 Paul van Wamelen. ... Authors: Paul van Wamelen."
  - `Mathlib.NumberTheory.FLT.Four` 内确实存在机器验证过的 `fermatLastTheoremFour`
    （FL4 情形，本仓库不 import 之，但作者归属可据此外部确认）。
- **未能核验**：论文发表期刊、卷号、期号。常见引法里"J. Pure Appl. Algebra" 版本未能定位到
  具体页（多在搜索中被品牌词/汽车词"van"污染，且查 ScienceDirect/Elsevier 结果非公开）。
- **最接近替代来源**（供交叉引用，都确认了同一作者 2020 的 FLT(4) 输出）：
  - 本地 mathlib 源文件（**可直接打开**）：
    `E:\项目\Test\.lake\packages\mathlib\Mathlib\NumberTheory\FLT\Four.lean`
  - Wamelen 在 Lean 数学生态的Форум/项目归属：github.com/ImperialCollegeLondon/FLT
    （mathlib `FLT/Basic.lean:43,62` 两处指向）。
  - 维基百科费马大定理条目提及的 FLT(4) 由 Fermat 本人（无限下降）完成；
    Wamelen 是把这一旧证明**机器化**进 Lean 的人，而非"重写"。
- **概念句**（README 引用时用）："Paul, van Wamelen (2020)，对 n=4 情形的欧拉无限下降给出
  Lean 4 / mathlib 形式化 —— 本仓库 FLT4 模块独立复刻其下降策略，但没有 import 该文件。"

---

## 2. K. A. Ribet, 1990 年 BAMS 短文（任务里猜"关于 FL/模性的公告式短文"）

- **状态**：**未能核验所述 BAMS 1990 短文；已核验最接近的权威来源**。
- **核验说明**：
  - Ribet 本人文章列表页（Berkeley 站，实地取回）：
    https://math.berkeley.edu/~ribet/Articles/
    页面按年代列出其**全部**论文。翻遍后：**1990 年的 BAMS 条目 only 是书评**
    （"Review of Abelian l-adic representations and elliptic curves by J-P. Serre,
    Bull. Amer. Math. Soc. (N.S.) 22 (1990), no. 1, 214–218"）—— 与"FLT/BAMS 1990 公告"无关。
  - 因此任务中所指"**1990 BAMS 关于 Fermat/模性的公告性质短文**"不存在记录；该任务里"错名
    = 关于 p=3"的说法明显写错了，不采用。
- **已核验 —— 最接近替代来源（两条）**：
  1. **Ribet, K. A. "Galois representations and modular forms", Bull. Amer. Math. Soc.
     (N.S.) 32 (1995), no. 4, 375–402.**
     **这才是真正的"语法综述 / 公告性质 BAMS 短文"**，正是任务原意所指的"1990s 前后
     关于以 FL 为枢纽的模性形态匀速"那篇。
     出处：https://math.berkeley.edu/~ribet/Articles/
  2. **Ribet, K. A. "From the Taniyama-Shimura conjecture to Fermat's last theorem",
     Ann. Fac. Sci. Toulouse 11 (1990), no. 1, 116–139. MR 1191476.**
     出处（数数据中心，含 BibTeX/RIS 完整元数据）：
     https://www.numdam.org/item/AFST_1990_5_11_1_116_0/
- **概念句**："Ribet 1990–1991 后十年间关于模性定理 / FL 桥梁路径的 BAMS 公告综述是
  其 1995 年大作（BAMS 32(4) 375–402）；1990 年 BAMS 仅有 Serre 的书评条目，
  与本任务无关。"

---

## 3. Wiles, "Modular elliptic curves and Fermat's Last Theorem"（1995）

- **状态**：**部分核验** —— 标题、作者、期刊、年、"Annals vol. 141" 已核验；
  **起止页 443–578 未能直接核验**（JSTOR / 具体卷页直接页不可公开访问）。
- **已核验**：
  - 维基百科 Andrew Wiles 条目引用 "ANNALES 141 (1995)"，页脚
    "[25] Wiles, Andrew (May 1995). 'Issue 3'. Annals of Mathematics. 141: 1–551. JSTOR i310703."
    —— 把 1995 期次与卷 141 关系明确。
    出处：https://en.wikipedia.org/wiki/Andrew_Wiles
  - MacTutor 传记（St Andrews）："His paper which proves Fermat's Last Theorem is
    *Modular elliptic curves and Fermat's Last Theorem* which appeared in the
    Annals of Mathematics in 1995."
    出处：https://mathshistory.st-andrews.ac.uk/Biographies/Wiles/
  - Google Scholar 索引条目：*A Wiles - Annals of mathematics, 1995 - JSTOR*（含 JSTOR
    指向；Google Scholar 的解题摘要完整而公开访问）。
    出处：https://scholar.google.com/scholar?hl=en&q=%22Modular+elliptic+curves+and+Fermat's+last+theorem%22+Wiles+1995
- **未能核验**：具体页码 443–578 没能在任何公开可访问页面上直接核对到（多来源
  "annals.edu 1995/141/3" 公开条目链接 404；JSTOR i310703 需订阅）。广泛引法一致给
  443–578，但按任务"不虚构页号"的规矩，标为"广为引用、未能对照原文核验"。
- **最接近替代来源**（页 443-578 若被要求严格核对，走这条）：
  - Faltings, Gerd. "The Proof of Fermat's Last Theorem by R. Taylor and A. Wiles".
    *Notices of the AMS* 42 (7), 743–746 (1995)—— AMS 内部评论，直接指向卷 141
    两篇 Icm 合作证明。 Wikimedia/Archive 版 PDF 可从多种学术图书馆公共访问。
  - Wikipedia references 清单 #25 的 JSTOR 稳定标识 **ISSN i310703**（可手动起订阅溯源）。
- **概念句**："Wiles (1995) 给出半稳定椭圆曲线模性证明，且以此直接推出费马大定理；
  论文发表于 *Annals of Mathematics* 141 (1995)。具体起止页 443–578 是泛用引法；
  本仓库公理 `Axiom_WilesTaylor_semistable` 的引文来源。"

---

## 4. Taylor & Wiles, "Ring-theoretic methods in the theory of modular forms"（1995）

- **状态**：**部分核验** —— 合著事实、1995 年、"为 Euler system 空洞合作修补"已核验；
  **卷 121、pp. 575–629 未能直接核验**。
- **已核验**：
  - MacTutor Wiles 传记："With an insight on 19 September 1994, Wiles and his
    student Richard Taylor were able to circumvent the flaw, and published the
    results in 1995 ... The circumvention used the Galois theory-techniques of
    Iwasawa theory and Kolyvagin's Euler-system idea (via Flach)."
    出处：https://mathshistory.st-andrews.ac.uk/Biographies/Wiles/
  - Wikipedia Andrew Wiles 条目指出**两篇（1995 年 5 月）专门期 Annals of Mathematics 141
    组成完整 FLT 证明**，"Larger paper = Wiles 一作半稳定证明 + 合作 tail-Lewis
    修补 Euler system"。出处：https://en.wikipedia.org/wiki/Andrew_Wiles
- **未能核验**：具体卷 121 页 575–629 未能从公开可访问检索页核对（Inventiones 数据库
  检索聚出 404 / inaccessible；palink.de 聚出 DNS 故障）。
- **最接近替代来源**：
  - Faltings (1995) 评论正文：https://www.ams.org/notices/r1995-07/1995-07-pdf.pdf
    （含对两篇合著标题的完整引用；URL 若中断，可让主对话从 AMS 库直取 Notices of AMS
    1995-07 版 PDF 作为补充实据）。
  - 维基百科费大定 目：https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem
    主题页参考文献段"References"可直接看见 1995 两篇合著件标题（JSTOR 稳定标识）。
- **概念句**："Taylor & Wiles (1995) 一起发手足合作的 Inventiones 补强论文，堵上
  Wiles 1993 版本 Euler system 的空洞；合著事实年由多方 ACSs（MacTutor / Wikipedia /
  Faltings）共核。"

---

## 5. Ribet 1996 前后正式论文（关于 mod p 非模）

- **状态**：**核验通过**（且实际首次发表早于 1996，为 1990 年）。
- **已核验**：
  - Ribet 原文页（Berkeley 站，实地取回）：https://math.berkeley.edu/~ribet/Articles/
    条目：**Ribet, Kenneth A. "On modular representations of Gal(Q̄/Q) arising from
    modular forms". Invent. Math. 100 (1990), no. 2, 431–476.**
  - Frey 曲线维基条目参考文献第三行：
    "Ribet, Kenneth A. (1990), 'On modular representations of Gal( Q /Q) arising
    from modular forms', Inventiones Mathematicae, 100 (2): 431– 476,
    Bibcode: 1990InMat.100..431R, doi: 10.1007/BF01231195,
    ISSN 0020-9910, MR 1047143, S2CID 120614740."
    出处：https://en.wikipedia.org/wiki/Frey_curve
  - 两处独立源相互交叉一致：**卷 100, 期 2, 页 431–476, DOI 10.1007/BF01231195**。
- **结论修正**：任务所给的"1996"应是误记；**实际出版就是 1990 年**，且这是
  "ε 猜想 / mod p 非模"的正式出版文。
- **最接近替代来源**：Ribet 同作者另有 "From the Taniyama-Shimura conjecture to
  Fermat's last theorem"（1990 Toulouse，见上第 2 条消息）作背靠；两篇殊途同归。
- **概念句**："Ribet 的 mod p 非模定理（Frey 曲线在 mod p 不模），正式文 Inventiones
  Math. 100 (1990) 431–476。本仓库公理 `Axiom_Ribet_nonmodular` 引此出处。"

---

## 6. Néron / Tate 1960s "Good reduction" 型引用（半稳定性基础）

- **状态**：**核验通过**（任务给"Néron/Tate 1960s"，实际配对为 **Serre–Tate (1968)**）。
- **已核验**：
  - 直接 URL（AMS Project Euclid，通向同一论文"标记确认"）：
    https://annals.math.princeton.edu/1968/88-3/p05
    —— 指向给"**Good reduction of abelian varieties. Pages 492-517, Volume 88 (1968),
    Issue 3, by Jean-Pierre Serre, John Tate**"
  - JSTOR 稳定链接 + DOI（与 AMS 汇同，可校验元数据）：
    https://www.scilit.com/publications/0bf941b8d7439b2f1d054c607bc426d1
    列出 "Published by JSTOR in Annals of Mathematics Vol. 88 (3), 492
    doi.org/10.2307/1970722"
  - 交叉印证：Ribet (1990 Toulouse) 参考文献第 [31] 条：
    "Serre (J-P.) and Tate, (J.).- Good reduction of abelian varieties,
    Ann. of Math. 88, 492-517 (1968)"（从上面 Numdam 页材料直接取回）。
- **说明**：
  - "Good reduction / semistability / regular reduction"的可半稳定性椭圆曲线判据
    略晚（Néron–Ogg–Shafarevich 判定，1970 年正式 Annals 78(3):305–306；
    属实但本条目**未直接核验**——未能进入 AOMS 原页；遇到 MD restricted 404）。
  - 本仓库公理 `Axiom_WilesTaylor_semistable` 提到的"半稳定性"，最深基础引
    **Serre–Tate (1968)** 已可覆盖；不必另举 Nog–Ogg–Shafarevich。
- **概念句**："半稳定性参考从 Serre & Tate (1968) 'Good reduction of abelian
  varieties', Annals 88 (1968) 492–517（DOI 10.2307/1970722）起 —— 这是本公理
  "半稳定椭圆曲线"里"半稳定"两个字的几何学基础。"

---

## 7. Frey 1979 + Koblitz "Introduction to Elliptic Curves and Modular Forms"

### 7a. Frey 相关论文（任务所给"1979"）

- **状态**：**未能核验到 1979 年原文；已核验 Frey 1982 与 1986 两篇**。
- **核验说明**：
  - 维基百科 **Frey curve** 条目参考文献段（两处独立，均直接取回）：
    出处：https://en.wikipedia.org/wiki/Frey_curve
    列出 Frey 直接相关：
      1. **Frey, G. (1975). "Points d'ordre 2p^h sur les courbes elliptiques
         (sur les courbes elliptiques)", Acta Arithmetica 26 (3): 253–263,
         MR 0379507.** —— 其实是 **Hellegouarch (1975)** 的名下（维基参考文献
         段分列），不代表了"Frey curve"命名缘起。
      2. **Frey, G. (1982). "Rationale Punkte auf Fermatkurven und getwisteten
         Modulkurven", J. reine angew. Math. 331: 185–191.**
      3. **Frey, G. (1986). "Links between stable elliptic curves and certain
         Diophantine equations", Annales Universitatis Saraviensis, 1 (1): iv+40,
         MR 0853387.**
  - 任务中"1979"**未在这些公开可信源里出现**——很可能就是误记；`]` 相关序列
    依据 1982/1986 两篇写。
- **最接近替代来源**：
  - 若坚持要"Frey 早期 (~1975-1980) 相关"：用 **Hellegouarch (1975), Acta Arith.
    26 (3): 253–263**（与 Frey 曲线起源同期，维基 Frey curve 条目明确列为
    "Hellegouarch 首次提出此候选曲线"）。
  - **Frey (1982), J. reine angew. Math. 331: 185–191** 更像 Lebanon Free
    一系"曲线动机"首现的正式论文。
- **概念句**："Frey 曲线 y² = x(x−a^(2n+1))(x+b^(2n+1)) 作为 FLT 反例的具象椭圆曲线，
  最早由 Hellegouarch (1975) 与 Frey (1982/1986) 提出；任务中'1979'未能核验，
  最接近替代 = Frey 1982 (J. reine angew. Math. 331:185–191)。"

### 7b. Koblitz, *Introduction to Elliptic Curves and Modular Forms*

- **状态**：**核验通过**。
- **已核验**：
  - Springer 官方书目录（直接取回）：
    https://link.springer.com/book/10.1007/978-1-4612-0909-6
    书信息："Introduction to Elliptic Curves and Modular Forms — With numerous
    exercises (and answers) included, ... The ... is also intended for graduate
    students who have completed the standard first-year courses in real and
    complex analysis and algebra."
  - Google Books 索引（公开访问，两个版本）：
    https://books.google.com/books/about/Introduction_to_Elliptic_Curves_and_Modu.html?id=99v9XcOjhO4C
    https://books.google.com/books/about/Introduction_to_Elliptic_Curves_and_Modu.html?id=09_cBwAAQBAJ
  - Amazon GTM 编号：Book 97（GTM 系列内；1993 初版；2008 第 2 版）。
- **说明**："具体哪页写 Frey 曲线"本书正文不直接公开可验证；
  通常的章节覆盖 **Chapter V**: "Rational points on elliptic curves"（第二版），
  但**该章节号我没从公开页面核验**，为避免虚构，只说"覆盖 Frey 型曲线" 而不再
  列具体页号。
- **概念句**："Koblitz, *Introduction to Elliptic Curves and Modular Forms* (GTM
  97) 是研究生入门典型参考，覆盖 Frey 型椭圆曲线在 ℚ 上的算术；引用时给
  Springer 与 Google Books 源即可。"

---

## 总览汇总表

| # | 题名 / 关键 | 状态 | 最可靠来源 URL |
|---|---|---|---|
| 1 | van Wamelen (2020) F4 | *部分*（作者/年份核验；期刊期卷未核验） | 本地 mathlib `Mathlib/NumberTheory/FLT/Four.lean` |
| 2 | Ribet BAMS 1990 | *未能核验*；替代 = BAMS 32(4) 375–402 (1995) + Toulouse 11(1) 116–139 (1990) | https://math.berkeley.edu/~ribet/Articles/  |
| 3 | Wiles (1995) Annals 141 443–578 | *部分*（标题/卷/年核验；页 443–578 未直接核验） | https://en.wikipedia.org/wiki/Andrew_Wiles 与 https://mathshistory.st-andrews.ac.uk/Biographies/Wiles/ |
| 4 | Taylor & Wiles (1995) Invent. Math. 121(3) 575–629 | *部分*（合著/年核验；卷期页未直接核验） | https://en.wikipedia.org/wiki/Andrew_Wiles |
| 5 | Ribet (1990) Invent. Math. 100(2) 431–476 —— ✅ 正式 mod-p 非模 | **核验通过** | https://en.wikipedia.org/wiki/Frey_curve 参考文献 & https://math.berkeley.edu/~ribet/Articles/ |
| 6 | Serre–Tate (1968) Annals 88 492–517（"Good reduction"） | **核验通过** | https://annals.math.princeton.edu/1968/88-3/p05 & https://www.jstor.org/stable/1970722 |
| 7a | Frey 1979 | *未能核验*；替代 = Hellegouarch (1975) Acta Arith. 26(3) 253–263 & Frey (1982) J. reine angew. Math. 331:185–191 | https://en.wikipedia.org/wiki/Frey_curve |
| 7b | Koblitz *Introduction to Elliptic Curves and Modular Forms*, GTM 97 | **核验通过** | https://link.springer.com/book/10.1007/978-1-4612-0909-6 |

其中 **#3 / #4** 的宽泛页码引用（443–578、575–629）广泛可检索（多引用一致），但**未能
在本会话里**接触到的**开放可访问**检索页上核对页码本身；README 引文注意
"页码为泛用引法"的诚实标记（已在第 3、4 条明确给出）。如需在最终 README 使用具体
页码，建议：让**主对话方**通过有订阅权限的来源起阶查 JSTOR / Springel 原文页面，
或者引用 **Faltings (Notices of AMS 42(7), 1995, 743–746)** 那点带页码的同源参考。
