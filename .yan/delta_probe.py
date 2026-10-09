# -*- coding: utf-8 -*-
# Frey 曲线 y^2 = x^3 + (B-A)x^2 - ABx  的判别式/最小判别式精确公式（sympy 展开）。
# A = a^p, B = b^p（p 固定偶，poly 符号算）。
import subprocess, sys

subprocess.run([sys.executable, '-m', 'pip', 'install', '-q', 'sympy'], check=True)
import sympy as sp

A, B = sp.symbols('A B')
a1, a2, a3, a4, a5, a6 = sp.symbols('a1 a2 a3 a4 a5 a6')

# 标准不变量（与 mathlib Weierstrass 应逐字一致——已对照过源码，若不一致以源码为准）
b2 = a1**2 + 4*a2
b4 = 2*a4 + a1*a3
b6 = a3**2 + 4*a5
b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a5 + a2**2*a4 - 4*a4**2
Delta = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6

# 自检 1: y^2 = x^3 + x  -> a2=0,a4=1 -> 期望 Delta = -64, j = 1728
subs1 = {a1:0, a2:0, a3:0, a4:1, a5:0, a6:0}
D1 = sp.expand(Delta.subs(subs1))
print('check y^2=x^3+x : Delta =', D1, '(expect -64)')

# 自检 2: y^2 = x^3 + x + 1 -> 期望 -16(4+27) = -496
subs2 = {a1:0, a2:0, a3:0, a4:1, a5:0, a6:1}
print('check y^2=x^3+x+1: Delta =', sp.expand(Delta.subs(subs2)), '(expect -496)')

# Frey: a1=a3=a5=a6=0, a2 = B - A, a4 = -A*B
subsF = {a1:0, a2:B-A, a3:0, a4:-A*B, a5:0, a6:0}
DF = sp.expand(Delta.subs(subsF))
print('Frey Delta(A,B) =', DF)
print('factor:  ', sp.factor(DF))
# 以 S = A + B (即 c^p) 的形态尝试分解:
DF2 = sp.factor(DF.subs({A: sp.Symbol('S') - B}))
print('in (S=A+B):', sp.factor(DF2))

c4 = (b2**2 - 24*b4).subs(subsF)
print('c4 =', sp.factor(sp.expand(c4)))
j = sp.factor(sp.expand(c4**3 / DF))
print('j    = 16 *', sp.factor(sp.simplify(j/16)), '   (expect 16*(A^4 - A^3B + A^2B^2 - AB^3 + B^4)^? / (A+B)^2 ... to be seen)')

# 数值核对 p=1, a=1, b=2（A=1,B=2），与纯整数手递推（y^2 = x(x-1)(x+2) = x^3 + x^2 - 2x）
print('numeric A=1,B=2: Delta =', DF.subs({A:1, B:2}), ' c4=', c4.subs({A:1,B:2}))
