# independent verification of the Kummer table logic (temp, delete after)
import collections
for p in [3, 5, 7, 11, 13, 17]:
    mp = p ** 4
    root_any = set()
    root_unit = set()
    for c in range(mp):
        v = pow(c, p, mp)
        root_any.add(v)
        if c % p:
            root_unit.add(v)
    U = [x for x in range(mp) if x % p]
    H = [pow(x, p, mp) for x in U]
    setH = set(H)
    CZ = sum(1 for a in H if (-a) % mp in setH)
    Cex = Cun = 0
    any_ex = unit_ex = None
    if p <= 11:
        dist = collections.Counter((a + b) % mp for a in H for b in H)
        for S, n in dist.items():
            if S in root_any:
                Cex += n
                if any_ex is None and S != 0:
                    any_ex = (S, p)
            if S in root_unit:
                Cun += n
                if unit_ex is None:
                    c = next(c for c in range(mp) if pow(c, p, mp) == S and c % p)
                    unit_ex = (S, c, p)
    else:
        import numpy as np
        hU = np.array(H, dtype=np.uint64)
        arr_any = np.zeros(mp, dtype=bool)
        arr_uni = np.zeros(mp, dtype=bool)
        arr_any[list(root_any)] = True
        arr_uni[list(root_unit)] = True
        for i0 in range(0, len(H), 1024):
            A = hU[i0:i0 + 1024]
            S = (A[:, None] + hU[None, :]) % mp
            Cex += int(arr_any[S].sum())
            Cun += int(arr_uni[S].sum())
    print(f"p={p}: mp={mp}  pairs={len(U) ** 2:,}  CZ={CZ:,}  Cex={Cex:,}  Cun={Cun:,}  "
          f"any_nonzero_example={any_ex}  unit_example(S,c)={unit_ex}")
    if p in (3, 5):
        nz = sorted((s for s in root_any if s != 0))
        print(f"   nonzero pth-powers in Z/{p}^4Z (first 8): {nz[:8]}  (count {len(nz)})")
