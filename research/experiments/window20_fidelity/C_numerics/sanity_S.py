import sys, time
from itertools import product
sys.path.insert(0, '.')
from paper_side import S_count

ref = {(2,2):8, (3,2):26, (5,2):182, (2,3):72, (3,3):6398, (6,2):801064}
bad = 0
for (n,d),val in ref.items():
    got = S_count(n,d,2)
    print(f"|S_{n}^{d}| (sigma=2) formula={got} ref={val} {'OK' if got==val else 'MISMATCH'}")
    bad += got != val

# definition-level brute force: s : (Z/n)^d -> Sigma is shift-symmetric iff some v != 0 has s(u+v)=s(u) for all u
def brute(n, d, sigma):
    cells = list(product(range(n), repeat=d))
    idx = {c:i for i,c in enumerate(cells)}
    perms = []
    for v in cells:
        if any(v):
            perms.append([idx[tuple((a+b) % n for a,b in zip(u,v))] for u in cells])
    cnt = 0
    for s in product(range(sigma), repeat=len(cells)):
        for pm in perms:
            if all(s[pm[i]] == s[i] for i in range(len(cells))):
                cnt += 1; break
    return cnt

t=time.time()
for (n,d,sg) in [(2,2,2),(3,2,2),(2,3,2),(4,2,2),(2,4,2),(6,1,2),(6,1,3),(12,1,2),(2,2,3),(3,2,3),(4,1,5),(10,1,2),(9,1,3),(6,2,1),(3,2,1)]:
    b = brute(n,d,sg); f = S_count(n,d,sg)
    print(f"brute n={n} d={d} sigma={sg}: brute={b} formula={f} {'OK' if b==f else 'MISMATCH'}")
    bad += b != f
print("mismatches:", bad, f"time {time.time()-t:.1f}s")
