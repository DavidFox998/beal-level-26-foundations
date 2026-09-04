# M3 matrix from your v9.1.0 EKG canvas — this is the hard one
# This generates the cert Beacon needs to stop complaining about bug #220
N=26
M = ModularSymbols(N, 2, 1).cuspidal_subspace().new_subspace()
print(M.dimension())  # should be 2
# Formal immersion at p=2 check — Mazur method
X = J0(N)
print(f"J0({N}) decomposition for immersion: {X.decomposition()}")
# Save q-expansions for the two newforms 26a and 26b
for f in Newforms(N, names='a'):
    print(f, f.qexp(20))
