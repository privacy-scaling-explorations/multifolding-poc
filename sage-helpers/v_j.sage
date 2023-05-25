# This file computes the v_j values in Sage, but instead of working
# with MLE & boolean hypercube, working directly on the matrices coordinates.

# BLS12-381 Fr:
F = GF(0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)

# R1CS matrices for: x^3 + x + 5 = y (example from article
# https://www.vitalik.ca/general/2016/12/10/qap.html )
A = matrix([
    [F(0), 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0],
    [0, 1, 0, 0, 1, 0],
    [5, 0, 0, 0, 0, 1],
    ])
B = matrix([
    [F(0), 1, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0],
    ])
C = matrix([
    [F(0), 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 0],
    ])
# CCS translation from the R1CS instance:
t=3; q=2; d=2; S1=[0,1];
S2=[2]; S = [S1, S2];
c0=1; c1=-1; c = [c0, c1]
M = [A, B, C]

# z vector
z = [F(1), 3, 35, 9, 27, 30]

print("A\n", A)
print("B\n", B)
print("C\n", C)
print("z\n", z)




acc = 0
def v_j(j, r):
    M_j = M[j] # get matrix M_j
    acc = F(0)
    for y in range(0, M_j.ncols()):
        acc += M_j[r][y] * z[y]
    return acc

# random r. In the rust implementation it would be an entry of the boolean
# hypercube, but here we work with matrix coordinates
r = 0

print("v_j:", v_j(0, r))
print("v_j:", v_j(1, r))
print("v_j:", v_j(2, r))

assert v_j(0, r) * v_j(1, r) == v_j(2, r)
