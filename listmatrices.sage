import itertools

def iota( P ):
    r"""
    P - Point on elliptic curve E:y^2 = x^3 + x
    Function computes the image of P under iota: (x,y) |--> (-x,i*y)
    """
    E = P.curve()
    if P == E(0): return P;
    z = P.base_ring().gen()
    (x,y) = P.xy()
    return E([-x,z*y])
    
def frob( P ):
    r"""
    P - Point on elliptic curve
    Function computes the image of P under frobenius: (x,y) |--> (x^p,y^p)
    """
    E = P.curve()
    p = E.base_ring().characteristic()
    if P == E(0): return P
    (x,y) = P.xy()
    return E([x^p,y^p])
   
def FormExEellSubgroup( ell, EellBasis ):
    r"""
    ell       - Integer
    EellBasis - Tuple (P,Q) such that <P,Q> = E[ell] as a group
    Returns all subgroups of the form C_ell x C_ell. Subgroups
    generators are returned.
    """
    result = []
    for a in range(3):
        for b in range(a+1, 4):
            for var0 in itertools.product(range(ell), repeat=2-a):
                #print("0",var0)
                r0 = [0]*a + [1] + list(var0) + [0]
                r0[3] = r0[b]
                r0[b] = 0
                for var1 in itertools.product(range(ell), repeat=3-b):
                    r1 = [0]*b + [1] + list(var1)
                    result.append(tuple(tuple(r[o]*EellBasis[0]+r[o+1]*EellBasis[1] \
                                                for o in [0,2]) for r in [r0, r1]))
    return result

def PointCoefficients( X, ell, EellBasis ):
    r"""
    X - elliptic curve ell-torsion point 
    ell - integer and order of X divides ell
    EellBasis - basis of E[ell]
    Expresses elliptic curve point X as a linear combination
    of a given torsion basis EellBasis
    """
    P, Q = EellBasis
    epq = P.weil_pairing(Q, ell)
    return (X.weil_pairing(Q, ell).log(epq), -X.weil_pairing(P, ell).log(epq))

def ComputeKernelMatrix( Kgens, ell, EellBasis, O ):
    r"""
    Kgens     - A tuple ((A,B), (C,D)) that specifies a kernel of an isogeny
                (A,B) and (C,D) are in E x E
    ell       - an integer such that the kernel is isomorphic as a group to C_ell x C_ell
    EellBasis - A tuple (P,Q) such that <P,Q> = E[ell]
    O         - A quaternion order such that End(E) is isomorphic to it

    Given generators of a kernel, compute a matrix that corresponds to the kernel
    """
    E = EellBasis[0].curve()
    if Kgens[0][0].weil_pairing(Kgens[1][0], ell) != 1:
        # print("First case")
        return ComputeKernelMatrix_LeftCase(Kgens, ell, EellBasis, O)
    elif Kgens[0][1].weil_pairing(Kgens[1][1], ell) != 1:
        # print("Second case")
        M = ComputeKernelMatrix_LeftCase([(g[1],g[0]) for g in Kgens], ell, EellBasis, O)
        M.swap_columns(0,1)
        return M
    else:
        # print("Third case")
        # print(f"{Kgens[0]=} {Kgens[1]=}")
        A, B = Kgens[0]
        C, D = Kgens[1]
        a1,a2 = PointCoefficients( A, ell, EellBasis )
        b1,b2 = PointCoefficients( B, ell, EellBasis )
        c1,c2 = PointCoefficients( C, ell, EellBasis )
        d1,d2 = PointCoefficients( D, ell, EellBasis )
        Mac = Matrix(Integers(ell),2,2,[a1,c1,a2,c2])
        Mbd = Matrix(Integers(ell),2,2,[b1,d1,b2,d2])
        alpha, beta  = next(x for x in Mbd.right_kernel().basis() if Mac*x)
        gamma, delta = next(x for x in Mac.right_kernel().basis() if Mbd*x)
        P = alpha*A + beta*C
        Q = gamma*B + delta*D
        # print(f"{P=} {Q=}")
        b = O(0)
        num_tries = 0
        qb = O.basis()
        while EvaluateEnd(b,Q).weil_pairing(P,ell) == 1:
            num_tries += 1
            size = int(num_tries ** (2/3))
            b = sum(randint(0, size) * bq for bq in qb[0:2 + num_tries//8])
        gamma0 = Matrix(2,2,[1,b,0,1])
        gamma1 = ComputeKernelMatrix_LeftCase( [(P,E(0)), (EvaluateEnd(b,Q), Q)], ell, EellBasis, O )
        # print(f"{gamma0=}\n{gamma1=}\n")
        return gamma1*gamma0

def ComputeKernelMatrix_LeftCase( Kgens, ell, EellBasis, O ):
    r"""
    Kgens     - A tuple ((A,B), (C,D)) that specifies a kernel of an isogeny
                (A,B) and (C,D) are in E x E
    ell       - an integer such that the kernel is isomorphic as a group to C_ell x C_ell
    EellBasis - A tuple (P,Q) such that <P,Q> = E[ell]
    O         - A quaternion order such that End(E) is isomorphic to it

    This function takes in generators of a kernel subgroup of E x E and outputs the matrix
    that corresponds to the kernel.
    This function assumes that the kernel K contains (P,*) and (Q,*), where P and Q are
    generators of E[ell].
    """
    # print("ComputeKernelMatrix_LeftCase:", Kgens,ell,EellBasis)
    P,Q = EellBasis
    qb = O.basis()
    CI = itertools.chain.from_iterable
    lambdas = ComputeLambdaValues(Kgens, ell, EellBasis)
    # print("lambdas:", lambdas, sep="\n")
    sv = Matrix(list(CI(PointCoefficients(EvaluateEnd(z, r),ell,EellBasis) \
                        for r in EellBasis)) for z in qb).T \
           .solve_right(vector(CI(lambdas)))
    a = sum(Integers()(sv[i]) * qb[i] for i in range(4))
    return Matrix(2,2,((ell,0),(-a,1)))

def ComputeLambdaValues( Kgens, ell, EellBasis ):
    r"""
    This function takes in the generators of K
    [(X,Y), (Z,W)] and basis elements of E[ell] = [P, Q]
    and outputs values
    lambda11, lambda12, lambda21, lambda22 such that
    (P, [lambda11]P + [lambda12]Q) is in K and 
    (Q, [lambda21]P + [lambda22]Q) is in K.
    """
    M0, M1 = [Matrix(2,2,[PointCoefficients(g[i],ell,EellBasis) for g in Kgens], \
                base_ring=Integers(ell)) for i in [0,1]]
    # print("M0:", M0, "M1:", M1, sep="\n")
    return M0.inverse() * M1

def EvaluateEnd( alpha, P, thorough=False ):
    r"""
    alpha    - Quaternion algebra element
    P        - Point on an elliptic curve
    thorough - Boolean to check evaluation is correct

    Evaluates the point P on the endomorphism represented by alpha.
    """
    if alpha == 1:
        return P
    elif alpha == -1:
        return -P
    elif alpha == 0:
        return P.curve()(0)
    if P == P.curve()(0):
        return P
    alphacoeff = alpha.coefficient_tuple()
    if thorough:
        Qlist = P.division_points(alpha.denominator())
        retlist = []
        for Q in Qlist:
            Q1 = alpha.denominator() * alphacoeff[0] * Q
            Q2 = alpha.denominator() * alphacoeff[1] * iota(Q)
            Q3 = alpha.denominator() * alphacoeff[2] * frob(Q)
            Q4 = alpha.denominator() * alphacoeff[3] * iota(frob(Q))
            retlist.append(Q1 + Q2 + Q3 + Q4)
        retset = set(retlist)
        if len(retset) == 1:
            return retlist[0]
        else:
            return retlist
    else:
        Q = P.division_points(alpha.denominator())[0]
        Q1 = alpha.denominator() * alphacoeff[0] * Q
        Q2 = alpha.denominator() * alphacoeff[1] * iota(Q)
        Q3 = alpha.denominator() * alphacoeff[2] * frob(Q)
        Q4 = alpha.denominator() * alphacoeff[3] * iota(frob(Q))
        return Q1 + Q2 + Q3 + Q4

def EvaluatePointOnMatrix( M, X, thorough=False ):
    r"""
    M        - Matrix in M_2(O), i.e. 2 x 2 matrix with entries in O
    X        - Point on E x E, i.e. X[0] \in E and X[1] \in E
    thorough - Boolean to check evaluation is correct

    Evaluates the point P on the input matrix where each entry is taken
    to be an endomorphism on E.
    """
    return [ EvaluateEnd(M[0][0], X[0], thorough) + EvaluateEnd(M[0][1], X[1], thorough),\
             EvaluateEnd(M[1][0], X[0], thorough) + EvaluateEnd(M[1][1], X[1], thorough),]

def EvaluateSubgroupOnMatrix( M, G ):
    r"""
    M        - Matrix in M_2(O), i.e. 2 x 2 matrix with entries in O
    G        - Subgroup of E x E where each element is in E x E 
    thorough - Boolean to check evaluation is correct

    Evaluates every element in the subgroup G on the input matrix where 
    each entry is taken to be an endomorphism on E.
    """
    E = G[0][0].curve();

    retM = [];
    for X in G:
        retM.append( EvaluatePointOnMatrix( M , X ) );
    return retM;

def ConjugateTranspose( M ):
    r"""
    Computes conjugate and transpose of a given matrix M.
    Entry-wise conjugation is over the quaternion algebra.
    """
    return Matrix(2,2,[ind.conjugate() for ind in M]).transpose();

def ReducedNorm( u ):
    r"""
    This is the reduced norm as given by Lemma 2.8 in the paper.
    mathcal{N}(u) = det(u*ConjugateTranspose(u)) 
                  = det(ConjugateTranspose(u)*u) 
                  = n(a)n(d) + n(b)n(c) - tr(Conjugate(a)*b*Conjugate(d)*c)
    """
    a = u[0][0];    b = u[0][1];
    c = u[1][0];    d = u[1][1];
    ## Alternatively, we can return (u*ConjugateTranspose(u)).determinant();
    return a.reduced_norm() * d.reduced_norm() + b.reduced_norm() * c.reduced_norm() - (a.conjugate() * b * d.conjugate() * c).reduced_trace();

def ComputeKernel( M, ell, EellBasis ):
    r"""
    M          - 2 x 2 matrix with entries in a quaternion order
    EellBasis  - A tuple [P, Q] such that P and Q together generates E[ell]

    Given
    """
    P,Q = EellBasis
    c = [list(itertools.chain.from_iterable(PointCoefficients(EvaluateEnd(M[j][i], p), \
        ell, EellBasis) for j in [0,1])) for i in [0,1] for p in EellBasis]
    m = Matrix(Integers(ell), 4, 4, c).T
    k = m.right_kernel()
    # print(m, k, sep='\n')
    return [(x*P+y*Q, z*P+w*Q) for x,y,z,w in k]

def MakeKernelMatrices( ell, p, output=False ):
    r"""
    ell - small prime
    p   - prime number

    Given ell and p, this function computes all the subgroups of the form
    C_ell x C_ell and their associated matrices.
    """
    _.<xx> = GF(p)[]
    K.<z> = GF(p^2, name='z', modulus=xx^2+1)
    B.<i,j,k> = QuaternionAlgebra(-1,-p);
    O = B.quaternion_order([1, i, i/2 + j/2, 1/2 + k/2])
    E0 = EllipticCurve([K(1),K(0)])

    E0EllTors = E0(0).division_points(ell)
    # print(E0EllTors)
    BasisEll = [ E0EllTors[1], \
                 next(x for x in E0EllTors if E0EllTors[1].weil_pairing(x, ell) != 1)]
    E0xE0EllTors = list(itertools.product(E0EllTors,repeat=2))
    E0xE0EllSubgroup = FormExEellSubgroup( ell, BasisEll );

    MatrixSubgroupList = []
    for X in E0xE0EllSubgroup:
        M = ComputeKernelMatrix(X, ell, BasisEll, O)
        Kc = ComputeKernel( M, ell, BasisEll )
        assert X[0] in Kc and X[1] in Kc and len(Kc) == ell ** 2
        MatrixSubgroupList.append([M,X])
        if output:
            print(X)
            print(M)
            print()
    return MatrixSubgroupList

p = 3 * 2^43 - 1
p = 2^27 * 3^3 * 5 * 7 * 11 - 1

MSList = MakeKernelMatrices(7,p,output=False)
print(len(MSList))