

# This file was *autogenerated* from the file experiments2.sage
from sage.all_cmdline import *   # import sage library

_sage_const_0 = Integer(0); _sage_const_1 = Integer(1); _sage_const_2 = Integer(2); _sage_const_4 = Integer(4); _sage_const_64 = Integer(64); _sage_const_30 = Integer(30); _sage_const_32 = Integer(32); _sage_const_10 = Integer(10); _sage_const_128 = Integer(128); _sage_const_256 = Integer(256); _sage_const_5 = Integer(5); _sage_const_512 = Integer(512); _sage_const_3 = Integer(3); _sage_const_20 = Integer(20); _sage_const_100 = Integer(100)
import time
load("congruence.sage")


def NiceOKBasis(K, L):
    # L is a cyclotomic field of conductor m = 4k, K is the maximal totally real subfield
    # OK is generated by the power basis (zeta+zeta^-1)^i, but it has less nice geometry that the basis zeta^i + zeta^-i
    # This function outputs the latter basis via a triangular change of basis (this avoids casting it from L to K)

    T = [ [ _sage_const_0  for _ in range(K.degree()) ] for _ in range(K.degree()) ]
    for i in range(K.degree()):
        T[i][i] = _sage_const_1 
        
    for i in range(_sage_const_2 , K.degree()):
        for j in range(i):
            if(j%_sage_const_2  == i%_sage_const_2 ):
                T[i][j] = binomial(i, (i-j)/_sage_const_2 )
                
    T = Matrix(T)
    Chg = T.inverse()
    B_OK = [ K(e) for e in Chg ]
    return (B_OK,T)

def FakeHawkKeyGen(K, C, MC_, bo, Hawk=True):
    # return a Hawk-like matrix but over a totally really field
    # bo is a bound on the entries of the first column
    # basically, it's Cohen algorithm to complete a basis of a rank 2 module
    # (see also: NTRU solve)
    # C should be the basis for K
    # MC_ is the matrix of the inverse of C

    if(Hawk==False):
        while(True):
            a, b, c, d = [ K( [ randint(-bo, bo+_sage_const_1 ) for i in range(K.degree()) ] ) for _ in range(_sage_const_4 ) ]
            if(a*d-b*c != _sage_const_0 ):
                break
        return Matrix( [ [a, c], [b ,d] ] )
    
    s = K.gen()
    a = sum( [ randint(-bo, bo+_sage_const_1 )*s**i for i in range(K.degree()) ] )
    A = a.matrix().LLL()
    while True:
        # we try to find a coprime principal ideal
        b = sum( [ randint(-bo, bo+_sage_const_1 )*s**i for i in range(K.degree()) ] )
        B = b.matrix().LLL()
        A_B = block_matrix( [ [A], [B] ] ).change_ring(ZZ)
        H,T = A_B.hermite_form(transformation=True) # will be long for large field
        if(H[_sage_const_0 :K.degree()]==identity_matrix(K.degree())):
            break
    # (a) and (b) are coprime, we can find ad-bc = 1    
    d = K(T[_sage_const_0 ][_sage_const_0 :K.degree()]*A)/a
    c = -K(T[_sage_const_0 ][K.degree():_sage_const_2 *K.degree()]*B)/b

    # Now we algebraically size-reduce according to the chosen basis of K   
    mu = (a*c+b*d)/(a**_sage_const_2 +b**_sage_const_2 )
    coord_mu = vector(mu)*MC_
    mu_round = sum( round(coord_mu[i])*C[i] for i in range(K.degree()) )
    c_red = c - mu_round * a
    d_red = d - mu_round * b

    return Matrix( [ [ a, c_red ], [ b, d_red ] ] )

pari_size_max = _sage_const_64 *_sage_const_2 **_sage_const_30 
path_to_pari = None

def param(e):
    return (euler_phi(_sage_const_4 *e), _sage_const_4 *e, e)

LIST_m  = { _sage_const_32 :[_sage_const_10 , [], _sage_const_0 ], _sage_const_64 :[_sage_const_10 , [], _sage_const_0 ], _sage_const_128 :[_sage_const_10 , [], _sage_const_0 ], _sage_const_256 : [_sage_const_5 , [], _sage_const_0 ], _sage_const_512 :[_sage_const_5 ,[],_sage_const_0 ] }
LIST_m2 = { _sage_const_32 :[_sage_const_10 , [], _sage_const_0 ], _sage_const_64 :[_sage_const_10 , [], _sage_const_0 ], _sage_const_128 :[_sage_const_10 , [], _sage_const_0 ], _sage_const_256 : [_sage_const_5 , [], _sage_const_0 ], _sage_const_512 :[_sage_const_5 ,[],_sage_const_0 ] }

LIST_m  = { _sage_const_512 :[_sage_const_1 ,[],_sage_const_0 ] }
LIST_m2 = { _sage_const_512 :[_sage_const_1 ,[],_sage_const_0 ] }

#LIST_m = { 4*9:[10, [], 0], 4*13:[10, [], 0], 4*19:[10, [], 0], 4*21:[10, [], 0], 4*26:[10, [], 0], 4*31:[5, [], 0], 4*39:[5, [], 0], 4*45:[5, [], 0], 4*51:[5, [], 0], 4*57:[5, [], 0] }

#LIST_m = { 340:[3, [], 0], 296:[3, [], 0] } #276:[5, [], 0], 260:[5, [], 0],  232:[3, [], 0],

path_to_GS = "Gentry_Szydlo/"

Verb = _sage_const_0 
for m in LIST_m:
    
    pari.allocatemem(s = pari.stacksize(), sizemax = pari_size_max)
    L = CyclotomicField(m)
    print("Running over a field of conductor", m, " and degree", euler_phi(m))
    (K, phi) = L.maximal_totally_real_subfield()

    NTEST = LIST_m[m][_sage_const_0 ]    
    
    print("\nComputing a basis of OK and its inverse...")
    t1 = time.time()
    B_OK, MC_ = NiceOKBasis(K, L)

    for _ in range(NTEST):
        
        print("\nCreating the challenge instance...")
        t1 = time.time()
        B = FakeHawkKeyGen(K, B_OK, MC_, _sage_const_3 , Hawk=True)
        Q = B.T*B
        t3 = time.time()
        print("...done creating the challence instance")
        print("(this took", Reals(_sage_const_20 )(t3-t1), "seconds)\n")

        print("\nStarting the attack using the original algorithm...")
        t1 = time.time()
        sols = CongruenceSolver(Q, K, L, B_OK, phi, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb=Verb)
        t2 = time.time()
        print("...the attack is over")
        print("(this took", Reals(_sage_const_20 )(t2-t1), "seconds)\n")
        if B in sols:
            print("and the original basis is part of it (attack successful!)")
            LIST_m[m][_sage_const_1 ] += [ Reals(_sage_const_20 )(t2-t1) ]
        else:
            print("and the original basis is *not* part of it (attack failed...)")
        
        print("\nStarting the attack using our modified algorithm...")
        t1 = time.time()
        sols2 = CongruenceSolver2(Q, K, L, B_OK, phi, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb=Verb)
        t2 = time.time()
        print("...the attack is over")
        print("(this took", Reals(_sage_const_20 )(t2-t1), "seconds)\n")

        if B in sols2:
            print("and using our algorithm, the original basis is part of it (attack successful!)")
            LIST_m2[m][_sage_const_1 ] += [ Reals(_sage_const_20 )(t2-t1) ]
        else:
            print("and using our modified algorithm,  the original basis is *not* part of it (attack failed...)")

            
    LIST_m[m][_sage_const_2 ] = sum( LIST_m[m][_sage_const_1 ] )/NTEST
    LIST_m2[m][_sage_const_2 ] = sum( LIST_m2[m][_sage_const_1 ] )/NTEST
    print("Average attack time using the original algorithm for", (m, euler_phi(m)), ":", LIST_m[m][_sage_const_2 ])
    print("Average attack time using the modified algorithm for", (m, euler_phi(m)), ":", LIST_m2[m][_sage_const_2 ])
    print("="*_sage_const_100 )
    
print( [ LIST_m[e][_sage_const_2 ] for e in LIST_m ] )
print( [ LIST_m2[e][_sage_const_2 ] for e in LIST_m2 ] )


