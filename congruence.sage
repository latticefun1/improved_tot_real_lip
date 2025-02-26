##########
# Copyright 2024, Guilhem Mureau, Alice Pellet-Mary, Heorhii Pliatsok,
# Alexandre Wallet

# This file is part of the algorithm to solve Module-LIP in rank 2
# over totally real fields, called for referencing reason
# ModLipAttack. ModLipAttack is free software: you can redistribute it
# and/or modify it under the terms of the GNU Affero Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.  ModLipAttack is
# distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero Public License
# for more details.  You should have received a copy of the GNU Affero
# Public License along with ModLipAttack. If not, see
# <https://www.gnu.org/licenses/>

##########

#####################################################################
## The main function of this file is CongruenceSolver, which 
## takes as input a module Gram matrix Q (related to a free basis)
## of OK^2, where K is a totally real number field, and computes
## a basis B of OK^2 such that B*B^T = Q (i.e., it solves the
## module-LIP problem in K, with input Q).
######################################################################

load("two_squares.sage")
import time
from sage.stats.distributions.discrete_gaussian_lattice import DiscreteGaussianDistributionIntegerSampler

########## FUNCTIONS

##############################
#### Auxilliary functions ####
##############################

###########
## The following four functions are used to sample Gaussian elements in
## a rank-2 module represented by a (module) Gram matrix Q (more precisely,
## we generate the coordinates of a vector that would be Gaussian in this
## module).
## The function Gram_lat_from_gram_mod computes a Gram matrix of the 
## latticd (over ZZ), from the module Gram matrix.
## Gram_GPV runs the GPV algorithm (takes as input a triangular basis R of the lattice we want to sample from
## and returns the coordinates of a Gaussian vector in the lattice)
## Gaussian_Gram_init precomputes the basis R (and LLL reduces the Gram matrix of the module), to fasten
## repeated sampling in the same module lattice
## Finally, Gaussian_gram takes as input the quantities pre-computed by Gaussian_Gram_init and
## sample Gaussian vectors in the module lattice
###########

def Gram_lat_from_gram_mod(Q, K, B_OK):
    # K is a totally real number field of degree d, 
    # B_OK is a precomputed basis of OK (so we avoid that sage recomputes OK when we need the ring)
    # Q is a 2x2 matrix over OK, which is the Gram matrix of a rank-2 module
    # returns (Q_lat, B_OK) where
    # Q_lat is a (2d)x(2d) matrix over ZZ, which is the Gram matrix of the lattice (in canonical embedding) associated to the rank-2 module represented by Q
    
    d = K.degree()
        
    Q_lat = matrix(ZZ, 2*d)
    for i in range(2*d):
      for j in range(2*d):
        b1 = i//d ## takes the 1st or 2nd row of Q
        b2 = j//d ## takes the 1st of 2nd column of Q
        tmp = K(B_OK[i%d]*Q[b1,b2]*B_OK[j%d])
        Q_lat[i,j] = tmp.trace()
    return Q_lat
    
def Gram_GPV(R, sigma):
  # R is a lower-triangular matrix which defines a lattice L
  # sigma > 0 is a real number (the parameter of the gaussian distribution)
  # outputs a vector u with integer coordinates such that u*R follows a gaussian distribution with parameter sigma in L
  dim = R.ncols()
  c = vector(RR,dim)
  res = vector(ZZ,dim)
  Id = identity_matrix(ZZ,dim)
  
  for i in range(dim-1,-1,-1):
    c_tmp = c[i]/R[i,i]
    sigma_tmp = sigma/R[i,i]
    #D = DiscreteGaussianDistributionIntegerSampler(sigma=sigma_tmp, c = c_tmp)
    z = round(c_tmp)+ZZ.random_element(-round(sigma_tmp),round(sigma_tmp)) ## This is not really a Gaussian distribution, but it works well in practice, and it avoids some memory leakage that arise in large dimension when we need to call this function many times (it seems that creating a discrete Gaussian distribution objects has a small memory leakage)
    c = c-z*R[i]
    res = res+z*Id[i]
  return res
  
  
def Gaussian_gram_init(Q, K, B_OK, path_to_pari = None, path_to_GS = "./", verb = False):
    # K is a totally real number field of degree d
    # B_OK is a basis of OK (ring of integers of K)
    # Q is a 2x2 matrix over OK, which is the Gram matrix of a rank-2 module
    # returns R lower triangular such that Q = R*R^T, U unimodular such that U^T*Q_lat*U is LLL-reduced, and sigma_min which is a lower bound on the size of the parameter sigma that we can use for GPV's algorithm
    
    Q_lat = Gram_lat_from_gram_mod(Q, K, B_OK)
    t1 = time.time()
    if verb:
        print("Starting LLL reduction of the input module...")
    if path_to_pari is None:
        U = Q_lat.LLL_gram() # the LLL-reduced gram matrix is Q_red = U.transpose() * Q_lat * U
    else:
        U = LLL_gram_calling_pari(Q_lat, path_to_pari, path_to_GS = path_to_GS, verbose = verb)
    Q_red = U.transpose()*Q_lat*U ## reduced Gram matrix
    t2 = time.time()
    if verb:
        print("...done with LLL reduction")
        print("(time spent LLL reducing the basis of the input module:", Reals(20)(t2-t1), "seconds)")
    t1 = time.time()
    R = matrix(RR,Q_red.cholesky())
    t2 = time.time()
    if verb:
        print("(Cholesky decomposition took time: ", Reals(20)(t2-t1), "seconds)")
    sigma_min = 2*RR(sqrt(log(R.ncols(),2)))*max([R[i,i] for i in range(R.ncols())]) ## the sampling algorithm works for sigma > omega(sqrt(log n))*||B^*||
    return (R, U, sigma_min)
    
def Gaussian_gram(R,U,sigma,B_OK):
    # (R,U,sigma_min,B_OK) should be the output of Gaussian_gram_init (sigma >= sigma_min) on input Q,K, B_OK
    # Outputs a vector w in OK^2 such that w*B is a Gaussian vector in the module lattice spanned by B (in KR^{2*2}), where B*B^T = Q
    # said differently, w is the vector of coordinates of a Gaussian vector in the lattice implicitely defined by Q
    
    u = Gram_GPV(R, sigma) ## so that u^T * Q_red * u is small
    v = U*u ## so that v^T * Q_lat * v is small
    
    ## compute w = (w1,w2) in OK^2 that corresponds to v (i.e., w^T * Q * w corresponds to v^T * Q_lat * v
    w1 = sum([B_OK[i]*v[i] for i in range(len(B_OK))])
    w2 = sum([B_OK[i]*v[i+len(B_OK)] for i in range(len(B_OK))])
    
    return (w1, w2)
    

def FindPrimeNorm(Q, POL, R, U, sigma, B_OK, count=False, verb = False):
    # find a random vector z in OK^2 with z*Qz generating a prime ideal
    # Q is 2x2 over OK
    # POL should be defining polynomial for K
    # (R,U,sigma,B_OK) are as output by the function Gaussian_gram_init (they are pre-computed quantities that fasten the computation of random vectors in the module lattice associated to Q)
    if(count):
        cpt = 0
    is_prime=False
    
        
    while(not(is_prime)):
        if(count):
            cpt+=1
            
        (u,v) = Gaussian_gram(R,U,sigma,B_OK)
        #u, v = K( [ randint(-bo, bo+1) for _ in range(K.degree()) ] ), K( [ randint(-bo, bo+1) for _ in range(K.degree()) ] )
        z = Matrix( [ [u], [v] ] )
        q = K( list( (z.T * Q * z)[0][0] ) ) # coordinate should be integers
        Nq = Integer(det(q.matrix()))
        
        # we manually check the primality
        is_prime = Nq.is_prime(proof=False)
        
    qOK = K.fractional_ideal(q)
    (p, poldef_q) = qOK.gens_two()
                                
    if(count): #we return the second element in a two-element representation of qOK = (p, poldef_q) for later use, and v = deg poldef_q.
        return(q, (p,1, poldef_q), z, cpt) 
    else:
        return(q, (p,1, poldef_q), z)
        
#######################
#### Main function ####
#######################

def CongruenceSolver(Q, K, L, B_OK, phi = None, path_to_pari = None, path_to_GS = "./", verb = False):
    # Find the congruence matrices between Q and the identity matrix over K^2
    # Q is 2x2 over OK, with det(Q)=1.
    # L is the extension K(i) ; alternatively, K should be the totally real subfield of a cyclotomic field of conductor m such that m%4 = 0
    # B_OK is a (good) basis of OK (ring of integers of K)
    # phi (optional) is a map from K to L. If phi is None, use the default L(x) to map elements x in K to L.
    # Follows the attack described in the paper

    m = L.conductor()
    
    ## precomputing some quantities to fasten future random sampling in Q
    t1 = time.time()
    (R, U, sigma) = Gaussian_gram_init(Q, K, B_OK, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb = verb)
    t2 = time.time()
    if verb:
        print("(time spent pre-computing a good basis for random sampling in the module:", Reals(20)(t2-t1), "seconds)")

    #First we find vectors u, u2 with prime "norms" q = u^t Qu, q2 = u2^t Qu2.
    t1 = time.time()
    q, PV, u = FindPrimeNorm(Q, K.defining_polynomial(), R, U, sigma, B_OK, verb = verb)
    t2 = time.time()
        
    if verb:
      print("(time spent computing a vector of prime norm q:", Reals(20)(t2-t1),"seconds)")
    sols_q = RelativeNormSolutions(q, K, L, m, prime=True, PV=PV, phi = phi, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb = verb)
     
    TwoSquares_q = TwoSquaresFromRelativeNorm(q, K, L, m, sols_q, B_OK = B_OK, phi = phi, verb = verb)

    
    u2 = u
    t1 = time.time()
    while(u[0]*u2[1] - u[1]*u2[0] == 0): # in case of colinearity
        q2, PV2, u2 = FindPrimeNorm(Q, K.defining_polynomial(), R,U,sigma,B_OK, verb = verb)
    t2 = time.time()
    if verb:
      print("(time spent computing a second independent vector of prime norm q2:", Reals(20)(t2-t1),"seconds)")
    sols_q2 = RelativeNormSolutions(q2, K, L, m, prime=True, PV=PV2, phi = phi, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb = verb)
    TwoSquares_q2 = TwoSquaresFromRelativeNorm(q2, K, L, m, sols_q2, B_OK = B_OK, phi = phi, verb = verb)

    
    U = Matrix( [  vector(u) , vector(u2) ] ).T

    candidates = []
    for ((t1, t2), (t1_, t2_)) in itertools.product(TwoSquares_q, TwoSquares_q2):
        T = Matrix( [ [ K([ round(e) for e in t1.list()]), K([ round(e) for e in t1_.list()]) ],
                      [ K([ round(e) for e in t2.list()]), K([ round(e) for e in t2_.list()]) ] ])
        # let's prefilter the possibilities (doable when we know det(B) = det(Q) = 1)
        if(det(T) == det(U)):
            candidates += [T]

    sols = []
    for C in candidates:
        check = True
        CC = C*U.inverse()
        for r in CC:
            for e in r:
                if(e.denominator()!=1):
                    check = False
                    break
        if(check):
            sols += [CC]

    return sols
    



###########################
#### Modified function ####
###########################

def CongruenceSolver2(Q, K, L, B_OK, phi = None, path_to_pari = None, path_to_GS = "./", verb = False):
    # Find the congruence matrices between Q and the identity matrix over K^2
    # Q is 2x2 over OK, with det(Q)=1.
    # L is the extension K(i) ; alternatively, K should be the totally real subfield of a cyclotomic field of conductor m such that m%4 = 0
    # B_OK is a (good) basis of OK (ring of integers of K)
    # phi (optional) is a map from K to L. If phi is None, use the default L(x) to map elements x in K to L.
    # Follows the attack described in the paper

    m = L.conductor()
    
    ## precomputing some quantities to fasten future random sampling in Q
    t1 = time.time()
    (R, U, sigma) = Gaussian_gram_init(Q, K, B_OK, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb = verb)
    t2 = time.time()
    if verb:
        print("(time spent pre-computing a good basis for random sampling in the module:", Reals(20)(t2-t1), "seconds)")

    #First we find vectors u, u2 with prime "norms" q = u^t Qu, q2 = u2^t Qu2.
    t1 = time.time()
    q, PV, u = FindPrimeNorm(Q, K.defining_polynomial(), R, U, sigma, B_OK, verb = verb)
    t2 = time.time()
        
    if verb:
      print("(time spent computing a vector of prime norm q:", Reals(20)(t2-t1),"seconds)")
    sols_q = RelativeNormSolutions(q, K, L, m, prime=True, PV=PV, phi = phi, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb = verb)
     
    TwoSquares_q = TwoSquaresFromRelativeNorm(q, K, L, m, sols_q, B_OK = B_OK, phi = phi, verb = verb)

    u2 = [0,1]
    U = Matrix( [  vector(u) , vector(u2) ] ).T
    Uinv = U.inverse()
    newQ = U.T * Q *U
    alpha,beta,gamm = newQ[0,0],newQ[1,0], newQ[1,1]

        
    candidates = []
    u0,u1 = u.coefficients()
    for (a_,b_) in TwoSquares_q:
        c_ = (a_ * beta - b_*u0 )/alpha
        d_ = (a_ * u0 + b_* beta )/alpha
        candidates.append(Matrix(2,2,[a_,c_,b_,d_]))
        
    sols = []
    for C in candidates:
        check = True
        CC = C*Uinv
        for r in CC:
            for e in r:
                if(e.denominator()!=1):
                    check = False
                    break
        if(check):
            sols += [CC]
    
    
    return sols
    
