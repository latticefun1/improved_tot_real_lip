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

#####################################################
## This file contains the functions
## related to decomposing an element of 
## OK as a sum of two squares in a 
## totally real number field K (here, OK
## is the ring of integers of K).
## The main functions of this file are
##  -RelativeNormSolutions: which solves
##   norm equations in relative CM extensions
##   (K totally real and L totally imaginary of
##   degree 2 over K).
##  -TwoSquaresFromRelativeNorm, which converts
##   a solution of a norm equation in L/K with
##   L = K(i) and K totally real, into a solution
##   to a sum-of-two-squares problem
######################################################


import itertools, time, os
os.chdir("Gentry_Szydlo/") #changing repository to load Gentry_Szydlo.sage, otherwise the load inside Gentry_szydlo.Sage are not working...
load('Gentry_Szydlo.sage')
os.chdir("../") #back to 'normal' repository

########## FUNCTIONS

##############################
#### Auxilliary functions ####
##############################

def Embeddings(v):
    # sage does not order embeddings the same way if the field is CyclotomicField or RelativeNumberField.
    # we reorder them if needed (we only need half of them anyway)
    emb_v = v.complex_embeddings()
    emb_v_out = []
    if(emb_v[0] == emb_v[1].conjugate()):
        emb_v_out = [ emb_v[2*i] for i in range(len(emb_v)/2) ] + [ emb_v[2*i+1] for i in range(len(emb_v)/2) ]
    else:
        emb_v_out = emb_v

    return emb_v_out
     
def Proj(v):
    # projection onto the LogUnitLattice space
    nu = len(v)
    av_nu = (1/nu) * sum(v)
    return vector( v[i] - av_nu for i in range(nu) )

def Log(a):
    # Log embedding
    L = a.parent()
    nu = sum(L.signature())
    a_emb = vector(Embeddings(a)) # vector(a.complex_embeddings()) 
    return vector( 2 * log(abs(a_emb[i])) for i in range(nu) )

def LogUnitLattice(L, cyclo_units=False):
    # return a list FU of fundamental units in L and two matrices B, Bdag
    # B is a row-matrix of their Log-embedding, Bdag is the pseudo-inverse
    
    FU = L.units(proof=False) # if proof=True, "takes forever" (sic);
    # may not be the real log-unit lattice, but will suffice.
    # We could directly feed the cyclotomic units if L is a cyclotomic field?
    
    B = Matrix( [ Log(FU[i]) for i in range(len(FU)) ] )
    Bdag = ((B*B.T)^-1 * B).T #for lattice decoding
    return FU, B, Bdag

def UnitDecoding(t, Bdag):
    # gets a unit close of t, in the Log-space
    # returns the coordinate of t wrt. the fundamental units, if t is a unit
    plog_t = Proj(Log(t))
    return vector( round(e) for e in plog_t * Bdag )

def GenerateInstance(K, L, B, which="with sol"):
    # Coefficients of the intances are less than B.
    # if which = two squares, will generate a = x^2 + y^2 from OK and return x,y too
    # if which = with sol, will generate a = xx^* and return x too
    # if which = random, will generate a random element in K and return 0,0 too for coherence
    # we avoid ramifications at the moment, for simplicity in testing.
    if(which=="two squares"):
        DK = K.absolute_discriminant()
        while(True):
            x,y = K( [ randint(-B, B+1) for _ in range(K.absolute_degree()) ] ),  K( [ randint(-B, B+1) for _ in range(K.absolute_degree()) ] )
            a = x^2+y^2
            if(gcd(a.norm(), DK) == 1):
                
                break
        
    elif(which=="with sol"):
        DL = L.absolute_discriminant()
        while(True):
            x = L( [ randint(-B, B+1) for _ in range(L.absolute_degree()) ] )
            y = x.conjugate()
            a = x*y
            if(gcd(a.norm(), DL) == 1):
                break

    elif(which=="random"): # should basically never give a solution
        DK = K.absolute_discriminant()
        while(True):
            x = 0
            y = 0
            a = K( [ randint(-B, B+1) for _ in range(K.absolute_degree()) ] )
            if(gcd(a.norm(), DK) == 1):
                break
    return a, x, y 

def PrimesAbove(a, K, L, phi = None):
    # return the set of inerts and of splits above aOK with their exponents
    # phi is a map from K to L (when K,phi = L.maximal_totally_real_subfield(), using phi instead of L(x) for x in K improves considerably the running time in large dimension). If phi is None, use the default L(x) when x is in K
    # where L is a quadratic extension of K

    inerts_list = []
    splits_list = []
    
    aOK = Ideal(K(a))
    aOK_primes = aOK.factor() # can be slow, no way to avoid it.
        
    for (p,v) in aOK_primes:
        p_2gens = p.gens_two()
        if phi is None:
          pOL = Ideal( L(p_2gens[0]), L(p_2gens[1]) )
        else:
          pOL = Ideal( L(phi(p_2gens[0])), L(phi(p_2gens[1])) )
        pOL_primes = pOL.factor() # could be done by hand
        if(len(pOL_primes)==1):
            inerts_list += [ (pOL_primes[0][0], v) ]
        else:
            for (pp,vv) in pOL_primes:
                splits_list += [(pp, vv)]

    return inerts_list, splits_list

def CandidateIdeals(a, splits_list, inerts_list, cyclo=False, prime=False, phi = None, path_to_pari = None, path_to_GS = "./", verb=False):
    # compute all the product of all primes with all possible valuations given in split_list
    # split_list should be a list as ((P1, v1),  (P1*, v1),  (P2, v2), (P2*, v2), ...), with Pi a prime ideal in L and vi the corresponding valuation.
    # Then it keeps only the ones who are principal
    # If prime=True, we know splits_list = [P, P*] or inerts_list = [ P ], and that P is principal (this is from the attack designe)
    # so we avoid computing the product and do only one Gentr-Szydlo
    # phi is a map from K to L (when K,phi = L.maximal_totally_real_subfield(), using phi instead of L(x) for x in K improves considerably the running time in large dimension). If phi is None, use the default L(x) when x is in K
    # Outputs a list of (PrincipalIdeal, generator, valuations, valuations)

    for (I,v) in inerts_list:
        if(v%2!=0):
            raise Exception("Valuations at inert should be even.")

    candidates = []

    if(prime): # Note that the prime flag is True generally only for the attack, so only if cyclo=True too
        
        if(len(inerts_list)==1):

            J = inerts_list[0][0]
            L = J.gens()[0].parent()
            if phi is None:
              La = L(a)
            else:
              La = L(phi(a))
            if verb:    
                print("Finding the generator of an inert candidate...")
            
            if verb:
                print("\nEntering Gentry-Szydlo's algorithm... : D")
            t1 = time.time()
            gens = gentry_szydlo(J, La, L, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verbose = verb) 
            t2 = time.time()
            if verb:
                print("...done with Gentry-Szydlo's algorithm")
                print("(time spent in the Gentry-Szydlo algorithm:", Reals(20)(t2-t1),"seconds)\n")
                
            candidates += [(J, gens, 1, 1)]

        else: #then qOL = P P.conjugate()
            
            J = splits_list[0][0]
            L = J.gens()[0].parent()
            if phi is None:
                La = L(a)
            else:
                La = L(phi(a))
            if verb:    
                print("Finding the generators of two conjugate candidates...")

            if verb:
                print("\nEntering Gentry-Szydlo's algorithm...")
            t1 = time.time()
            gens = gentry_szydlo(J, La, L, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verbose = verb) 
            t2 = time.time()
            if verb:
                print("...done with Gentry-Szydlo's algorithm")
                print("(time spent in the Gentry-Szydlo algorithm:", Reals(20)(t2-t1),"seconds)\n")

            candidates += [(J, gens, 1, 1)] + [ (splits_list[1][0], gens.conjugate(), 1, 1) ]
                
                
    else:
        
        exponents_splits = [ [ _ for _ in range(v+1) ] for (I,v) in splits_list[0::2] ]
        possible_splits = [] 
        for e in itertools.product( *exponents_splits ): # compute all ideals products;
            J = 1
            val = []
            for i in range(len(splits_list)/2):
                Q, Qbar, v = splits_list[2*i][0], splits_list[2*i+1][0], splits_list[2*i][1]
                J *= Q^e[i] * Qbar^(v-e[i])
                val += [v]
            possible_splits += [(J,val,e)]

        inert_part = prod( I^(Integer(v/2)) for (I,v) in inerts_list )
        L = J.gens()[0].parent()
        if verb:    
            print("Finding the principal ideals among", len(possible_splits), "candidates...")
        if phi is None:
              La = L(a)
        else:
              La = L(phi(a))
        for (J,v,e) in possible_splits:
            C = inert_part * J
            # C is in two-elements representation.
            if(cyclo):
                if verb:
                    print("\nEntering Gentry-Szydlo's algorithm... : D")
                t1 = time.time()
                gens = gentry_szydlo(J, La, L, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verbose = verb) # if J is not principal, this returns None
                t2 = time.time()
                if verb:
                    print("...done with Gentry-Szydlo's algorithm")
                    print("(time spent in the Gentry-Szydlo algorithm:", Reals(20)(t2-t1),"seconds)\n")
                if(gens==None):
                    if(verb):
                        print("An ideal was not principal.")
                    continue
                else:
                    candidates += [ (C, gens, v, e) ]

            else:
                gens = C.gens_reduced()  # PIP solver, this is the bottleneck. We use Gentry-Szydlo in cyclotomic case.
                if(len(gens)==1):
                    candidates += [(C, gens[0], v, e)]
    
    return candidates
                

#############
## The following three functions are auxilliary function whose objective
## is to be able to cast elements from L to K (when we know that the element
## must belong to the subfield K of L). For some reason, if x is an element of
## L and we know that it belongs to K, doing y = K(x) is sage results in some
## error ("ValueError: cannot convert NaN or infinity to Pari float") when the dimension of K is somewhat large
## (e.g., for L of conductor 128). We think this may be due to precision issue when computing
## complex embeddings in L.
## To circumvent this, we reimplemented a function from_K_to_L, which only manipulates rational
## numbers. Namely, it computes a basis (bi) of OK, maps it to L and generate the matrix B whose row
## are the coordinates of the bi's in a given basis of L. Then it pre-computes the pseudo-inverse
## of this matrix (to fasten repeated computation), and use it to solve linear equations
## of the form z*B = x_coord, where x_coord are the coordinates of our target x in the given basis of L.
## Our function is targeted to cyclotomic fields, and we use the fact that we know good bases
## of OK and OL in this case.
##############
def pseudo_inverse(M):
    # M is a matrix with rational coefficients and more columns than rows
    # Output M_ with rational coefficients such that M*M_ = Id
    
    # Add rows to M to make it square and invertible
    M_completed = Matrix(QQ,M)
    r = rank(M_completed)
    for i in range(M.ncols()):
        ei = vector(QQ,i*[0]+[1]+(M.ncols()-1-i)*[0])
        M_tmp = matrix(QQ,list(M_completed)+[ei])
        if rank(M_tmp) > r:
            M_completed = M_tmp
            r = r+1
            if r == M.ncols():
                break
    # invert the completed matrix, and extract the good columns of the inverse
    M_ = M_completed^(-1)
    M_ = M_[range(M.ncols()),range(M.nrows())] ## extracting the first columns of M_
    assert(M*M_ == identity_matrix(M.nrows()))
    return M_

def from_L_to_K_cyclo_precomp(K,L,B_OK = None, phi = None):
    # input: L cyclotomic field and K totally real field of L
    #        optionally, takes the nice basis B_OK = (K(t^i + t^(-i))_i of OK as input (where t = L.gen())
    #        optionally, takes a map phi from K to L (when K,phi = L.maximal_totally_real_subfield(), using phi instead of L(x) for x in K improves considerably the running time in large dimension). If phi is None, use the default L(x) when x is in K
    # output: a list list_bi of elements of K forming a basis of OK, together with the pseudo-inverse M_ of the matrix of the coefficients of the bi in L
    if B_OK is None:
        OK = K.ring_of_integers()
        B_OK = OK.basis()
    list_bi = [K(bi) for bi in B_OK] ## casting vectors of OK.basis() in K makes computation faster
    if phi is None:
        M = matrix(QQ,[list(L(bi)) for bi in list_bi])
    else:
        M = matrix(QQ,[list(L(phi(bi))) for bi in list_bi])
    M_ = pseudo_inverse(M)
    return(list_bi, M_)
    
def from_L_to_K_cyclo(x,K,L, list_bi = None, M_ = None, phi = None):
    # input: L cyclotomic field, K totally real subfield of L, x an element whose parent is L, but actually living in the subfield K, and (list_bi,M_) which is output by the function from_L_to_K_cyclo_precomp(K,L).
    #        also takes optionally phi, a map from K to L
    # output: Kx, which equals x, but whose parent is now K
    # Note: using Kx = K(x) works for small element x of K, but we sometimes gets errors when the elements becomes larger ("ValueError: cannot convert NaN or infinity to Pari float")
    if list_bi is None or M_ is None:
      list_bi, M_ = from_L_to_K_cyclo_precomp(K,L)
    
    v = vector(QQ,list(L(x)))*M_ ## v should have integer coordinates
    Kx = K(0)
    for i in range(len(list_bi)):
        Kx += list_bi[i]*v[i]
    if phi is None:
        assert(L(Kx) == x)
    else:
        assert(L(phi(Kx)) == x)
    return Kx
    
    
########################
#### Main functions ####
########################

def RelativeNormSolutions(a, K, L, m, prime=False, PV=(0,0,0), phi = None, path_to_pari = None, path_to_GS = "./", verb=False):
    # given a in OK, solve xx^* = a using L=K(i)
    # use with m=0 if K is totally real but may not be a cyclotomic totally real subfield. !!!WARNING: this does not use Gentry-Szydlo, so it is slow!!!
    # takes optionally phi, a map from K to L (if phi is None, will use the default L(x) for x in K, to map elements from K to L, but this can be slow in large dimension)
    # returns a (possibly empty) set of solutions
    # if prime=True, an additional data PV is expected, containing a two-element representation of a prime ideal aOK = (p, poldef_a)
    # this allows to avoid refactoring aOK when we know it is a prime ideal.
    
    if(m%4==0 and m!=0):
        roots_of_unity = L.roots_of_unity()
    else:
        ii = L.gen()
        roots_of_unity = [ 1, -1, ii, -ii ]
    
    inerts_list, splits_list = [], []
    
    if(prime): # primes in OK may split in OL, but we would like to avoid refactoring; 
        p, v, poldef_a = PV
        Fp = GF(p)
        PolFp.<X> = PolynomialRing(Fp)
              
        if(v==1): #possibly this code could be factorised; we handle differently if the field is prime or an extension
            pol = PolFp(list(poldef_a))
            Delta = (X^2-4).mod(pol) # discriminant of T^2 - sT + 1 (defining L over K)
            is_split, sqr_root = is_square(Delta, root=True)
            
            if(is_split): # pOK splits in OL in two conjugates; equivalently, T^2 - sT + 1 = (T-d1)(T-d2) mod p
                
                xx = X.mod(pol) 
                d1 = (1/Fp(2)) * (xx + sqr_root)
                d2 = (1/Fp(2)) * (xx - sqr_root)
                p = ZZ(p) # cast p to ZZ because by default p is in K, and we need to cast it later on to L, which may be costly
                t = L.gen()

                if(phi==None):
                    PP = Ideal(L(p), t-L(d1))
                    PPbar = Ideal(L(p), t-L(d2))
                    splits_list = [ (PP, 1), (PPbar, 1) ]
                else:
                    PP = Ideal(phi(p), t-phi(d1))
                    PPbar = Ideal(phi(p), t-phi(d2))
                    splits_list = [ (PP, 1), (PPbar, 1) ]
            else:
                if not phi:
                    inerts_list = [ (Ideal(L(q)), 1) ] # it is in particular principal
                else:
                    inerts_list = [ (Ideal(phi(q)), 1) ]

        else:
            pol = PolFp(list(poldef_a))
            Fq.<T> = Fp.extension(pol)
            Delta = T^2-4 
            is_split, sqr_root = is_square(Delta, root=True)
            if(is_split): 
                d1 = (1/Fq(2)) * (T + sqr_root)
                d2 = (1/Fq(2)) * (T - sqr_root) 
                t = L.gen()
                if not phi:
                    PP = Ideal( L(p), t-L(d1.list()) )
                    PPbar = Ideal( L(p), t-L(d2.list()) )
                    splits_list = [ (PP, 1), (PPbar, 1) ]
                else:
                    PP = Ideal( phi(p), t-L(d1.list()) )
                    PPbar = Ideal( phi(p), t-L(d2.list()) )
                    splits_list = [ (PP, 1), (PPbar, 1) ]
               
                    
            else:
                if not phi:
                    inerts_list = [ (Ideal(L(q)), 1) ]
                else:
                    inerts_list = [ (Ideal(phi(q)), 1) ]
    else: # this covers the general case for two-square or relative norms problems.
        inerts_list, splits_list = PrimesAbove(a, K, L, phi = phi)
        if(verb):
            print("Factoring aOK done.")

    for (p,v) in inerts_list:
        if(v%2!=0 and verb):
            print("No solution for this norm equation.")
            return
        
    if(m%4==0 and m!=0):
        if(prime):
            candidates = CandidateIdeals(a, splits_list, inerts_list, cyclo=True, prime=True, phi = phi, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb=verb)
        else:
            candidates = CandidateIdeals(a, splits_list, inerts_list, cyclo=True, phi = phi, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verb=verb)
            
    else:
        candidates = CandidateIdeals(a, splits_list, inerts_list, phi = phi, verb = verb)
    if(verb):
        print("Finding candidate ideals done. Found", len(candidates), "ideals.")
        if(len(candidates)==0):
            print("Something went wrong, try again.")
            return Set()

    if(verb):
        print("Finding actual solutions...")

    
    sol = Set()
    cpt = 0
    for (J,g,v,e) in candidates:
        # using Gentry-Szydlo, we find the correct generator (up to roots of unity)
        Lg = [ rho * g for rho in roots_of_unity ] # [ w^i * g for i in range(m) ] 
        Lg_ = [ rho * g.conjugate() for rho in roots_of_unity ] # [ w^i * g.conjugate() for i in range(m) ]
        sol += Set(Lg) + Set(Lg_)

    # sanity check, can be commented if confident
    all_sols = True
    for s in sol:
        if phi is None:
            all_sols = all_sols & (s*s.conjugate() == L(a))
        else:
            all_sols = all_sols & (s*s.conjugate() == L(phi(a)))
            
    if(verb):
        if(all_sols):
            print("Done. Solutions of the relative norm equation found:", len(sol))
        else:
            print("?????")

    return sol


def TwoSquaresFromRelativeNorm(a, K, L, m, sol, B_OK = None, phi = None, verb=False):
    # from an element a in OK and a set sol of solutions of xx^* = a in OL
    # returns a list of tuple (x,y) in OK^2 such that a = x^2+y^2
    # use m=0 if K may not be a cyclotomic totally real subfield
    
    if(verb):
        print("Searching two-squares decompositions...")
    #L = OL.number_field()
    
    if B_OK is None:
      OK = K.ring_of_integers()
      B_OK = [K(b) for b in OK.basis()]
    
    true_sols = []
    # last step is to find the solutions coming from OK + iOK
    # can be done by a relative trace computation and a parity check
    if(m%4==0 and m!=0):
        ii = L.gen()^(m/4)  
        (list_bi, M_) = from_L_to_K_cyclo_precomp(K, L, B_OK, phi = phi)
        for s in sol:
            check = True
            #xx = (s+s.conjugate())/2
            #if xx in OL: ## if xx is in OL, then automatically yy will be in OL too
            tr_s = s+s.conjugate()
            for cof in tr_s.list():
                if(ZZ(cof)%2 !=0):
                    check = False
                    break
            if(check):
                xx = tr_s/2
                yy = (s-s.conjugate())/(2*ii)
                true_sols += [ (from_L_to_K_cyclo(xx,K,L, list_bi, M_, phi = phi), from_L_to_K_cyclo(yy,K,L, list_bi, M_, phi = phi)) ]
                
    else: #sadly, a relative field is a bit less flexible than an absolute one
        ii = L.gen()
        for s in sol:
            check = True
            tr_s = s+s.conjugate() 
            for cof in (tr_s[0]).list():
                if(ZZ(cof)%2!=0):
                    check = False
                    #print(s, " did not give a two-square decomposition.")
                    break
            if(check):    
                xx = K( tr_s[0]/2 ) 
                yy = K( ((s-s.conjugate())/(2*ii))[0] )
                true_sols += [ (xx, yy) ] 

    # sanity check, can be commented if confident
    all_true_sols = True
    for (xx,yy) in true_sols:
        all_true_sols = all_true_sols & (a==xx^2+yy^2)

    if(verb):
        if(all_true_sols):
            print("Found", len(true_sols)/4, "two-squares decompositions.") # we always find (x,y), (-x,y), (x,-y) and (-x,-y)
        else:
            print("?????")

    return true_sols


########## TESTING RELATIVE NORMS
# uncomment below to test this code

# m = 4*17 #code should work for any conductors, but will be slow if m%4 != 0, until GentrySzydlo is updated to works on CM

# L = CyclotomicField(m)
# OL = L.ring_of_integers()
# (K, phi) = L.maximal_totally_real_subfield()

# if(m%4!=0):
#    R.<X> = PolynomialRing(QQ)
#    L.<ii> = K.extension(X^2+1)

#which="with sol"
#a, x, y = GenerateInstance(K, L, 3, which="two squares")
#sols = RelativeNormSolutions(a, K, OL, m)

#if(which=="with sol"):
#    print(x in sols)

#elif(which=="two squares"):
#    TwoSquares = TwoSquaresFromRelativeNorm(a, K, OL, m, sols)
#    print((x,y) in TwoSquares)
    
