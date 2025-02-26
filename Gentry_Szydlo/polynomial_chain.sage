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

######################################################################
## This file contains the functions related to the so-called
## polynomial chain computations in the Gentry-Szydlo algorithm.
## The intuition is that we are doing a fast exponentiation of
## our input ideal, but with some tricks to keep its size controlled.
## The main function of this file is smallpow_modQ, all other functions
## are auxilliary functions.
######################################################################

load("implicit_reduction.sage")

############################
### Auxilliary functions ###
############################


#####
## reimplementing operations modulo a 
## prime integer in a number field
## (generic functions modulo an ideal
## are quite slow, we gain a factor 50 to
## 100 with our 3 small functions below)
#####

def center_remainder(a,b):
    ## return a representative of a mod b in (-b/2, b/2]
    ## TODO there is most probably already a function in sage for this, but I could not find it...
    res = a%b
    if res <= b/2:
      return res
    else:
      return res-b

def mod_fast(x,P,L):
    ## computes x modulo P, where x is an element in the number field L, and P is a prime integer (in ZZ)
    list_x = list(L(x))
    res = L([center_remainder(xi,P) for xi in list_x])
    return res 

def inverse_mod_fast(x,P,L):
    ## computes x^(-1) modulo P, where x is an element in the number field L, and P is a prime integer (in ZZ)
    norm_x = x.norm()
    if not norm_x.is_integer():
      raise ValueError("x must be in the ring of integers (for inversion modulo P)")
    norm_x = ZZ(norm_x)
    return mod_fast(norm_x.inverse_mod(P)*(norm_x/x),P,L)



# Input : two integers m, and min_P, a number field L whose ring OL is generated by the power basis and x an element of OL
# Output : two primes P1 and P2 >= min_P such that P1 = P2 = 1 mod m and gcd(P1-1, P2-1) = m and P1*OL and P2*OL are coprime with x*OL, and integers u,v such that (P1-1)*u + (P2-1)*v = 1.

def good_primes(m,min_P, x, L):
    P1 = 1 + m*ceil(min_P/m)
    norm_x = x.norm()
    while not (gcd(P1,norm_x) == 1 and P1.is_prime()):
      P1 += m
    P2 = P1
    while not (gcd(P1-1, P2-1) == m and gcd(P2,norm_x) == 1 and P2.is_prime()):
      P2 += m
    (_,u,v) = xgcd(P1-1, P2-1)
    assert(P1.is_prime() and P2.is_prime() and u*(P1-1)+v*(P2-1) == m and L.fractional_ideal(P1) + L.fractional_ideal(x) == L.fractional_ideal(1) and L.fractional_ideal(P2) + L.fractional_ideal(x) == L.fractional_ideal(1)) ##TODO remove if we are convinced
    return(P1, P2, u, v)



# Input : I_pari is pari's representation of the ideal I=v_0*OL, 
#         x = v_0*bar(v_0) an element of L, 
#         k a positive integer
#         P a prime integer such that x is not a zero divisor modulo P
#         OL the ring of integers of L
#         path_to_pari is a string, used to call a specific version of pari/gp if it is not none
#         path_to_GS is a string, used if we want to load the file from another directory (needed only if path_to_pari is not None)
#         verbose is a boolean, if true, print debugging comments
# Output : Polynomial chains {(v_0**(k_i})*(v_i**2)*bar(v_i+1)} and {v_i*bar(v_i)} where the k_i's (i <= r) are the digits of k in base 2.
# The v_i's are short vectors and not zero divisors modulo P.

def pol_chain(I_pari,x,k,P, L, path_to_pari = None, path_to_GS = "./", verbose = False):
    
    ## Only when path_to_pari is not None: creates a folder for temporary files,
    ## which will be used to store the input and output of pari/gp
    if not (path_to_pari is None): 
      tmp_dir_name = "GentrySzydlo_temporary_files"
      if not os.path.isdir("GentrySzydlo_temporary_files"): ## test if the directory already exists, and if not create it
        os.mkdir("GentrySzydlo_temporary_files")
        if verbose:
          print("(creating folder GentrySzydlo_temporary_files)")
      else:
        if verbose:
          print("(folder GentrySzydlo_temporary_files already exists, continuing)")
    
    nf = pari(L)
    chain = []
    chain_norm = [x]
    
    digits = k.digits(2)
    r = len(digits)
    if verbose:
      print("length of the polynomial chain (number of LLL calls): ", r-1)
    J_pari = I_pari
    normi = x
    normj = x

    # Latter we will need to invert x modulo P, this can be tested by computing the gcd of the ideals x*OL and P*OL.
    assert(L.fractional_ideal(x) + L.fractional_ideal(P) == L.fractional_ideal(1)) ##TODO remove once convinced that it works 

    # Now we start computing the polynomial chains.
    for i in range(r-2,-1,-1): 
        c = digits[i]
        if c == 1:
          I_power_pari = pari.idealmul(nf,I_pari,pari.idealpow(nf,J_pari,2))
        else:
          I_power_pari = pari.idealpow(nf,J_pari,2)
        if verbose:
          print("ideal computed...")
        
        # We compute the norm of a generator of I_power = (v_0**c * v_i**2) * OL.
        # A short vector w in I_power is found using implicit_reduction on the basis of I_power.
        # It has shape w = v_0**c * v_i**2 * a_i and we put bar(v_i+1) := a_i if v_i+1 * bar(v_i+1) is invertible modulo P, otherwise 
        # we take other candidates for w until this is the case.  
        norm_power = (normi**c)*(normj)**2
        red_basis = implicit_reduction(I_power_pari,norm_power,L, path_to_pari = path_to_pari, path_to_GS = path_to_GS, verbose = verbose)
        w = red_basis[0]
        new_norm = w*conjugate(w)/norm_power
        l = 1
        while L.fractional_ideal(new_norm) + L.fractional_ideal(P) != L.fractional_ideal(1) and l < len(red_basis):
            w = red_basis[l]
            new_norm = w*conjugate(w)/norm_power
            l += 1
        chain.append(w)

        # We update the data by computing the ideal J generated by v_i+1 and its norm v_i+1 * bar(v_i+1).
        w_pari = pari(L.fractional_ideal(conjugate(w)/norm_power)) ##TODO this could be optimized here, we simply multiply an ideal by en element...
        J_pari = pari.idealmul(nf, w_pari, I_power_pari)
        normj = new_norm   
        chain_norm.append(normj)

    return(chain, chain_norm)
           


# Input : Two chains of polynomials, output by pol_chain, the exponent k, a modulus Q, and a basis of O_L.
# Output : The polynomial chain evaluated in Q i.e., v_0**k * bar(v_r) mod Q, where v_r is the last element of chain and where k is 
# the exponent used to compute the chains.

def eval_chain(chain,chain_norm,k,Q,L):
    # L is a number field with OL generated by the power basis
    # Requires that all the element in chain_norm are invertible modulo Q (i.e., their algebraic norm is coprime with Q)
    # We compute v_0**k * bar(v_r) mod Q iteratively. The first term is v_0**{k_r-1} * v_0**2 * bar(v_1),
    # which is exactly the first element in chain.
    
    r = len(k.digits(2))
    partial_prod = mod_fast(chain[0],Q, L)
    
    
    for i in range(1,r-1):
        partial_prod = mod_fast(partial_prod**2 * chain[i] * inverse_mod_fast(chain_norm[i], Q, L)**2, Q, L)
        
    return(partial_prod)


#######################
#### Main function ####
#######################

# Input : a basis of the ideal I=v_0*OL, its relative norm x = v_0*bar(v_0). The conductor m of the field. A size parameter e.
# Output : v_0**m
    
def smallpow_modQ(I_pari,x,min_Q,m,min_P, L, path_to_pari = None, path_to_GS = "./", verbose = False):
    ## Input: I_pari is an ideal in pari format, generated by some (secret) element s
    ##        x is the that x = s*bar(s)
    ##        m is an integer, it is the conductor of the ambiant cyclotomic field (or twice the conductor of the latter is odd)
    ##        min_Q is an estimate on the smallest value of Q required to recover the result, it should be > 2*maximum coeff of s^m
    ##        min_P is an estimate on the smallest value of P required to recover the good intermediate result, it depends on the quality of the LLL algorithm
    ##        path_to_pari is a string to a potential more recent installation of pari/gp (default: None)
    ##        path_to_GS is the path from the current directory (where Sage is run) to the directory containing the Gentry-Szydlo code 
    ##          files. It is required only when path_to_pari is not None
    ##        verbose is a boolean (default: False). If set to True, the algorithm will print some intermediate values and other
    ##          informations that can be useful for debugging.
    ## Output: the element s^m

    # First we compute good primes P1, P2 together with a Bezout relation (P1-1)*u + (P2-1)*v = 1.
    (P1, P2, u, v) = good_primes(m,min_P,x, L)
    if verbose:
      print("P1 = ", P1, ", P2 = ", P2)

    # Using gen_pow_modQ, we compute v_0**(P1-1) mod Q and v_0**(P2-1) mod Q.
    if verbose:
      print("\nentering the first polynomial chain computation...")
    (chain1, chain_norm1) = pol_chain(I_pari,x,P1-1,P1,L,path_to_pari = path_to_pari, path_to_GS = path_to_GS, verbose = verbose)
    bar_vr1 = eval_chain(chain1,chain_norm1,P1-1,P1,L)
    if verbose:
      print("...done with first polynomial chain computation")
    
    if P1 == P2:
      chain_norm2 = []
      if verbose:
        print("P1 = P2 = m+1, so we only needed one polynomial chain computatio (yay!)")
    else:
      if verbose:
        print("\nentering the second polynomial chain computation...")
      (chain2, chain_norm2) = pol_chain(I_pari,x,P2-1,P2,L,path_to_pari = path_to_pari, path_to_GS = path_to_GS, verbose = verbose)
      bar_vr2 = eval_chain(chain2,chain_norm2,P2-1,P2,L)
      if verbose:
        print("...done with second polynomial chain computation")
      
    # Computing a Q larger than min_Q and such that all elements in chain_norm1 and chain_norm2 are coprime to Q
    prod_norm = lcm([abs(x.norm()) for x in chain_norm1]+[abs(x.norm()) for x in chain_norm2])
    Q = min_Q
    while gcd(Q,prod_norm) != 1:
       Q += 1
    if verbose:
        print("log(Q,2) = ", RR(log(Q,2)))
    
    # Computing v0^{P1-1} and v0^{p2-1} modulo Q 
    tmp1 = eval_chain(chain1,chain_norm1,P1-1,Q, L) ## tmp1 = v0^{P1-1}*bar(vr1) mod Q
    pow1 = mod_fast(tmp1 * inverse_mod_fast(bar_vr1, Q, L), Q, L) ## pow1 = v0^{P1-1} mod Q
    if P1 != P2:
        tmp2 = eval_chain(chain2,chain_norm2,P2-1,Q,L) ## tmp2 = v0^{P2-1}*bar(vr2) mod Q
        pow2 = mod_fast(tmp2 * inverse_mod_fast(bar_vr2, Q, L), Q, L) ## pow2 = v0^{P2-1} mod Q
                     
    # Now using the Bezout coefficients u,v, we can compute v_0**(2m) mod Q.
    if P1 == P2:
        return pow1
    else:
        ## TODO write pow_mod function for large u and v (?) -> this does not seem to be a bottelneck at the moment
        if u < 0:
            return( mod_fast(inverse_mod_fast(pow1,Q,L)^(-u) * pow2^v, Q,L) )
        elif v < 0 :
            return( mod_fast(pow1^u * inverse_mod_fast(pow2, Q, L)^(-v),Q,L))
        else:
            return( mod_fast(pow1^u * pow2^v,Q,L))


########################
## How to use
########################
#m = 64
#L.<z> = CyclotomicField(m)
#OL = L.maximal_order()

#set_random_seed(42)
#s = OL.random_element()
#I = OL.fractional_ideal(s)
#x = s*s.conjugate()

#Q = ZZ(2*max([abs(si) for si in list(s^m)]))

#res = smallpow_modQ(I,x,Q,m,2,L)
#if res == s^m:
#    print("All good: we recovered s^m!")
#else:
#    print("Something went wrong: we did not recovered s^m")
