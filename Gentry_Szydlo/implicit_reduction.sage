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

import os
import subprocess

#####################################################
## The main function in this file computes the implicit
## reduction part of the Gentry-Szydlo algorithm
## Namely, given as input a principal ideal I = v*OL
## (where OL is the ring of integers of a CM field L)
## and the relative norm x = v*\bar(v) of the generator,
## the algorithm outputs an implicitely reduced basis
## (w1, ..., wd) of I (d = degree(L)), i.e., 
## (w1, ..., wd) is a basis of I, and wi = v*ai with 
## ai in OL such that (a1, ..., ad) is LLL-reduced
## (note: the ai are a priori unknown, since v is not
## supposed to be known)
#####################################################


##############################
#### Auxilliary functions ####
##############################

##########
## We use pari's format for ideals, which
## makes multiplication of ideals *much* faster
## than sage's default ideal class. To convert a
## sage ideal I into a pari ideal I_pari, it is 
## sufficient to do I_pari = pari(I).
## For the other direction, we provide a function
## that converts a pari ideal into a ZZ-basis of the
## ideal in sage's format (we do not really need 
## to have a sage ideal, only its basis)
###########


def ideal_pari_to_sage_basis(I_pari, L):
  ## Input: I_pari an ideal in pari's format, L is the number field (in sage format!) in which I_pari lives
  ## Output: a list of deg(L) elements of L (in sage format!), forming a ZZ-basis of I
  nf = pari(L)
  res = []
  for v_basis in I_pari:
    v_alg = pari.nfbasistoalg(nf,v_basis)
    res += [L(v_alg)]
  return res

  
def create_Gram_matrix(basis_I,x,nf):
  ## Input: basis_I is a ZZ-basis of a principal ideal I = v*OL in OL (ring of integers of L)
  ##        (basis_I is a list of elements of OL, obtained, e.g., with I.basis() or with the ideal_pari_to_sage_basis function)
  ##        and x = v*v.conjugate()
  ##        nf is pari's format for the number field L
  ## Output: the Gram matrix G of the ideal lattice sigma(x^{-1/2}*I), where sigma is the canonical embedding (mapping L to CC^d). Note that x^{-1/2}*I is not a fractional ideal of L, it lives in L_R, but its Gram matrix is rational. The (i,j)-th coefficient of the Gram matrix is simply Tr(1/x*b_i*b_j.conjugate()), where (b_i)_i is a basis of I.
  
  x_inv_pari = pari(1/x) # pre-computing 1/x (in pari's format) to fasten futur computation
  basis_I_conj_pari = [pari.nfeltmul(nf,x_inv_pari,pari(b.conjugate()))for b in basis_I] # pre-computing conjugation and multiplication by 1/x to fasten futur computations
  basis_I_pari = [pari(b) for b in basis_I] # converting to pari's format, which makes trace computation faster
  G = Matrix(QQ,len(basis_I))
  for i in range(len(basis_I)):
    for j in range(i,len(basis_I)):
      G[i,j] = QQ(pari.nfelttrace(nf,pari.nfeltmul(nf,basis_I_pari[i], basis_I_conj_pari[j])))
      G[j,i] = G[i,j] #to avoid half the calls to the multiplication and trace function (slightly costly)
  return G
  
## The following function is used only if you want to use the flatter LLL algorithm from pari/gp version 2.16 are later, *but* your sage installation uses by default a former version of pari/gp (2.15.x of before). In this case, a path_to_pari should be specified, leading to your gp executable (running the more recent version of pari/gp)
def LLL_gram_calling_pari(G, path_to_pari, path_to_GS = "./", verbose = False):
  ## Input:  G is a Gram matrix (with rational coefficients)
  ##         path_to_pari is a string, containing the absolute or relative path to the gp executable we want to use. E.g., path_to_pari = "~/code/pari/GPDIR/bin/gp"
  ## Output: a unimodular matrix U such that G' = U.transpose() * G * U is LLL-reduced. This function does not call Sage's LLL_gram function, but directly calls pari's qflllgram function (using pari's version found at path_to_pari)
  
  # write G, in pari format, in a file input_qflllgram (errasing existing content if the file already existed)
  G_pari = pari(G)
  file_pari = open("GentrySzydlo_temporary_files/input_qflllgram", "w")
  file_pari.write("G_pari = "+str(G_pari)+";")
  file_pari.close()
  # remove file output_qflllgram is it already exists, because pari's write function append the text to an existing file (which will cause trouble whe reading it later on)
  if os.path.isfile("GentrySzydlo_temporary_files/output_qflllgram"):
    os.remove("GentrySzydlo_temporary_files/output_qflllgram")
    if verbose:
      print("(rewriting existing file GentrySzydlo_temporary_files/output_qflllgram)")
  # running some pari/gp code which computes the transformation matrix U and writes it in a file output_qflllgram
  bash_execute_pari = path_to_pari+" --quiet "+path_to_GS+"LLL_gram_pari.gp"
  subprocess.run(bash_execute_pari, shell = True, executable="/bin/bash")
  # reading the matrix computed by pari and converting it back to sage format
  pari('U_pari = read(\"GentrySzydlo_temporary_files/output_qflllgram\");')
  U = Matrix(ZZ,pari('U_pari')) # the LLL-reduced gram matrix is G' = U.transpose() * G * U
  
  return U


#######################
#### Main function ####
#######################

def implicit_reduction(I_pari,x,L, path_to_pari = None, path_to_GS = "./", verbose = False):
  ## Input:  
  ##        L is a CM field L (with ring of integers OL)
  ##        I_pari is a principal OL-ideal, generated by some v in OL, in pari's format (e.g., obtained by pari(I), with I a sage's ideal)
  ##        x = v*v.conjugate() is the relative norm of v in the totally real subfield (but x is still an element of OL for its type)
  ##        path_to_pari is a string to a potential more recent installation of pari/gp (default: None)
  ##        path_to_GS is the path from the current directory (where Sage is run) to the directory containing the Gentry-Szydlo code 
  ##          files. It is required only when path_to_pari is not None
  ##        verbose is a boolean (default: False). If set to True, the algorithm will print some intermediate values and other
  ##          informations that can be useful for debugging.
  ##
  ## Output: a list of d := degree(L) elements [s*a_1, ..., s*a_d] which form a basis of I
  ##         and such that (a_1, ..., a_d) is LLL-reduced
  
  
  ## Create the Gram matrix of the ideal lattice sigma(x^{-1/2}*I). The multiplication by x^{-1/2} is used to "erase" the impact of s on the geometry of the ideal. 
  basis_I = ideal_pari_to_sage_basis(I_pari, L)
  if(verbose):
    print("basis of the ideal computed...")
  nf = pari(L)
  G = create_Gram_matrix(basis_I,x, nf)
  
  ## Reducing the basis
  if path_to_pari is None: # use Sage's LLL_gram function
    if verbose:
      print("using sage's LLL_gram")
    U = G.LLL_gram() # the LLL-reduced gram matrix is G' = U.transpose() * G * U
  else:
    if verbose:
      print("using pari's qflllgram")
    U = LLL_gram_calling_pari(G, path_to_pari, path_to_GS = path_to_GS, verbose = verbose) # the LLL-reduced gram matrix is G' = U.transpose() * G * U
  U = U.transpose() # to change U to row convention, as is usual in Sage
  
  ## Compute a good basis of I (cf description of good basis above), 
  ## using the transformation matrix U
  res = []
  for u in U:
    tmp = L(0)
    for i in range(len(u)):
      tmp += u[i]*basis_I[i]
    res += [tmp]
    
  return res
  
################
## How to use
################

#path_to_pari = None ## Update here with your own path to gp if you want to use a specific version of pari, e.g., path_to_pari = "~/pari/GPDIR/bin/gp" 

## defining the number field and the ideal and norm element
#m = 64
#L.<z> = CyclotomicField(m)
#OL = L.maximal_order()

#set_random_seed(42)
#s = OL.random_element()

#I = OL.fractional_ideal(s)
#I_pari = pari(I)
#x = s*s.conjugate()

## running the function and printing the output
#res = implicit_reduction(I_pari,x,L, path_to_pari = path_to_pari)
#print("First implicitely reduced vector:\n", "s *", res[0]/s, "\n =",res[0] )
