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

####################################
## This file contains a function to compute a r-th root of an
## element in a number field.
## Depending on the version of pari available through sage, it uses 
## either the built-in Sage function, or it calls pari (via sage) to
## compute the root (this is done if pari's version available via 
## sage is sufficiently recent to have the nfeltispower function).
## If the most recent function of pari is available, we gain a 
## factor 2 to 3 by using it.
#####################################

def number_field_root(x,r,L,verbose = False):
  ## Input: r in a positive integer
  ##        L is a number field
  ##        x is an element in L which is a r-th power of some element of L
  ## Output: a r-th root of x in L
  
  pari_version = pari.version()
  
  if pari_version < (2,15,0):
  ## If the version of pari available is too old, the function nfeltispower of pari won't be available, so we use the function nth_root of sage. This is 2 to 3 times slower than calling nfeltispower from pari (when it is available).
  ## This older version may also cause pari's stack to overflow when the degree of the number field is large, which results in a crash of the function
    if verbose:
      print("We use the function nth-root of sage (calling pari to factor the polynomial X^r-x in K). This is somewhat slow and can be (slightly) improved by using a more recent version of pari and the function nfeltispower.")
    res = x.nth_root(r)
    
  else:
  ## pari's version is sufficiently recent to use the function nfeltispower (but we need to call pari, this is not integrated directly in sage yet)
    if verbose:
      print("We use the function nfeltispower of pari. This is the fastest option at the moment (02/2024).")
    ## creating a repository for temporary files, in order to write the element x in a file, and have it read by pari
    tmp_dir_name = "GentrySzydlo_temporary_files"
    if not os.path.isdir("GentrySzydlo_temporary_files"): ## test if the directory already exists, and if not create it
      os.mkdir("GentrySzydlo_temporary_files")
      if verbose:
        print("(creating folder GentrySzydlo_temporary_files)")
    else:
      if verbose:
        print("(folder GentrySzydlo_temporary_files already exists, continuing)")
    ## write x, in pari format, in a file input_nfeltispower (errasing existing content if the file already existed)
    x_pari = pari(x)
    file_pari = open(tmp_dir_name+"/input_nfeltispower", "w")
    file_pari.write("x_pari = "+str(x_pari)+"; r = "+str(r)+";")
    file_pari.close()
    ## running pari's nfeltispower function inside pari's environnement
    pari('read(\"'+tmp_dir_name+'/input_nfeltispower\");')
    pari('nf = nfinit(x_pari.mod);')
    pari('is_pow = nfeltispower(nf,x_pari,r,&y_pari)') ## return 0 or 1 depending whether x_pari is a r-th power, and in case it is, put the r-th root in variable y_pari
    if pari('is_pow') == 1:
      pari('res_pari = nfbasistoalg(nf,y_pari)')
      res = L(pari('res_pari'))
    else:
      raise ValueError("%s is not a %s-th root in %s"%(x, r, L))
    
  assert(res^r == x) ##TODO: remove if it feels safe
  return res
  
################
## How to use
################

#m = 64
#K = CyclotomicField(m)
#OK = K.ring_of_integers()
#r = m
#set_random_seed(42)
#s = OK.random_element()
#x = s^m

#s2 = number_field_root(x,m,K, verbose = True)
#print("The root computed is correct:", s2^m ==x)
