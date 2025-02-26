/*
##########
# Copyright 2024, Guilhem Mureau, Alice Pellet-Mary, Heorhii Pliatsok,
# Alexandre Wallet


* This file is part of the algorithm to solve Module-LIP in rank 2
* over totally real fields, called for referencing reason
* ModLipAttack. ModLipAttack is free software: you can redistribute it
* and/or modify it under the terms of the GNU Affero Public License as
* published by the Free Software Foundation, either version 3 of the
* License, or (at your option) any later version.  ModLipAttack is
* distributed in the hope that it will be useful, but WITHOUT ANY
* WARRANTY; without even the implied warranty of MERCHANTABILITY or
* FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero Public License
* for more details.  You should have received a copy of the GNU Affero
* Public License along with ModLipAttack. If not, see
* <https://www.gnu.org/licenses/>


##########
*/

/* This short pari script reads the matrix G produced by the sage function implicit_reduction_pari, reduces it using pari's LLL algorithm, and writes the output in a file, to be read back by the function implicit_reduction_pari */


/* Setting a limit on the stack that pari is allowed to use.
The setting below puts this limit to 4GB of RAM and 1GB per thread.
Reduce it if your computer cannot stand it, or increase it if you want
to reach larger dimensions and get a "PARI stack overflow" error. */
default(parisizemax,4*2^30)
default(threadsizemax,2^30)

/* reading the input matrix */
tmp_dir_name = "GentrySzydlo_temporary_files"
read(concat(tmp_dir_name,"/input_qflllgram"));

/* reducing the matrix using qflllgram */
U_pari = qflllgram(G_pari);

/* writing the result in a file */
write(concat(tmp_dir_name, "/output_qflllgram"), U_pari);

/* exiting pari */
\q
