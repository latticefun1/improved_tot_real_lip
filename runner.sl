#!/bin/bash

#SBATCH --job-name=cof1

#SBATCH --ntasks=1 --nodes=1

#SBATCH --mem-per-cpu=64G

#SBATCH --partition=longq

#SBATCH --time=15-00:00:00

#SBATCH  -o  results__%j.%N.%a.out
#SBATCH -e  err_results_%j.err

module load Anaconda3
export CONDA_ENVS_PATH=/home/$USER/miniforge3/envs/
source activate sage
sage --version
sage experiments2.sage
