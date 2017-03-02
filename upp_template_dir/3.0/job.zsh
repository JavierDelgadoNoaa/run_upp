#!/usr/bin/env zsh

# TODO generalize for different hpc systems
source /etc/profile.d/modules.sh
source /etc/profile.d/gold_moab_torque.sh
module load intel
module load szip
module load hdf5
module load netcdf/4.3.0
module load impi

mpirun -np $PBS_NP ./unipost.exe
