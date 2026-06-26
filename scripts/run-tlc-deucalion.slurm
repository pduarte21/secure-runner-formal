#!/bin/bash

#SBATCH --account=<your-account>
#SBATCH --partition=normal-arm
#SBATCH --job-name=secure-runner-tlc
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=28G
#SBATCH --time=1-00:00:00
#SBATCH --output=tlc_%j.out
#SBATCH --error=tlc_%j.err

module load Java/17

export JAVA_HEAP=24G
export TLC_WORKERS=4

./tlc.sh run \
  -s ../model/SecureRunnerHardenedModel.tla \
  -c ../model/configs/liveness.cfg \
  -- -deadlock