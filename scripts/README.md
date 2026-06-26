# Scripts

This directory contains helper scripts used to reproduce the verification experiments.

| Script | Purpose |
|--------|---------|
| `tlc.sh` | Wrapper script for executing TLC with the desired specification and configuration files. |
| `run-tlc-deucalion.slurm` | Example Slurm batch script used to execute large verification campaigns Deucalion supercomputer. |

## Notes

- `tlc.sh` can be used on any machine with Java installed.
- `run-tlc-deucalion.slurm` is provided as a reference for Deucalion execution and may require adaptation to local cluster policies (partition, account, memory, and time limits).