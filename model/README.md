# Model

This directory contains the complete TLA+ specification of the Secure Runner formal model together with the TLC model-checking configurations used in the paper.

## Structure

```
model/
├── SecureRunner.tla
├── ABSS.tla
├── SecureRunnerHardenedModel.tla
└── configs/
    ├── safety.cfg
    ├── liveness.cfg
    ├── liveness_1runner.cfg
    └── liveness_without_adv.cfg
```

## Modules

### `SecureRunner.tla`

Defines the abstract Secure Runner lifecycle and execution states.

### `ABSS.tla`

Models the Attestation-Based Secret Service (ABSS) used during trust establishment.

### `SecureRunnerHardenedModel.tla`

Main specification integrating the Secure Runner lifecycle, attestation, secret leasing, execution capabilities, policy enforcement, adversarial behavior, safety invariants, and temporal properties.

## TLC Configurations

| Configuration | Purpose |
|--------------|---------|
| `safety.cfg` | Verifies all safety invariants on the complete adversarial model. |
| `liveness.cfg` | Verifies safety and liveness properties with fairness enabled on the complete adversarial model. |
| `liveness_1runner.cfg` | Small-state sanity check for liveness verification using a single runner. |
| `liveness_without_adv.cfg` | Verifies liveness in the absence of adversarial transitions. |