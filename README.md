# Secure Runner Formal Model

This repository contains the official TLA+ specification accompanying the paper:

> **Adversarially Verified Ephemeral Trust for Secure CI/CD Runners**

The model formalizes a lifecycle-oriented Secure Runner architecture for zero-trust CI/CD environments and provides the complete artifacts required to reproduce the verification results reported in the paper.

---

## Overview

The specification models trusted execution as an authorization lifecycle spanning:

- runner provisioning;
- policy authorization;
- remote attestation;
- trust establishment;
- ephemeral secret release;
- execution authorization;
- policy-constrained execution;
- fail-closed revocation;
- teardown.

Rather than treating trust as a static property, the model explicitly captures how trust evolves throughout the complete execution lifecycle under adversarial conditions.

---

## Security Features

The specification models:

- attestation-bound trust establishment;
- ephemeral secret leasing;
- immutable policy enforcement;
- consumable execution capabilities;
- fail-closed revocation semantics;
- replay-resistant authorization;
- runner isolation.

---

## Adversarial Model

The model explicitly represents the following attack classes:

- evidence replay;
- session replay;
- unauthorized policy injection;
- cross-runner secret reuse;
- use-after-expiry execution.

These adversarial behaviors are integrated directly into the state-space explored by TLC.

---

## Verification

The hardened specification verifies:

- **38 safety invariants**
- **9 temporal (liveness) properties**

covering:

- trust establishment;
- attestation freshness;
- authorization validity;
- secret lifecycle management;
- execution capability semantics;
- immutable policy enforcement;
- runner isolation;
- fail-closed revocation;
- adversarial resilience.

No violations were found for the reported verification configurations.

---

## Repository Structure

```
.
├── model/          # TLA+ specifications and TLC configurations
├── scripts/        # helper scripts
├── results/        # verification outputs
├── tools/          # bundled verification tools
├── README.md
├── LICENSE
└── CITATION.cff
```

---

## Requirements

- Java 17 or newer
- TLA+ Tools (bundled under `tools/`)

---

## Reproducing the Results

Run TLC directly:

```bash
java -jar tools/tlc/tla2tools.jar \
    -config model/configs/liveness.cfg \
    model/SecureRunnerHardenedModel.tla
```

or use the helper script:

```bash
./scripts/tlc.sh run -s model/SecureRunnerHardenedModel.tla -c model/configs/liveness.cfg
```

The expected outcome is successful verification of all safety invariants and temporal properties.

---

## Paper

If you use this repository, please cite:

> *Adversarially Verified Ephemeral Trust for Secure CI/CD Runners*

(BibTeX will be added upon publication.)

---

## License

Released under the MIT License.
