---- MODULE SecureRunner ----
EXTENDS Naturals

RunnerStates ==
  {"Init", "Booting", "WaitingForPolicy", "WaitingForAttestation",
   "Trusted", "SecretsReady", "Executing", "Completed",
   "Aborted", "Teardown", "Terminated"}

VARIABLES runnerState

RunnerInit ==
  runnerState = "Init"

BootRunner ==
  /\ runnerState = "Init"
  /\ runnerState' = "Booting"

WaitForPolicy ==
  /\ runnerState = "Booting"
  /\ runnerState' = "WaitingForPolicy"

WaitForAttestation ==
  /\ runnerState = "WaitingForPolicy"
  /\ runnerState' = "WaitingForAttestation"

MarkTrusted ==
  /\ runnerState = "WaitingForAttestation"
  /\ runnerState' = "Trusted"

MarkSecretsReady ==
  /\ runnerState = "Trusted"
  /\ runnerState' = "SecretsReady"

StartExecutionLocal ==
  /\ runnerState = "SecretsReady"
  /\ runnerState' = "Executing"

CompleteExecution ==
  /\ runnerState = "Executing"
  /\ runnerState' = "Completed"

AbortExecution ==
  /\ runnerState \in {"WaitingForPolicy", "WaitingForAttestation", "Trusted", "SecretsReady", "Executing"}
  /\ runnerState' = "Aborted"

BeginTeardown ==
  /\ runnerState \in {"Completed", "Aborted"}
  /\ runnerState' = "Teardown"

Terminate ==
  /\ runnerState = "Teardown"
  /\ runnerState' = "Terminated"

RunnerTypeInvariant ==
  runnerState \in RunnerStates

====