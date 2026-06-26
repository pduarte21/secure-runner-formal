
---- MODULE SecureRunnerHardenedModel ----
(***************************************************************************)
(* Secure Runner Hardened Trust Model                                      *)
(*                                                                         *)
(* Formal specification of a hardened ephemeral CI/CD runner with:         *)
(*   - attestation-bound trust establishment                               *)
(*   - ephemeral secret leasing                                            *)
(*   - immutable egress policy enforcement                                 *)
(*   - fail-closed execution semantics                                     *)
(*   - adversarial replay resistance                                       *)
(*                                                                         *)
(* Threats modeled:                                                        *)
(*   - evidence replay                                                     *)
(*   - session replay                                                      *)
(*   - policy injection                                                    *)
(*   - cross-runner secret reuse                                           *)
(*   - use-after-expiry                                                    *)
(*                                                                         *)
(* Security goals:                                                         *)
(*   - no execution before trust                                           *)
(*   - no secrets without attestation                                      *)
(*   - immutable policy after authorization                                *)
(*   - revocation destroys execution capability                            *)
(*   - no cross-runner trust reuse                                         *)
(***************************************************************************)

EXTENDS SecureRunner, ABSS, Naturals, FiniteSets

CONSTANTS
  JobIds,
  RunnerIds,
  Nonces,
  SessionIds,
  Endpoints,
  Null

PolicyDecisions == {"None", "Allow", "Deny"}
TrustStates == {"None", "Active", "Expired", "Revoked"}
SecretLeaseStates == {"None", "Issued", "Consumed", "Expired", "Revoked"}

RevocationReasons == {
  "None",
  "PolicyViolation",
  "Expiry",
  "ReplayDetected",
  "Teardown",
  "SessionReplay",
  "CrossRunnerSecretReuse",
  "EvidenceVerificationFailed"
}

VARIABLES
  jobOf,
  challengeNonce,
  evidenceNonce,
  attestationValid,
  policyDecision,
  trustState,
  trustSessionId,
  trustBoundJob,
  trustBoundRunner,
  trustUsed,
  secretsGranted,
  allowedEgress,
  successfulEgress,
  blockedEgress,
  usedSessions,
  usedNonces,
  attackerKnownNonces,
  attackerKnownSessions,
  replayedEvidence,
  replayedSession,
  injectedEgress,
  evidenceRunner,
  crossRunnerSecretReuse,
  policySnapshot,
  policyLocked,
  executionCapability,
  secretLeaseState,
  revocationReason

TrustVars ==
  << trustState,
     trustSessionId,
     trustBoundJob,
     trustBoundRunner,
     trustUsed,
     usedSessions >>

SecretVars ==
  << secretsGranted,
     executionCapability,
     secretLeaseState >>

PolicyVars ==
  << policyDecision,
     allowedEgress,
     successfulEgress,
     blockedEgress,
     policySnapshot,
     policyLocked >>

AttestationVars ==
  << challengeNonce,
     evidenceNonce,
     attestationValid,
     evidenceRunner,
     usedNonces >>

AdversaryVars ==
  << attackerKnownNonces,
     attackerKnownSessions,
     replayedEvidence,
     replayedSession,
     injectedEgress,
     crossRunnerSecretReuse >>

LifecycleVars ==
  << runnerState,
     abssState,
     revocationReason >>

Vars ==
  << LifecycleVars,
     jobOf,
     TrustVars,
     SecretVars,
     PolicyVars,
     AttestationVars,
     AdversaryVars >>

(***************************************************************************)
(* Derived Security Predicates                                             *)
(***************************************************************************)
RunnerHasSecrets(r) ==
  secretsGranted[r]

(***************************************************************************)
(* Policy Semantics                                                        *)
(***************************************************************************)
PolicyIntegrity(r) ==
  /\ policyLocked[r]
  /\ allowedEgress[r] = policySnapshot[r]

(***************************************************************************)
(* Trust Semantics                                                         *)
(***************************************************************************)
IsTrustBound(r) ==
  /\ trustState[r] = "Active"
  /\ trustSessionId[r] # Null
  /\ trustBoundJob[r] = jobOf[r]
  /\ trustBoundRunner[r] = r

TrustConsistent(r) ==
  /\ IsTrustBound(r)
  /\ policyDecision[r] = "Allow"
  /\ attestationValid[r]

TrustDestroyed(r) ==
  /\ trustState[r] \in {"Revoked", "Expired", "None"}
  /\ trustSessionId[r] = Null

SessionIntegrity(r) ==
  /\ trustSessionId[r] # Null
  /\ ~replayedSession[r]

AttestationFresh(r) ==
  /\ evidenceNonce[r] = challengeNonce[r]
  /\ evidenceRunner[r] = r

(***************************************************************************)
(* Secret Lease Semantics                                                  *)
(***************************************************************************)
LeaseIssued(r) ==
  secretLeaseState[r] = "Issued"

LeaseConsumed(r) ==
  secretLeaseState[r] = "Consumed"

LeaseRevoked(r) ==
  secretLeaseState[r] \in {"Expired", "Revoked"}

SecretAccessValid(r) ==
  /\ RunnerHasSecrets(r)
  /\ TrustConsistent(r)
  /\ secretLeaseState[r] \in {"Issued", "Consumed"}

(***************************************************************************)
(* Execution Semantics                                                     *)
(***************************************************************************)
ExecutionAuthorized(r) ==
  /\ executionCapability[r]
  /\ LeaseIssued(r)
  /\ IsTrustBound(r)

ExecutionSafe(r) ==
  /\ TrustConsistent(r)
  /\ RunnerHasSecrets(r)
  /\ LeaseConsumed(r)

SecureExecutionState(r) ==
  /\ runnerState[r] = "Executing"
  /\ ExecutionSafe(r)

SecurityHealthy(r) ==
  /\ TrustConsistent(r)
  /\ PolicyIntegrity(r)
  /\ SessionIntegrity(r)
  /\ SecretAccessValid(r)

(***************************************************************************)
(* Lifecycle Semantics                                                     *)
(***************************************************************************)
RunnerAlive(r) ==
  runnerState[r] \notin {"Teardown", "Terminated"}

RunnerFailed(r) ==
  runnerState[r] = "Aborted"

RunnerTrusted(r) ==
  runnerState[r] \in {
    "Trusted",
    "SecretsReady",
    "Executing",
    "Completed"
  }

RevokedState(r) ==
  /\ trustState[r] \in {"Revoked", "Expired"}
  /\ ~executionCapability[r]

Init ==
  /\ runnerState = [r \in RunnerIds |-> "Init"]
  /\ abssState = [r \in RunnerIds |-> "Idle"]
  /\ jobOf \in [RunnerIds -> JobIds]
  /\ \A r1, r2 \in RunnerIds :
        r1 # r2 => jobOf[r1] # jobOf[r2]
  /\ challengeNonce = [r \in RunnerIds |-> Null]
  /\ evidenceNonce = [r \in RunnerIds |-> Null]
  /\ attestationValid = [r \in RunnerIds |-> FALSE]
  /\ policyDecision = [r \in RunnerIds |-> "None"]
  /\ trustState = [r \in RunnerIds |-> "None"]
  /\ trustSessionId = [r \in RunnerIds |-> Null]
  /\ trustBoundJob = [r \in RunnerIds |-> Null]
  /\ trustBoundRunner = [r \in RunnerIds |-> Null]
  /\ trustUsed = [r \in RunnerIds |-> FALSE]
  /\ secretsGranted = [r \in RunnerIds |-> FALSE]
  /\ allowedEgress = [r \in RunnerIds |-> {}]
  /\ successfulEgress = [r \in RunnerIds |-> {}]
  /\ blockedEgress = [r \in RunnerIds |-> {}]
  /\ usedSessions = {}
  /\ usedNonces = {}
  (* adversarial *)
  /\ attackerKnownNonces = {}
  /\ attackerKnownSessions = {}
  /\ replayedEvidence = [r \in RunnerIds |-> FALSE]
  /\ replayedSession = [r \in RunnerIds |-> FALSE]
  /\ injectedEgress = [r \in RunnerIds |-> {}]
  /\ evidenceRunner = [r \in RunnerIds |-> Null]
  /\ crossRunnerSecretReuse = [r \in RunnerIds |-> FALSE]
  /\ policySnapshot = [r \in RunnerIds |-> {}]
  (* hardened *)
  /\ policyLocked = [r \in RunnerIds |-> FALSE]
  /\ executionCapability = [r \in RunnerIds |-> FALSE]
  /\ secretLeaseState = [r \in RunnerIds |-> "None"]
  /\ revocationReason = [r \in RunnerIds |-> "None"]


(***************************************************************************)
(* Trusted Boot Lifecycle                                                  *)
(***************************************************************************)
SubmitAndBoot(r) ==
  /\ runnerState[r] = "Init"
  /\ runnerState' = [runnerState EXCEPT ![r] = "Booting"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

MoveToPolicy(r) ==
  /\ runnerState[r] = "Booting"
  /\ runnerState' = [runnerState EXCEPT ![r] = "WaitingForPolicy"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

(***************************************************************************)
(* Policy Authorization Lifecycle                                          *)
(***************************************************************************)
EvaluatePolicyAllow(r, es) ==
  /\ runnerState[r] = "WaitingForPolicy"
  /\ policyDecision[r] = "None"
  /\ es \subseteq Endpoints
  /\ policyDecision' = [policyDecision EXCEPT ![r] = "Allow"]
  /\ allowedEgress' = [allowedEgress EXCEPT ![r] = es]
  /\ runnerState' = [runnerState EXCEPT ![r] = "WaitingForAttestation"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

EvaluatePolicyDeny(r) ==
  /\ runnerState[r] = "WaitingForPolicy"
  /\ policyDecision[r] = "None"
  /\ policyDecision' = [policyDecision EXCEPT ![r] = "Deny"]
  /\ runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

PolicyTimeout(r) ==
  /\ runnerState[r] = "WaitingForPolicy"
  /\ runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
  /\ trustState' = [trustState EXCEPT ![r] = "Revoked"]
  /\ revocationReason' = [revocationReason EXCEPT ![r] = "Expiry"]
  /\ UNCHANGED << abssState,
                  jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision,
                  trustSessionId,
                  trustBoundJob, trustBoundRunner,
                  trustUsed, secretsGranted,
                  allowedEgress, successfulEgress,
                  blockedEgress, usedSessions,
                  usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner,
                  crossRunnerSecretReuse,
                  policySnapshot, policyLocked,
                  executionCapability, secretLeaseState >>

(***************************************************************************)
(* Attestation Lifecycle                                                   *)
(***************************************************************************)
IssueChallengeSys(r, n) ==
  /\ runnerState[r] = "WaitingForAttestation"
  /\ abssState[r] = "Idle"
  /\ n \in Nonces
  /\ n \notin usedNonces
  /\ challengeNonce' = [challengeNonce EXCEPT ![r] = n]
  /\ abssState' = [abssState EXCEPT ![r] = "ChallengeIssued"]
  /\ usedNonces' = usedNonces \cup {n}
  /\ UNCHANGED << runnerState, jobOf, evidenceNonce,
                  attestationValid, policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

ProvideEvidenceSys(r) ==
  /\ runnerState[r] = "WaitingForAttestation"
  /\ abssState[r] = "ChallengeIssued"
  /\ evidenceNonce[r] = Null
  /\ abssState' = [abssState EXCEPT ![r] = "EvidenceReceived"]
  /\ evidenceNonce' = [evidenceNonce EXCEPT ![r] = challengeNonce[r]]
  /\ evidenceRunner' = [evidenceRunner EXCEPT ![r] = r]
  /\ UNCHANGED << runnerState, jobOf, challengeNonce,
                  attestationValid, policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, crossRunnerSecretReuse, policySnapshot,
                  policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

(*
 * Accept attestation evidence only if:
 *   - nonce freshness holds
 *   - evidence is bound to the same runner
 *
 * Security goal:
 *   Prevent replayed attestation evidence from establishing trust.
 *)
VerifyEvidenceSuccess(r) ==
  /\ runnerState[r] = "WaitingForAttestation"
  /\ abssState[r] = "EvidenceReceived"
  /\ evidenceNonce[r] = challengeNonce[r]
  /\ evidenceRunner[r] = r
  /\ abssState' = [abssState EXCEPT ![r] = "Verified"]
  /\ attestationValid' = [attestationValid EXCEPT ![r] = TRUE]
  /\ UNCHANGED << runnerState, jobOf, challengeNonce, evidenceNonce,
                  policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

VerifyEvidenceFail(r) ==
  /\ runnerState[r] = "WaitingForAttestation"
  /\ abssState[r] = "EvidenceReceived"
  /\ \/ evidenceNonce[r] # challengeNonce[r]
     \/ evidenceRunner[r] # r
  /\ attestationValid' = [attestationValid EXCEPT ![r] = FALSE]
  /\ abssState' = [abssState EXCEPT ![r] = "Denied"]
  /\ runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
  /\ trustState' = [trustState EXCEPT ![r] = "Revoked"]
  /\ executionCapability' = [executionCapability EXCEPT ![r] = FALSE]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Revoked"]
  /\ revocationReason' =
        [revocationReason EXCEPT
            ![r] =
                IF replayedEvidence[r]
                THEN "ReplayDetected"
                ELSE "EvidenceVerificationFailed"
        ]
  /\ trustSessionId' = [trustSessionId EXCEPT ![r] = Null]
  /\ UNCHANGED << jobOf, challengeNonce, evidenceNonce,
                  policyDecision,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked >>

AttestationTimeout(r) ==
  /\ runnerState[r] = "WaitingForAttestation"
  /\ runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
  /\ trustState' = [trustState EXCEPT ![r] = "Revoked"]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Revoked"]
  /\ revocationReason' = [revocationReason EXCEPT ![r] = "Expiry"]
  /\ UNCHANGED <<  abssState,
                    jobOf, challengeNonce, evidenceNonce,
                    attestationValid, policyDecision,
                    trustSessionId,
                    trustBoundJob, trustBoundRunner,
                    trustUsed, secretsGranted,
                    allowedEgress, successfulEgress,
                    blockedEgress, usedSessions,
                    usedNonces, attackerKnownNonces,
                    attackerKnownSessions,
                    replayedEvidence, replayedSession,
                    injectedEgress, evidenceRunner,
                    crossRunnerSecretReuse,
                    policySnapshot, policyLocked,
                    executionCapability >>

(***************************************************************************)
(* Trust Establishment Lifecycle                                           *)
(***************************************************************************)
EstablishTrust(r, s) ==
  /\ runnerState[r] = "WaitingForAttestation"
  /\ abssState[r] = "Verified"
  /\ attestationValid[r] = TRUE
  /\ policyDecision[r] = "Allow"
  /\ s \in SessionIds
  /\ s \notin usedSessions
  /\ trustState[r] = "None"
  /\ ~trustUsed[r]
  /\ usedSessions' = usedSessions \cup {s}
  /\ abssState' = [abssState EXCEPT ![r] = "Authorized"]
  /\ runnerState' = [runnerState EXCEPT ![r] = "Trusted"]
  /\ trustState' = [trustState EXCEPT ![r] = "Active"]
  /\ trustSessionId' = [trustSessionId EXCEPT ![r] = s]
  /\ trustBoundJob' = [trustBoundJob EXCEPT ![r] = jobOf[r]]
  /\ trustBoundRunner' = [trustBoundRunner EXCEPT ![r] = r]
  /\ policySnapshot' = [policySnapshot EXCEPT ![r] = allowedEgress[r]]
  /\ policyLocked' = [policyLocked EXCEPT ![r] = TRUE]
  /\ UNCHANGED << jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress, 
                  usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  executionCapability,
                  secretLeaseState, revocationReason >>

(*
 * Secrets are released only after:
 *   - successful attestation
 *   - explicit policy authorization
 *   - trust binding establishment
 *
 * Models attestation-bound secret release.
 *)
ReleaseSecrets(r) ==
  /\ runnerState[r] = "Trusted"
  /\ abssState[r] = "Authorized"
  /\ trustState[r] = "Active"
  /\ trustBoundJob[r] = jobOf[r]
  /\ trustBoundRunner[r] = r 
  /\ ~secretsGranted[r]
  /\ runnerState' = [runnerState EXCEPT ![r] = "SecretsReady"]
  /\ secretsGranted' = [secretsGranted EXCEPT ![r] = TRUE]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Issued"]
  /\ executionCapability' = [executionCapability EXCEPT ![r] = TRUE]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked,
                  revocationReason >>

(***************************************************************************)
(* Secure Execution Lifecycle                                              *)
(***************************************************************************)

(*
 * Execution capability acts as a single-use execution token.
 *
 * Once execution begins:
 *   - capability is consumed
 *   - lease transitions to Consumed
 *   - no second execution may occur
 *)
StartExecution(r) ==
  /\ runnerState[r] = "SecretsReady"
  /\ trustState[r] = "Active"
  /\ secretsGranted[r]
  /\ executionCapability[r]
  /\ runnerState' = [runnerState EXCEPT ![r] = "Executing"]
  /\ trustUsed' = [trustUsed EXCEPT ![r] = TRUE]
  /\ executionCapability' = [executionCapability EXCEPT ![r] = FALSE]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Consumed"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked,
                  revocationReason >>

AttemptEgress(r, e) ==
  /\ runnerState[r] = "Executing"
  /\ e \in Endpoints
  /\ IF e \in allowedEgress[r]
        THEN /\ successfulEgress' = [successfulEgress EXCEPT ![r] = successfulEgress[r] \cup {e}]
             /\ UNCHANGED runnerState
             /\ UNCHANGED << trustState, trustSessionId, trustBoundJob,
                             trustBoundRunner, secretsGranted, blockedEgress, 
                             executionCapability, secretLeaseState, revocationReason >>
        ELSE /\ blockedEgress' = [blockedEgress EXCEPT ![r] = blockedEgress[r] \cup {e}]
             /\ runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
             /\ trustState' = [trustState EXCEPT ![r] = "Revoked"]
             /\ trustSessionId' = [trustSessionId EXCEPT ![r] = Null]
             /\ trustBoundJob' = [trustBoundJob EXCEPT ![r] = Null]
             /\ trustBoundRunner' = [trustBoundRunner EXCEPT ![r] = Null]
             /\ secretsGranted' = [secretsGranted EXCEPT ![r] = FALSE]
             /\ executionCapability' = [executionCapability EXCEPT ![r] = FALSE]
             /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Revoked"]
             /\ revocationReason' = [revocationReason EXCEPT ![r] = "PolicyViolation"]
             /\ UNCHANGED successfulEgress
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustUsed,
                  allowedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked >>

FinishExecution(r) ==
  /\ runnerState[r] = "Executing"
  /\ runnerState' = [runnerState EXCEPT ![r] = "Completed"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

(***************************************************************************)
(* Cleanup and Revocation Lifecycle                                        *)
(***************************************************************************)
ExpireTrust(r) ==
  /\ trustState[r] = "Active"
  /\ trustState' = [trustState EXCEPT ![r] = "Expired"]
  /\ abssState' = [abssState EXCEPT ![r] = "Expired"]
  /\ secretsGranted' = [secretsGranted EXCEPT ![r] = FALSE]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Expired"]
  /\ executionCapability' = [executionCapability EXCEPT ![r] = FALSE]
  /\ revocationReason' = [revocationReason EXCEPT ![r] = "Expiry"]
  /\ IF runnerState[r] \in {"Trusted", "SecretsReady", "Executing"}
        THEN runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
        ELSE UNCHANGED runnerState
  /\ UNCHANGED << jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked >>

Teardown(r) ==
  /\ runnerState[r] \in {"Completed", "Aborted"}
  /\ runnerState' = [runnerState EXCEPT ![r] = "Teardown"]
  /\ trustState' = [trustState EXCEPT ![r] = "Revoked"]
  /\ secretsGranted' = [secretsGranted EXCEPT ![r] = FALSE]
  /\ trustSessionId' = [trustSessionId EXCEPT ![r] = Null]
  /\ trustBoundJob' = [trustBoundJob EXCEPT ![r] = Null]
  /\ trustBoundRunner' = [trustBoundRunner EXCEPT ![r] = Null]
  /\ policyLocked' = [policyLocked EXCEPT ![r] = FALSE]
  /\ executionCapability' = [executionCapability EXCEPT ![r] = FALSE]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Revoked"]
  /\ revocationReason' = [revocationReason EXCEPT ![r] = "Teardown"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustUsed,
                  allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot >>

TerminateSys(r) ==
  /\ runnerState[r] = "Teardown"
  /\ runnerState' = [runnerState EXCEPT ![r] = "Terminated"]
  /\ trustState' = [trustState EXCEPT ![r] = "None"]
  /\ secretsGranted' = [secretsGranted EXCEPT ![r] = FALSE]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  allowedEgress, successfulEgress, blockedEgress,
                  usedSessions, usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  injectedEgress, evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

StayTerminated(r) ==
  /\ runnerState[r] = "Terminated"
  /\ UNCHANGED Vars

(***************************************************************************)
(* Adversarial Actions                                                     *)
(*                                                                         *)
(* Models an active attacker capable of:                                   *)
(*   - observing trust material                                            *)
(*   - replaying attestation evidence                                      *)
(*   - replaying trust sessions                                            *)
(*   - attempting unauthorized egress                                      *)
(*   - reusing secrets across runners                                      *)
(*                                                                         *)
(* These actions model hostile CI/CD execution environments.               *)
(***************************************************************************)
ObserveChallenge(r) ==
  /\ challengeNonce[r] # Null
  /\ attackerKnownNonces' = attackerKnownNonces \cup {challengeNonce[r]}
  /\ UNCHANGED << runnerState, abssState, jobOf,
                  challengeNonce, evidenceNonce, attestationValid,
                  policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress,
                  blockedEgress, usedSessions, usedNonces,
                  attackerKnownSessions,
                  replayedEvidence, replayedSession, injectedEgress, 
                  evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>

ReplayEvidenceAcrossRunners(src, dst, n) ==
  /\ src # dst 
  /\ runnerState[dst] = "WaitingForAttestation"
  /\ abssState[dst] = "ChallengeIssued"
  /\ evidenceNonce[dst] = Null
  /\ n \in attackerKnownNonces
  /\ evidenceNonce' = [evidenceNonce EXCEPT ![dst] = n]
  /\ abssState' = [abssState EXCEPT ![dst] = "EvidenceReceived"]
  /\ replayedEvidence' = [replayedEvidence EXCEPT ![dst] = TRUE]
  /\ evidenceRunner' = [evidenceRunner EXCEPT ![dst] = src]
  /\ revocationReason' = [revocationReason EXCEPT ![dst] = "ReplayDetected"]
  /\ UNCHANGED << runnerState, jobOf, challengeNonce,
                  attestationValid, policyDecision, trustState,
                  trustSessionId, trustBoundJob, trustBoundRunner,
                  trustUsed, secretsGranted, allowedEgress,
                  successfulEgress, blockedEgress, usedSessions,
                  usedNonces, attackerKnownNonces,
                  attackerKnownSessions,
                  replayedSession, injectedEgress, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState >>

ObserveSession(r) ==
  /\ trustSessionId[r] # Null
  /\ attackerKnownSessions' = attackerKnownSessions \cup {trustSessionId[r]}
  /\ UNCHANGED << runnerState, abssState, jobOf,
                  challengeNonce, evidenceNonce, attestationValid,
                  policyDecision, trustState, trustSessionId,
                  trustBoundJob, trustBoundRunner, trustUsed,
                  secretsGranted, allowedEgress, successfulEgress,
                  blockedEgress, usedSessions, usedNonces,
                  attackerKnownNonces,
                  replayedEvidence, replayedSession, injectedEgress, 
                  evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked, executionCapability,
                  secretLeaseState, revocationReason >>
  
ReplaySession(r, s) ==
  /\ runnerState[r] \notin {"Teardown", "Terminated"}
  /\ s \in attackerKnownSessions
  /\ trustSessionId[r] = Null
  /\ replayedSession' = [replayedSession EXCEPT ![r] = TRUE]
  /\ trustSessionId' = [trustSessionId EXCEPT ![r] = Null]
  /\ trustState' = [trustState EXCEPT ![r] = "Revoked"]
  /\ runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
  /\ secretsGranted' = [secretsGranted EXCEPT ![r] = FALSE]
  /\ executionCapability' = [executionCapability EXCEPT ![r] = FALSE]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Revoked"]
  /\ revocationReason' = [revocationReason EXCEPT ![r] = "SessionReplay"]
  /\ trustBoundJob' = [trustBoundJob EXCEPT ![r] = Null]
  /\ trustBoundRunner' = [trustBoundRunner EXCEPT ![r] = Null]
  /\ UNCHANGED << abssState, jobOf,
                  challengeNonce, evidenceNonce,
                  attestationValid, policyDecision,
                  trustUsed,
                  allowedEgress, successfulEgress,
                  blockedEgress, usedSessions,
                  usedNonces, attackerKnownNonces,
                  replayedEvidence, injectedEgress,
                  evidenceRunner,
                  attackerKnownSessions, crossRunnerSecretReuse,
                  policySnapshot, policyLocked >>

InjectEgressPolicy(r, e) ==
  /\ runnerState[r] \in {"Trusted", "SecretsReady", "Executing"}
  /\ trustState[r] = "Active"
  /\ e \in Endpoints
  /\ e \notin allowedEgress[r]
  /\ injectedEgress' = [injectedEgress EXCEPT ![r] = injectedEgress[r] \cup {e}]
  /\ blockedEgress' = [blockedEgress EXCEPT ![r] = blockedEgress[r] \cup {e}]
  /\ runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
  /\ trustState' = [trustState EXCEPT ![r] = "Revoked"]
  /\ secretsGranted' = [secretsGranted EXCEPT ![r] = FALSE]
  /\ trustSessionId' = [trustSessionId EXCEPT ![r] = Null]
  /\ trustBoundJob' = [trustBoundJob EXCEPT ![r] = Null]
  /\ trustBoundRunner' = [trustBoundRunner EXCEPT ![r] = Null]
  /\ executionCapability' = [executionCapability EXCEPT ![r] = FALSE]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![r] = "Revoked"]
  /\ revocationReason' = [revocationReason EXCEPT ![r] = "PolicyViolation"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustUsed,
                  allowedEgress, successfulEgress, usedSessions,
                  usedNonces, attackerKnownNonces, attackerKnownSessions,
                  replayedEvidence, replayedSession,
                  evidenceRunner, crossRunnerSecretReuse,
                  policySnapshot, policyLocked >>

ReuseSecretsAcrossRunners(src, dst) ==
  /\ src \in RunnerIds
  /\ dst \in RunnerIds
  /\ src # dst
  /\ secretsGranted[src]
  /\ trustState[src] = "Active"
  /\ runnerState[dst] \notin {"Teardown", "Terminated"}
  /\ secretsGranted' = [secretsGranted EXCEPT ![dst] = FALSE]
  /\ trustState' = [trustState EXCEPT ![dst] = "Revoked"]
  /\ trustSessionId' = [trustSessionId EXCEPT ![dst] = Null]
  /\ trustBoundJob' = [trustBoundJob EXCEPT ![dst] = Null]
  /\ trustBoundRunner' = [trustBoundRunner EXCEPT ![dst] = Null]
  /\ crossRunnerSecretReuse' = [crossRunnerSecretReuse EXCEPT ![dst] = TRUE]
  /\ runnerState' = [runnerState EXCEPT ![dst] = "Aborted"]
  /\ executionCapability' = [executionCapability EXCEPT ![dst] = FALSE]
  /\ secretLeaseState' = [secretLeaseState EXCEPT ![dst] = "Revoked"]
  /\ revocationReason' = [revocationReason EXCEPT ![dst] = "CrossRunnerSecretReuse"]
  /\ UNCHANGED << abssState, jobOf,
                  challengeNonce, evidenceNonce,
                  attestationValid, policyDecision,
                  trustUsed, allowedEgress,
                  successfulEgress, blockedEgress,
                  usedSessions, usedNonces,
                  attackerKnownNonces,
                  attackerKnownSessions,
                  replayedEvidence,
                  replayedSession,
                  injectedEgress,
                  evidenceRunner, policySnapshot, 
                  policyLocked >>
  
RaceUseAfterExpiry(r) ==
  /\ runnerState[r] = "SecretsReady"
  /\ trustState[r] \in {"Expired", "Revoked"}
  /\ secretsGranted[r]
  /\ runnerState' = [runnerState EXCEPT ![r] = "Aborted"]
  /\ revocationReason' = [revocationReason EXCEPT ![r] = "Expiry"]
  /\ UNCHANGED << abssState, jobOf, challengeNonce, evidenceNonce,
                  attestationValid, policyDecision, trustState,
                  trustSessionId, trustBoundJob, trustBoundRunner,
                  secretsGranted, allowedEgress, successfulEgress,
                  blockedEgress, usedSessions, usedNonces,
                  attackerKnownNonces, attackerKnownSessions,
                  replayedEvidence, replayedSession, injectedEgress,
                  evidenceRunner, crossRunnerSecretReuse, policySnapshot,
                  policyLocked, executionCapability,
                  secretLeaseState, trustUsed >>

(***************************************************************************)
(* Trusted System Transitions                                              *)
(***************************************************************************)
TrustedNext ==
  \E r \in RunnerIds:
    \/ SubmitAndBoot(r)
    \/ MoveToPolicy(r)
    \/ \E es \in SUBSET Endpoints :
         EvaluatePolicyAllow(r, es)
    \/ EvaluatePolicyDeny(r)
    \/ \E n \in Nonces :
         IssueChallengeSys(r, n)
    \/ ProvideEvidenceSys(r)
    \/ VerifyEvidenceSuccess(r)
    \/ VerifyEvidenceFail(r)
    \/ \E s \in SessionIds :
         EstablishTrust(r, s)
    \/ ReleaseSecrets(r)
    \/ StartExecution(r)
    \/ \E e \in Endpoints :
         AttemptEgress(r, e)
    \/ AttestationTimeout(r)
    \/ PolicyTimeout(r)
    
(***************************************************************************)
(* Lifecycle and Cleanup Transitions                                       *)
(***************************************************************************)
LifecycleNext ==
  \E r \in RunnerIds:
    \/ FinishExecution(r)
    \/ ExpireTrust(r)
    \/ Teardown(r)
    \/ TerminateSys(r)
    \/ StayTerminated(r)
    
(***************************************************************************)
(* Adversarial Transitions                                                 *)
(***************************************************************************)
AdversaryNext ==
  \/ \E r \in RunnerIds:
       \/ ObserveChallenge(r)
       \/ ObserveSession(r)
       \/ \E s \in SessionIds:
            ReplaySession(r, s)
       \/ \E e \in Endpoints:
            InjectEgressPolicy(r, e)
       \/ RaceUseAfterExpiry(r)
  \/ \E src, dst \in RunnerIds:
       \/ \E n \in Nonces:
            ReplayEvidenceAcrossRunners(src, dst, n)
       \/ ReuseSecretsAcrossRunners(src, dst)

Next ==
  \/ TrustedNext
  \/ LifecycleNext
  \/ AdversaryNext

(***************************************************************************)
(* Core Specification                                                       *)
(***************************************************************************)

Spec ==
  Init /\ [][Next]_Vars

(***************************************************************************)
(* Fairness Assumptions                                                     *)
(***************************************************************************)

IssueSomeChallenge(r) ==
  \E n \in Nonces :
    IssueChallengeSys(r, n)

EstablishSomeTrust(r) ==
  \E s \in SessionIds :
    EstablishTrust(r, s)

Fairness ==
  \A r \in RunnerIds :
    /\ WF_Vars(MoveToPolicy(r))
    /\ WF_Vars(IssueSomeChallenge(r))
    /\ WF_Vars(ProvideEvidenceSys(r))
    /\ WF_Vars(VerifyEvidenceSuccess(r))
    /\ WF_Vars(VerifyEvidenceFail(r))
    /\ WF_Vars(EstablishSomeTrust(r))
    /\ WF_Vars(ReleaseSecrets(r))
    /\ WF_Vars(StartExecution(r))
    /\ WF_Vars(FinishExecution(r))
    /\ WF_Vars(Teardown(r))
    /\ WF_Vars(TerminateSys(r))

(***************************************************************************)
(* Executable Specification                                                 *)
(***************************************************************************)

SystemSpec ==
  Spec /\ Fairness

(***************************************************************************)
(* Type and Domain Invariants                                               *)
(***************************************************************************)

TypeInvariant == 
  /\ runnerState \in [RunnerIds -> RunnerStates]
  /\ abssState \in [RunnerIds -> ABSSStates]
  /\ jobOf \in [RunnerIds -> JobIds]
  /\ challengeNonce \in [RunnerIds -> Nonces \cup {Null}]
  /\ evidenceNonce \in [RunnerIds -> Nonces \cup {Null}]
  /\ attestationValid \in [RunnerIds -> BOOLEAN]
  /\ policyDecision \in [RunnerIds -> PolicyDecisions]
  /\ trustState \in [RunnerIds -> TrustStates]
  /\ trustSessionId \in [RunnerIds -> SessionIds \cup {Null}]
  /\ trustBoundJob \in [RunnerIds -> JobIds \cup {Null}]
  /\ trustBoundRunner \in [RunnerIds -> RunnerIds \cup {Null}]
  /\ trustUsed \in [RunnerIds -> BOOLEAN]
  /\ secretsGranted \in [RunnerIds -> BOOLEAN]
  /\ allowedEgress \in [RunnerIds -> SUBSET Endpoints]
  /\ successfulEgress \in [RunnerIds -> SUBSET Endpoints]
  /\ blockedEgress \in [RunnerIds -> SUBSET Endpoints]
  /\ usedSessions \subseteq SessionIds
  /\ usedNonces \subseteq Nonces
  /\ attackerKnownNonces \subseteq Nonces
  /\ attackerKnownSessions \subseteq SessionIds
  /\ replayedEvidence \in [RunnerIds -> BOOLEAN]
  /\ replayedSession \in [RunnerIds -> BOOLEAN]
  /\ injectedEgress \in [RunnerIds -> SUBSET Endpoints]
  /\ evidenceRunner \in [RunnerIds -> RunnerIds \cup {Null}]
  /\ crossRunnerSecretReuse \in [RunnerIds -> BOOLEAN ]
  /\ policySnapshot \in [RunnerIds -> SUBSET Endpoints]
  /\ policyLocked \in [RunnerIds -> BOOLEAN]
  /\ executionCapability \in [RunnerIds -> BOOLEAN]
  /\ secretLeaseState \in [RunnerIds -> SecretLeaseStates]
  /\ revocationReason \in [RunnerIds -> RevocationReasons]

Inv_UniqueJobAssignment ==
  \A r1, r2 \in RunnerIds :
    r1 # r2 => jobOf[r1] # jobOf[r2]

Inv_UniqueActiveSessions ==
  \A r1, r2 \in RunnerIds :
    r1 # r2 =>
      ~(trustSessionId[r1] # Null /\
        trustSessionId[r2] # Null /\
        trustSessionId[r1] = trustSessionId[r2])

Inv_UniqueActiveNonces ==
  \A r1, r2 \in RunnerIds :
    r1 # r2 =>
      ~(challengeNonce[r1] # Null /\
        challengeNonce[r2] # Null /\
        challengeNonce[r1] = challengeNonce[r2])

FoundationInvariants ==
  /\ TypeInvariant
  /\ Inv_UniqueJobAssignment
  /\ Inv_UniqueActiveSessions
  /\ Inv_UniqueActiveNonces

(***************************************************************************)
(* Trust and Attestation Invariants                                         *)
(***************************************************************************)

Inv_ActiveTrustIsBound ==
  \A r \in RunnerIds :
    trustState[r] = "Active" =>
      IsTrustBound(r)

Inv_UsedActiveTrustIsBound ==
  \A r \in RunnerIds :
    trustUsed[r] /\ trustState[r] = "Active" =>
      IsTrustBound(r)

Inv_NoExecBeforeTrust ==
  \A r \in RunnerIds : 
    runnerState[r] = "Executing" =>
      SecureExecutionState(r)

Inv_NoSecretsBeforeTrust ==
  \A r \in RunnerIds :
    RunnerHasSecrets(r) =>
      /\ IsTrustBound(r)
      /\ runnerState[r] \in {
            "SecretsReady", 
            "Executing",
            "Completed"
        }

Inv_Freshness ==
  \A r \in RunnerIds :
    attestationValid[r] => 
      AttestationFresh(r)

Inv_EvidenceRunnerBinding ==
  \A r \in RunnerIds :
    attestationValid[r] => evidenceRunner[r] = r

TrustInvariants ==
  /\ Inv_ActiveTrustIsBound
  /\ Inv_UsedActiveTrustIsBound
  /\ Inv_NoExecBeforeTrust
  /\ Inv_NoSecretsBeforeTrust
  /\ Inv_Freshness
  /\ Inv_EvidenceRunnerBinding

(***************************************************************************)
(* Secret Lease and Capability Invariants                                   *)
(***************************************************************************)

Inv_ExecutionCapabilitySingleUse ==
  \A r \in RunnerIds :
    executionCapability[r] =>
      /\ runnerState[r] = "SecretsReady"
      /\ LeaseIssued(r)
      /\ IsTrustBound(r)

Inv_ConsumedLeaseCannotExecuteAgain ==
  \A r \in RunnerIds :
    LeaseConsumed(r) =>
      ~executionCapability[r]

Inv_NoSecretsWithRevokedLease ==
  \A r \in RunnerIds :
    LeaseRevoked(r) =>
      ~RunnerHasSecrets(r)

Inv_ExecutionRequiresConsumedLease ==
  \A r \in RunnerIds :
    runnerState[r] = "Executing" =>
      LeaseConsumed(r)

Inv_RevokedLeaseNoRecovery ==
  \A r \in RunnerIds :
    LeaseRevoked(r) =>
      /\ ~executionCapability[r]
      /\ ~RunnerHasSecrets(r)

CapabilityInvariants ==
  /\ Inv_ExecutionCapabilitySingleUse
  /\ Inv_ConsumedLeaseCannotExecuteAgain
  /\ Inv_NoSecretsWithRevokedLease
  /\ Inv_ExecutionRequiresConsumedLease
  /\ Inv_RevokedLeaseNoRecovery

(***************************************************************************)
(* Network and Policy Invariants                                            *)
(***************************************************************************)

Inv_EgressAuthorized ==
  \A r \in RunnerIds :
    successfulEgress[r] \subseteq allowedEgress[r]

Inv_BlockedEgressFailsClosed ==
  \A r \in RunnerIds :
    blockedEgress[r] # {} =>
      runnerState[r] \in {"Aborted", "Teardown", "Terminated"}

Inv_NoEgressAmbiguity ==
  \A r \in RunnerIds :
    successfulEgress[r] \cap blockedEgress[r] = {}

Inv_NoPolicyMutationAfterTrust ==
  \A r \in RunnerIds :
    trustState[r] = "Active" =>
      allowedEgress[r] = policySnapshot[r]

Inv_PolicyLockedImmutable ==
  \A r \in RunnerIds :
    policyLocked[r] =>
      PolicyIntegrity(r)

Inv_PolicyLockImpliesEstablishedTrust ==
  \A r \in RunnerIds :
    policyLocked[r] =>
      trustState[r] \in {
        "Active",
        "Expired",
        "Revoked"
      }

PolicyEgressInvariants ==
  /\ Inv_EgressAuthorized
  /\ Inv_BlockedEgressFailsClosed
  /\ Inv_NoEgressAmbiguity
  /\ Inv_NoPolicyMutationAfterTrust
  /\ Inv_PolicyLockedImmutable
  /\ Inv_PolicyLockImpliesEstablishedTrust

(***************************************************************************)
(* Isolation Invariants                                                     *)
(***************************************************************************)

Inv_NoCrossRunnerTrustBinding ==
  \A r1, r2 \in RunnerIds :
    r1 # r2 =>
      ~( trustBoundJob[r1] = jobOf[r2]
         /\ trustState[r1] = "Active" )

Inv_NoCrossRunnerSecretLeak ==
  \A r1, r2 \in RunnerIds :
    r1 # r2 =>
      ~( secretsGranted[r1]
         /\ trustBoundJob[r1] = jobOf[r2] )

Inv_NoCrossRunnerSecretReuse ==
  \A r \in RunnerIds :
    crossRunnerSecretReuse[r] =>
      /\ ~RunnerHasSecrets(r)
      /\ trustState[r] # "Active"
      /\ trustSessionId[r] = Null

IsolationInvariants ==
  /\ Inv_NoCrossRunnerTrustBinding
  /\ Inv_NoCrossRunnerSecretLeak
  /\ Inv_NoCrossRunnerSecretReuse

(***************************************************************************)
(* Lifecycle and Fail-Closed Invariants                                     *)
(***************************************************************************)

Inv_TrustDestroyed ==
  \A r \in RunnerIds :
    runnerState[r] \in {"Teardown", "Terminated"} =>
      /\ ~RunnerHasSecrets(r)
      /\ TrustDestroyed(r)

Inv_TerminatedIsQuiescent ==
  \A r \in RunnerIds :
    runnerState[r] = "Terminated" =>
      /\ trustState[r] = "None"
      /\ ~secretsGranted[r]
      /\ trustSessionId[r] = Null
      /\ trustBoundJob[r] = Null
      /\ trustBoundRunner[r] = Null

Inv_AbortIsSafe ==
  \A r \in RunnerIds :
    RunnerFailed(r) =>
      /\ ~RunnerHasSecrets(r)
      /\ trustState[r] \in {
            "Revoked",
            "Expired",
            "None"
        } 

Inv_NoUseAfterTrustExpiry ==
  \A r \in RunnerIds :
    trustState[r] \in {"Expired", "Revoked"} =>
      /\ runnerState[r] # "Executing"
      /\ ~RunnerHasSecrets(r)

Inv_RevokedTrustNeverReactivates ==
  \A r \in RunnerIds :
    trustState[r] \in {"Revoked", "Expired"} =>
      runnerState[r] \notin {
        "Trusted",
        "SecretsReady",
        "Executing"
      }

Inv_TerminatedNoCapabilities ==
  \A r \in RunnerIds :
    runnerState[r] = "Terminated" =>
      /\ ~executionCapability[r]
      /\ secretLeaseState[r] \in {
            "Revoked",
            "Expired",
            "None"
         }
      /\ ~policyLocked[r]

LifecycleInvariants ==
  /\ Inv_TrustDestroyed
  /\ Inv_TerminatedIsQuiescent
  /\ Inv_AbortIsSafe
  /\ Inv_NoUseAfterTrustExpiry
  /\ Inv_RevokedTrustNeverReactivates
  /\ Inv_TerminatedNoCapabilities

(***************************************************************************)
(* Adversarial Invariants                                                   *)
(***************************************************************************)

Inv_NoTrustFromReplayedEvidence ==
  \A r \in RunnerIds :
    replayedEvidence[r] =>
      trustState[r] # "Active"

Inv_NoTrustFromReplayedSession ==
  \A r \in RunnerIds :
    replayedSession[r] =>
      trustState[r] # "Active"

Inv_NoInjectedEgressAllowed ==
  \A r \in RunnerIds :
    injectedEgress[r] \cap successfulEgress[r] = {}

Inv_ReplayEvidenceForcesRevocation ==
  \A r \in RunnerIds :
    replayedEvidence[r] =>
      trustState[r] # "Active"

Inv_ReplayedSessionForcesAbort ==
  \A r \in RunnerIds :
    replayedSession[r] =>
      /\ trustState[r] # "Active"
      /\ runnerState[r] \in {
            "Aborted",
            "Teardown",
            "Terminated"
         }

AdversarialInvariants ==
  /\ Inv_NoTrustFromReplayedEvidence
  /\ Inv_NoTrustFromReplayedSession
  /\ Inv_NoInjectedEgressAllowed
  /\ Inv_ReplayEvidenceForcesRevocation
  /\ Inv_ReplayedSessionForcesAbort

(***************************************************************************)
(* Hardened Execution Invariants                                            *)
(***************************************************************************)

Inv_ExecutingRunnerIsFullyConsistent ==
  \A r \in RunnerIds :
    runnerState[r] = "Executing" =>
      /\ SecureExecutionState(r)
      /\ PolicyIntegrity(r)
      /\ SessionIntegrity(r)
      /\ AttestationFresh(r)

Inv_ExecutionRequiresHealthySecurity ==
  \A r \in RunnerIds :
    runnerState[r] = "Executing" =>
      SecurityHealthy(r)

Inv_TrustUseOnlyAfterExecutionStarted ==
  \A r \in RunnerIds :
    trustUsed[r] =>
      runnerState[r] \in {"Executing", "Completed", "Aborted", "Teardown", "Terminated"}

HardenedExecutionInvariants ==
  /\ Inv_ExecutingRunnerIsFullyConsistent
  /\ Inv_ExecutionRequiresHealthySecurity
  /\ Inv_TrustUseOnlyAfterExecutionStarted

(***************************************************************************)
(* All Safety Invariants                                                    *)
(***************************************************************************)

SafetyInvariants ==
  /\ FoundationInvariants
  /\ TrustInvariants
  /\ CapabilityInvariants
  /\ PolicyEgressInvariants
  /\ IsolationInvariants
  /\ LifecycleInvariants
  /\ AdversarialInvariants
  /\ HardenedExecutionInvariants

(***************************************************************************)
(* Lifecycle Temporal Properties                                            *)
(***************************************************************************)

EventuallyTerminatesAfterAbort ==
  \A r \in RunnerIds :
    runnerState[r] = "Aborted" ~>
      runnerState[r] = "Terminated"

EventuallyTerminatesAfterCompleted ==
  \A r \in RunnerIds :
    runnerState[r] = "Completed" ~>
      runnerState[r] = "Terminated"

ExecutionEventuallyEnds ==
  \A r \in RunnerIds :
    runnerState[r] = "Executing" ~>
      runnerState[r] \in {
        "Completed",
        "Aborted",
        "Teardown",
        "Terminated"
      }

LifecycleTemporalProperties ==
  /\ EventuallyTerminatesAfterAbort
  /\ EventuallyTerminatesAfterCompleted
  /\ ExecutionEventuallyEnds

(***************************************************************************)
(* Trust and Secret Temporal Properties                                     *)
(***************************************************************************)

SecretsEventuallyRevokedAfterCompletionOrAbort ==
  \A r \in RunnerIds :
    (secretsGranted[r] /\ runnerState[r] \in {"Completed", "Aborted"}) ~>
      ~secretsGranted[r]

TrustEventuallyDestroyedAfterAbort ==
  \A r \in RunnerIds :
    runnerState[r] = "Aborted" ~>
      trustState[r] \in {
        "Revoked",
        "Expired",
        "None"
      }

TrustEventuallyDestroyedAfterCompleted ==
  \A r \in RunnerIds :
    runnerState[r] = "Completed" ~>
      trustState[r] \in {
        "Revoked",
        "None"
      }

LeaseEventuallyClosedAfterCompletionOrAbort ==
  \A r \in RunnerIds :
    (secretLeaseState[r] \in {"Issued", "Consumed"} /\
     runnerState[r] \in {"Completed", "Aborted"}) ~>
      secretLeaseState[r] \in {"Expired", "Revoked"}

TrustTemporalProperties ==
  /\ SecretsEventuallyRevokedAfterCompletionOrAbort
  /\ TrustEventuallyDestroyedAfterAbort
  /\ TrustEventuallyDestroyedAfterCompleted
  /\ LeaseEventuallyClosedAfterCompletionOrAbort

(***************************************************************************)
(* Adversarial Temporal Properties                                          *)
(***************************************************************************)

ReplayEventuallyHandled ==
  \A r \in RunnerIds :
    replayedEvidence[r] ~>
      runnerState[r] \in {"Aborted", "Teardown", "Terminated"}

SessionReplayEventuallyTerminated ==
  \A r \in RunnerIds :
    replayedSession[r] ~>
      runnerState[r] = "Terminated"

AdversarialTemporalProperties ==
  /\ ReplayEventuallyHandled
  /\ SessionReplayEventuallyTerminated

(***************************************************************************)
(* All Temporal Properties                                                  *)
(***************************************************************************)

TemporalProperties ==
  /\ LifecycleTemporalProperties
  /\ TrustTemporalProperties
  /\ AdversarialTemporalProperties

HardenedSpec ==
  SystemSpec

NextNoAdversary ==
  \/ TrustedNext
  \/ LifecycleNext

LivenessSpec ==
  Init /\ [][Next]_Vars /\ Fairness

LivenessWithoutAdversary ==
  Init /\ [][NextNoAdversary]_Vars /\ Fairness

====
