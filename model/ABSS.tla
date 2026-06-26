---- MODULE ABSS ----

ABSSStates ==
  {"Idle", "ChallengeIssued", "EvidenceReceived", "Verified", "Authorized", "Denied", "Expired"}

VARIABLES abssState

ABSSInit ==
  abssState = "Idle"

IssueChallenge ==
  /\ abssState = "Idle"
  /\ abssState' = "ChallengeIssued"

ReceiveEvidence ==
  /\ abssState = "ChallengeIssued"
  /\ abssState' = "EvidenceReceived"

MarkVerified ==
  /\ abssState = "EvidenceReceived"
  /\ abssState' = "Verified"

Authorize ==
  /\ abssState = "Verified"
  /\ abssState' = "Authorized"

Deny ==
  /\ abssState = "Verified"
  /\ abssState' = "Denied"

Expire ==
  /\ abssState = "Authorized"
  /\ abssState' = "Expired"

ABSSTypeInvariant ==
  abssState \in ABSSStates

====