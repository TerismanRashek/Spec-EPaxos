# SMRSpec

This folder contains a standalone TLA⁺ specification of a **State Machine Replication (SMR)** model.

The purpose of this part is **didactic and preparatory**:
it was written as an initial step to get familiar with TLA⁺, TLC,
and the style of modeling replicated state machines before moving on
to writing the EPaxos protocol specification.

### Contents

- A simple SMR specification use global shared variables modeling:
  - command submission
  - replication across processes
  - agreement and consistency invariants
- Basic invariants expressing:
  - agreement on committed commands
  - safety properties of replicated execution
  - Liveness

### Role in the project

This model is **not used directly** by the EPaxos specifications.
Instead, it served as:
- training for TLA⁺ modeling
- a conceptual baseline for later EPaxos execution and commit models

### Pratical elements

You can change the config using the .cfg file and run the spec using the run.sh file

