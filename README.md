# Spec-EPaxos

The recovery protocol folder contains the full Commit + Recovery spec folder.

There are three existing modules for the execution, the commit, and the recovery protocols of EPaxos,  There is also a SMRspec model in the SMRSpec folder (first step I did, mostly for training).
The OneSystemSpec folder is an unsuccessful attempt to use modules properly in building my spec.

To run the model, use the following command as a template (the tla2tools jar is inncluded in the folder), or use ./run.sh :
java -cp PATH_TO_tla2tools.jar/tla2tools.jar tlc2.TLC SPEC_FILE_NAME.tla
The .cfg file can be modified to change the parameters with which the model is ran.

### SMRSpec

This folder contains a standalone TLA⁺ specification of a **State Machine Replication (SMR)** model.

The purpose of this part is **didactic and preparatory**:
it was written as an initial step to get familiar with TLA⁺, TLC,
and the style of modeling replicated state machines before moving on
to writing the EPaxos protocol specification.


### ExecutionSpec

This folder contains a TLA⁺ specification of the **execution protocol**
of EPaxos.

The execution protocol is responsible for executing committed commands according to the dependency graph (dep map in the code)


This specification models **execution only**, assuming that commands
and their dependency sets have already been correctly committed. (commands are still submitted and committed in the code, but we "cheat" it by using globally accessing variables)


### OnlyCommitSpec

This folder contains a TLA⁺ specification of the **EPaxos commit protocol**,
without recovery.

The commit protocol is responsible for:
- pre-accept, accept, and commit phases
- fast-path and slow-path commits
- dependency discovery for conflicting commands
- ensuring agreement and visibility guarantees


### EPaxosRecovery

This folder contains the **full EPaxos specification**, including:

- commit protocol
- recovery protocol
- ballot escalation
- validation and waiting logic

This is the most complete and complex model in the repository.

The code has the exact same code that the commit protocol had, with the recovery part added.

