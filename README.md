# Spec-EPaxos

The CommitWithRecoverySpec folder contains the full Commit + Recovery spec folder.

There are three existing specs for the execution, the commit part by itself, and the commit + recovery protocols of EPaxos,  There is also a SMRspec model in the SMRSpec folder (first step I did, mostly for training).

**To run the model**, use the following command as a template (the tla2tools jar is inncluded in the folder), or use ./run.sh :
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



### EPaxosCommitWithRecovery

This folder contains the **full EPaxos specification**

### Misc

There are also a report and a set of slides included (these are in French).
