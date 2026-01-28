# OnlyCommitSpec

This folder contains a TLA⁺ specification of the **EPaxos commit protocol**,
without recovery.

The commit protocol is responsible for:
- pre-accept, accept, and commit phases
- fast-path and slow-path commits
- dependency discovery for conflicting commands
- ensuring agreement and visibility guarantees

### Role in the project

This part models the commit part of the protocol, and also builds into the commit + recovery specification in another folder.

### Notes

It's possible to set an  **unsafe parameterizations** in the config file
(e.g. small N, large F/E) and get invariant violations when running the spec.

### Pratical elements

You can change the config using the .cfg file and run the spec using the run.sh file.

