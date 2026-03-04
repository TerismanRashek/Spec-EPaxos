# EPaxosRecovery

This folder contains the **full EPaxos specification**, including:

- commit protocol
- recovery protocol
- ballot escalation
- validation and waiting logic

This is the complete and most complex spec in the repository.

The code has the same code that the commit protocol had, with the recovery part added.

### Role in the project

This part models the full commit with recovery part of the protocol, the idea is to run the model checker on interesting configurations to add a layer of certainty that the protocol is correct. The amount of states that the model checker must go through increases exponentially, anything greater than 2 will probably not resolve.

### Pratical elements

You can change the config using the .cfg file and run the spec using the run.sh file.



