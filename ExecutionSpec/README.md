# ExecutionSpec

This folder contains a TLA⁺ specification of the **execution protocol**
of EPaxos.

The execution protocol is responsible for executing committed commands according to the dependency graph (dep map in the code)


This specification models **execution only**, assuming that commands
and their dependency sets have already been correctly committed. (commands are still submitted and committed in the code, but we "cheat" it by using globally accessing variables)


### Role in the project

This part is somewhat isolated from the rest, it allows to check the execution protocol on it's own. 
It is also the easier part of EPaxos, so the first one I tackled. However, it is not exactly the most interesting to add a layer of certainty to. In that sense, it was mostly training to then tackle the commit part of the algorithm, which is also the part for which veryfing configurations is actually interesting.

### Pratical elements

You can change the config using the .cfg file and run the spec using the run.sh file.
