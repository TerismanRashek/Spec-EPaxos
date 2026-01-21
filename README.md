# Spec-EPaxos

There are three existing modules for the execution, the commit, and the recovery protocols of EPaxos, The recovery protocol folder contains the full Commit + Recovery spec. There is also a SMRspec model in the SMRSpec folder (first step I did, mostly for training).
The OneSystemSpec folder is an unsuccessful attempt to use modules properly in building my spec.

To run the model, use the following command as a template (you will need the tla2tools jar downloaded on your system) :
java -cp $PATH_TO_tla2tools.jar$/tla2tools.jar tlc2.TLC $SPEC_FILE_NAME$.tla
the .cfg file can be modified to change the parameters with which the model is ran.

