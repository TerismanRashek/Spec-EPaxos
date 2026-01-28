    # Spec-EPaxos



    The recovery protocol folder contains the full Commit + Recovery spec folder.

    There are three existing modules for the execution, the commit, and the recovery protocols of EPaxos,  There is also a SMRspec model in the SMRSpec folder (first step I did, mostly for training).
    The OneSystemSpec folder is an unsuccessful attempt to use modules properly in building my spec.

    To run the model, use the following command as a template (the tla2tools jar is inncluded in the folder), or use ./run.sh :
    java -cp PATH_TO_tla2tools.jar/tla2tools.jar tlc2.TLC SPEC_FILE_NAME.tla
    the .cfg file can be modified to change the parameters with which the model is ran.

