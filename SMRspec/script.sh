#!/bin/bash

TLCDIR="/home/terisman/Projet_ASR_SPEC/tlaplus/tlatools/org.lamport.tlatools"
JARGS= "-cp /home/terisman/Projet_ASR_SPEC/tlaplus/tla2tools.jar tlc2.TLC SMRspec.tla"


MODULES="SMRspec.tla"


for mod in ${MODULES};
do
    java ${JARGS} ${mod}
done
