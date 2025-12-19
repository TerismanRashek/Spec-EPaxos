-------------------------------- MODULE Test --------------------------------
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == x < 5 /\ x' = x + 1

Spec == Init /\ [][Next]_x
============================================================

\* Modification History
\* Last modified Wed Oct 22 08:46:26 CEST 2025 by terisman
\* Created Wed Oct 22 08:39:43 CEST 2025 by terisman
