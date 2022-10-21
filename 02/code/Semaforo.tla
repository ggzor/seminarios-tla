---- MODULE Semaforo ----
EXTENDS TLC

VARIABLE color
SInit == color = "verde"
SNext == IF color = "verde"
         THEN color' = "amarillo"
         ELSE IF color = "amarillo"
              THEN color' = "rojo"
              ELSE color' = "verde"
Spec == SInit /\ [][SNext]_color

TypeInvariant == color \in {"verde", "amarillo", "rojo"}
----
THEOREM Spec => []TypeInvariant
====