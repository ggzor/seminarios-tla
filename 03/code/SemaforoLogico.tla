---- MODULE SemaforoLogico ----
EXTENDS TLC
VARIABLE color

Init == color = "verde"
Verde_Amarillo == /\ color = "verde"
                  /\ color' = "amarillo"

Amarillo_Rojo  == /\ color = "amarillo"
                  /\ color' = "rojo"

Rojo_Verde     == /\ color = "rojo"
                  /\ color' = "verde"

Next == Verde_Amarillo \/ Amarillo_Rojo \/ Rojo_Verde

Spec == Init /\ [][Next]_color

TypeInvariant == color \in {"verde", "amarillo", "rojo"}
====