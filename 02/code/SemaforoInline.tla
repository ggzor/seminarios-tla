---- MODULE SemaforoInline ----
EXTENDS TLC, Naturals 

VARIABLE color
Spec == (color = "verde") /\ [][
IF color = "verde"
         THEN color' = "amarillo"
         ELSE IF color = "amarillo"
              THEN color' = "rojo"
              ELSE color' = "verde"
]_color

TypeInvariant == color \in {"verde", "amarillo", "rojo"}
----
THEOREM Spec => []TypeInvariant
====