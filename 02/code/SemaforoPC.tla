---- MODULE SemaforoPC ----
EXTENDS TLC

(*--algorithm SemaforoPC
variable color = "verde";

define
  TypeInvariant == color \in {"verde","amarillo","rojo"}
end define;

begin
  while TRUE do
    if color = "verde" then
      color := "amarillo";
    elsif color = "amarillo" then
      color := "rojo";
    else
      color := "verde";
    end if;
  end while;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "52c66dd6" /\ chksum(tla) = "e2890aa9")
VARIABLE color

(* define statement *)
TypeInvariant == color \in {"verde","amarillo","rojo"}


vars == << color >>

Init == (* Global variables *)
        /\ color = "verde"

Next == IF color = "verde"
           THEN /\ color' = "amarillo"
           ELSE /\ IF color = "amarillo"
                      THEN /\ color' = "rojo"
                      ELSE /\ color' = "verde"

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

====
