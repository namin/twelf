(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

signature ABSMACHINE =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)

  val solve     : (int option * int option)
                  -> (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (IntSyn.Exp -> unit) -> unit

end;  (* signature ABSMACHINE *)
