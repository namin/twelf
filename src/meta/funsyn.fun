(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor FunSyn (structure IntSyn' : INTSYN) : FUNSYN= 
struct
  structure IntSyn = IntSyn'

  exception Error of string 


  type label = int      
  type name = string
  type lemma = int 

  datatype LabelDec =			(* ContextBody                *)
    LabelDec of name * IntSyn.dctx * IntSyn.dctx
					(* BB ::= l: SOME Theta. Phi  *)

  datatype CtxBlock =                   (* ContextBlocks              *)
    CtxBlock of 
      label option * IntSyn.dctx	(* B ::= l : Phi              *) 

  datatype LFDec =			(* Contexts                   *)
    Prim of IntSyn.Dec			(* LD ::= x :: A              *)
  | Block of CtxBlock			(*      | B                   *)

  type lfctx = LFDec IntSyn.Ctx         (* Psi ::= . | Psi, LD        *) 

  datatype For =			(* Formulas                   *)
    All of LFDec * For			(* F ::= All LD. F            *)
  | Ex  of IntSyn.Dec * For		(*     | Ex  D. F             *)
  | True				(*     | T                    *)
  | TClo of (For * IntSyn.Sub)		(*     | F [s]                *)
  | And of For * For                    (*     | F1 ^ F2              *)

  datatype Pro =			(* Programs                   *)
    Lam of LFDec * Pro			(* P ::= lam LD. P            *)
  | Inx of IntSyn.Exp * Pro             (*     | <M, P>               *)
  | Unit				(*     | <>                   *)
  | Rec of MDec * Pro			(*     | mu xx. P             *)
  | Let of Decs * Pro			(*     | let Ds in P          *)
  | Case of Opts                        (*     | case O               *)
  | Pair of Pro * Pro                   (*     | <P1, P2>             *)

  and Opts =				(* Option list                *)
    Opts of (lfctx * IntSyn.Sub * Pro) list
                                        (* O ::= (Psi' |> s |-> P     *)

  and MDec =				(* Meta Declaration:          *)
    MDec of name option * For		(* DD ::= xx : F              *)
 
  and Decs =				(* Declarations               *)
    Empty				(* Ds ::= .                   *)
  | Split of int * Decs			(*      | <x, yy> = P, Ds     *)
  | New of CtxBlock * Decs		(*      | nu B. Ds            *)
  | App of (int * IntSyn.Exp) * Decs	(*      | xx = yy M, Ds       *)
  | PApp of (int * int) * Decs		(*      | xx = yy Phi, Ds     *)
  | Lemma of lemma * Decs               (*      | xx = cc, Ds         *)
  | Left of int * Decs                  (*      | xx = pi1 yy, Ds     *)
  | Right of int * Decs                 (*      | xx = pi2 yy, Ds     *)
 
  datatype LemmaDec =			(* Lemmas                     *)
    LemmaDec of name * For		(* L ::= c:F                  *)

  type mctx = MDec IntSyn.Ctx           (* Delta ::= . | Delta, xx : F*)

  local
    structure I = IntSyn
    val maxLabel = Global.maxCid
    val maxLemma = Global.maxCid

    val labelArray = Array.array (maxLabel+1, LabelDec("", I.Null, I.Null)) : LabelDec Array.array
    val nextLabel = ref 0

    val lemmaArray = Array.array (maxLemma+1, LemmaDec ("", True)) : LemmaDec Array.array
    val nextLemma = ref 0

    fun labelLookup label = Array.sub (labelArray, label)
    fun labelAdd (labelDec) = 
        let
	  val label = !nextLabel
	in
	  if label > maxLabel
	    then raise Error ("Global signature size " ^ Int.toString (maxLabel+1) ^ " exceeded")
	  else (Array.update (labelArray, label, labelDec) ;
		nextLabel := label + 1;
		label)
	end
    fun labelSize () = (!nextLabel)


    fun lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    fun lemmaAdd (lemmaDec) = 
        let
	  val lemma = !nextLemma
	in
	  if lemma > maxLemma
	    then raise Error ("Global signature size " ^ Int.toString (maxLemma+1) ^ " exceeded")
	  else (Array.update (lemmaArray, lemma, lemmaDec) ;
		nextLemma := lemma + 1;
		lemma)
	end
    fun lemmaSize () = (!nextLemma)


    fun mdecSub (MDec (name, F), s) = MDec (name, TClo (F, s))

    (* union (G, G') = G''

       Invariant:
       G'' = G, G'
    *)
    fun union (G, I.Null) = G
      | union (G, I.Decl (G', D)) = I.Decl (union(G, G'), D)

    (* makectx Psi = G
     
       Invariant:
       G is Psi, where the Prim/Block information is discarded.
    *)
    fun makectx (I.Null) = I.Null
      | makectx (I.Decl (G, Prim D)) = I.Decl (makectx G, D)
      | makectx (I.Decl (G, Block (CtxBlock (l, G')))) = union (makectx G, G')

    fun lfctxLength (I.Null) = 0
      | lfctxLength (I.Decl (Psi, Prim _))= (lfctxLength Psi) + 1
      | lfctxLength (I.Decl (Psi, Block (CtxBlock (_, G)))) =
          (lfctxLength Psi) + (I.ctxLength G)


    (* lfctxDec (Psi, k) = (LD', w')
       Invariant: 
       If      |Psi| >= k, where |Psi| is size of Psi,
       and     Psi = Psi1, LD, Psi2
       then    Psi |- k = LD or Psi |- k in LD  (if LD is a contextblock
       then    LD' = LD
       and     Psi |- w' : Psi1, LD\1   (w' is a weakening substitution)
       and     LD\1 is LD if LD is prim, and LD\1 = x:A if LD = G, x:A
   *)
    fun lfctxLFDec (Psi, k) = 
      let 
	fun lfctxLFDec' (I.Decl (Psi', LD as Prim (I.Dec (x, V'))), 1) = 
	      (LD, I.Shift k)
	  | lfctxLFDec' (I.Decl (Psi', Prim _), k') = lfctxLFDec' (Psi', k'-1)
	  | lfctxLFDec' (I.Decl (Psi', LD as Block (CtxBlock (_, G))), k') =
	    let 
	      val l = I.ctxLength G 
	    in
	      if k' <= l then
		(LD, I.Shift (k - k' + 1))
	      else
		lfctxLFDec' (Psi', k' - l)
	    end

	 (* lfctxDec' (Null, k')  should not occur by invariant *)
      in
	lfctxLFDec' (Psi, k)
      end

    (* dot1n (G, s) = s'
      
       Invariant:
       If   G1 |- s : G2
       then G1, G |- s' : G2, G
       where s' = 1.(1.  ...     s) o ^ ) o ^
                        |G|-times
    *)
    fun dot1n (I.Null, s) = s
      | dot1n (I.Decl (G, _) , s) = I.dot1 (dot1n (G, s))


  in 
    val labelLookup = labelLookup 
    val labelAdd = labelAdd
    val labelSize = labelSize
    val lemmaLookup = lemmaLookup 
    val lemmaAdd = lemmaAdd
    val lemmaSize = lemmaSize
    val mdecSub = mdecSub
    val makectx = makectx
    val lfctxLength = lfctxLength
    val lfctxLFDec = lfctxLFDec
    val dot1n = dot1n
  end
end (* functor FunSyn *)





