(* Syntax and semantics of the module system, also encapsulation of the state of modular LF *)
(* Author: Florian Rabe *)

signature MODSYN =
sig
  structure I : INTSYN

  exception Error of string           (* raised on general errors *)
  exception UndefinedCid of IDs.cid   (* raised when symbol lookups fail *)
  exception UndefinedMid of IDs.mid   (* raised when module lookups fail *)


  (* general notes
     The concept of modules unifies the concepts of signatures and views.
     The concept of symbols unifies the concepts of constants (i.e., ConDec) and structures (i.e., StrDec).
     The concept of links unifies the concept of structures and views.
     A "C" at the end of a function name means that it affects the current module (i.e., the most recently opened one).
     Besides IntSyn, only the global structure IDs is assumed. In particular, we have
     - mid: module id (nested modules have unique mids)
     - cid: global symbol id, every constant or structure of any module has a unique cid
  *)

  (********************** Data types and related functions **********************)
  
  (*
    open declarations occur as part of signature inclusions and structure declarations
    They consists of a list of qualified names c of the domain signature and names n.
    The semantics is that n becomes an abbreviation for c in the codomain signature.
  *)
  datatype OpenDec = OpenDec of (IDs.cid * string) list

  (*
     morphisms
     morphisms have a domain and a codomain signature
     a morphism from S to T can be regarded as a (record/structure) expression of type S over signature T
     MorStr(c) is the morphism induced by the structure c
     MorView(m) is the morphism induced by the view m
     MorComp(mor,mor') is the composition of mor and mor' in diagram order (i.e., mor' o mor)
  *)
  datatype Morph = MorStr of IDs.cid | MorView of IDs.mid | MorId of IDs.mid | MorComp of Morph * Morph
  
  (* logical relations *)
  datatype Rel = Rel of IDs.mid | RelComp of Morph * Rel

  (* symbol instantiations within a view or structure
     instantiations are the building blocks of structures and views, say from S to T
     * ConInst(c, O, t) instantiates the constant c of S with the expression t over T
     * StrInst(r, O, mor) instantiates the structure r (say with domain R) of S with the expression mor,
        i.e., a morphism from R to T
       deep assignments are possible, e.g., ConInst(r.s.c, t) or Str(r.s, mor)
     * InclInst(c, O, mor) instantiates the direct inclusion into S (say from R) with the morphism mor from R to T
     Above, O is the origin of the instantiation:
       NONE if given by the input, SOME s if generated by elaborating the StrInst s
  *)
  datatype SymInst = ConInst of IDs.cid * (IDs.cid option) * I.Exp | StrInst of IDs.cid * (IDs.cid option) * Morph
                   | InclInst of IDs.cid * (IDs.cid option) * Morph

  (* symbol cases within a logical relations *)
  datatype SymCase  = ConCase of IDs.cid * (IDs.cid option) * I.Exp | StrCase of IDs.cid * (IDs.cid option) * Rel
                   | InclCase of IDs.cid * (IDs.cid option) * Rel

  (* inclusion declaration in a signature *)
  datatype SigIncl
     = SigIncl of IDs.mid     (* included signature *)
                * OpenDec     (* opening and renaming of constants in the included signature *)

  (*
     structure declarations
     a structure instantiates another signature, say S
     such a structure s declared in signature T induces a morphism MorStr(s) from S to T
     such a structure carries instantiations of symbols of S with expressions of T
     structure definitions define a structure with a morphism
  *)
  datatype StrDec
  = StrDec of
      string list                      (* qualified name *)
    * IDs.qid                          (* list of structures via which it is imported *)
    * IDs.mid                          (* domain (= instantiated signature) *)
    * SymInst list                     (* instantiations *)
    * OpenDec                          (* opened and renamed imported names *)
    * bool                             (* implicit *)
  | StrDef of
      string list                      (* qualified name *)
    * IDs.qid                          (* list of structures via which it is imported *)
    * IDs.mid                          (* domain (= instantiated signature) *)
    * Morph                            (* definition *)    
    * bool                             (* implicit *)

  (* module declarations
     * A signature is a list of symbol declarations.
     * A view from S to T provides instantiations for all symbols of S in terms of expressions over T
       It can be considered as an implementation of S in terms of the symbols of T.
       Thus a view from S to T can be seen as a functor from T to S.
     * A logical relations between a list morphisms with the same domain and codomain.
     The symbol level declarations within a module are stored separately and are not part of the ModDec
  *)
  datatype ModDec
     = SigDec of
         URI.uri                       (* namespace *)
       * string list                   (* qualified name *)
     | ViewDec of
         URI.uri                       (* base *)
       * string list                   (* name *)
       * IDs.mid                       (* domain *)
       * IDs.mid                       (* codomain *)
       * bool                          (* implicit *)
     | RelDec of
         URI.uri                       (* base *)
       * string list                   (* name *)
       * IDs.mid                       (* domain *)
       * IDs.mid                       (* codomain *)
       * Morph list                    (* morphisms *)
  
  (* unifies all symbol level declarations *)
  datatype Declaration = SymMod of IDs.mid * ModDec
                       | SymCon of I.ConDec | SymStr of StrDec | SymIncl of SigIncl
                       | SymConInst of SymInst | SymStrInst of SymInst | SymInclInst of SymInst
                       | SymConCase of SymCase | SymStrCase of SymCase | SymInclCase of SymCase

   datatype Read = ReadFile of string  (* file name *)
   
  (* convenience methods to access components of declarations *)
  val modDecBase : ModDec -> URI.uri
  val modDecName : ModDec -> string list
  val strDecName : StrDec -> string list
  val strDecFoldName: StrDec -> string
  val modName    : IDs.mid -> string list
  val modFoldName: IDs.mid -> string
  val symName    : IDs.cid -> string list
  val symFoldName: IDs.cid -> string
  val fullFoldName: IDs.cid -> string
  val strDecQid  : StrDec -> IDs.qid
  val strDecDom  : StrDec -> IDs.mid
  val symInstCid : SymInst -> IDs.cid
  val symInstOrg : SymInst -> IDs.cid option
  val symQid     : IDs.cid -> IDs.qid

  (********************** Interface methods that affect the state **********************)
  
  (* called at the beginning of a module *)
  val modOpen    : ModDec -> IDs.cid
  (* called at the end of a module *)
  val modClose   : unit -> unit
  (* called to add an inclusion to the current module, which must be a signature *)
  val inclAddC   : SigIncl -> IDs.cid
  (* called to add a constant declaration to the current signature, which must be a signature *)
  val sgnAddC    : I.ConDec -> IDs.cid
  (* called to add a structure declaration to the current module, which must be a signature *)
  val structAddC : StrDec -> IDs.cid
  (* called to add an instantiation to the current module, which must be a view *)
  val instAddC   : SymInst -> IDs.cid
  (* called to add a case to the current module, which must be a logical relation *)
  val caseAddC   : SymCase -> IDs.cid
  (* called to reset the state *)
  val reset      : unit -> unit

  (********************** Interface methods that do not affect the state **********************)

  (* generic lookup of symbol declarations or instantiation by global id, raises UndefinedCid _ *)
  val symLookup : IDs.cid -> Declaration
  (* specialized lookups; these raise UndefinedCid _ if the cid is defined but returns the wrong data *)
  val sgnLookup     : IDs.cid -> I.ConDec          (* constant declarations *)
  val structLookup  : IDs.cid -> StrDec            (* structure declarations *)

  (* looks up a module declaration, raise UndefinedMid _ *)
  val modLookup  : IDs.mid -> ModDec
  val midToCid   : IDs.mid -> IDs.cid
  val cidToMid   : IDs.cid -> IDs.mid

  (* sigRelType describes signatures visible to a signature m: 
     a) m itself: (m,Self)
     b) every ancestor signature a: (a, Ancestor p) where p is the position within a where m occurs
     c) every signature d directly included via include declaration with cid: (d, Included SOME cid)
     d) every signature d indirectly included (transitive closure): (d, Included NONE)
     e) every signature d visible to m because it is directly or indirectly included into an ancestor of m: (d, AncIncluded)
     The relations a, b, and (c \cup d \cup e) are mutually exclusive,
     c, d, and e may be combined in which case e takes precedence over c and d.
     The ancestors of included signatures can be ignored because they must also be ancestors of m.
     The order in the list is: Self, Ancestor _ (innermost to outermost), AncIncluded (any order), Included _ (any order)
     
     Semantics:
     * m can see all symbols in Self and all symbols in AncIncluded or Included signatures,
       but only those declarations of Ancestor p that occur before position p in the ancestor.
     * Morphisms out of m are the identity for all symbols in Ancestor _ or AncIncluded signatures.
       They provide ConInst _ (possibly generated by a StrInst _) for the symbols of Self and
       InclInst for the symbols of Included signatures.
       Consequently, an inclusion/structure/view from dom to cod is only legal
       if cod can see the signatures for which the morphism must be the identity.
   *)
  datatype SigRelType = Self | Included of IDs.cid option | Ancestor of IDs.lid | AncIncluded
  (* ModLevObject is the type of composed expressions of module level concepts *)
  datatype ModLevObject = ObjSig of IDs.mid * SigRelType | ObjMor of Morph | ObjRel of Rel
  (* returns the list of objects included into a module
     - for signatures M, this is the flattened list of ObjSig(m,r) where m is any kind of include into M of type r
     - for views and logical relations, this is the list of direct includes of ObjMor(mor) or ObjRel(rel), respectively *)
  val modInclLookup: IDs.mid -> ModLevObject list

  (* convenience methods based on the above *)
  (* sigIncluded(dom,cod) iff dom is included into cod (Self, Included_, or AncIncluded) *)
  val sigIncluded : IDs.mid * IDs.mid -> bool
  (* isSome (symVisible(c, m)) iff c is visible to m, returns the relation between m and IDs.midOf(c)
     AncIncluded takes precedence over Included _ if both are present. *)
  val symVisible : IDs.cid * IDs.mid -> SigRelType option

  (* implicitLookup(d,c) = SOME mor iff mor:d->c is an implicit morphism (coercion) *)
  val implicitLookup: IDs.mid * IDs.mid -> Morph option

  (* application of a method to all declarations of a module
     if called for a signature, the function is applied to all possibly elaborated declarations in declaration order,
     if called for a view, the function is applied to all possibly undefined assignments for all symbols of the domain *)
  val sgnApp     : IDs.mid * (IDs.cid -> unit) -> unit
  val sgnAppC    : (IDs.cid -> unit) -> unit
  (* application of a method to all modules in declaration order *)
  val modApp     : (IDs.mid -> unit) -> unit
  
  (* index for efficiency: application of a structure to a constant/structure *)
  val structMapLookup : IDs.cid * IDs.cid -> IDs.cid option

  (* methods related to the current scope (convenience except for getScope() *)    
  (* returns the list of currently open modules in inverse declaration order and their next available lid *)
  val getScope   : unit -> (IDs.mid * IDs.lid) list 
  (* the current module *)
  val currentMod : unit -> IDs.mid
  (* true: current module is signature, false: current module is view *)
  val inSignature: unit -> bool
  (* true if current module is toplevel signature *)
  val onToplevel : unit -> bool
  (* the current target signature: the current module if a signature, its codomain if a view *)
  val currentTargetSig : unit -> IDs.mid
  (* push/pop the current scope to permit context switching *)
  val pushContext: unit -> unit
  val popContext : unit -> IDs.cid

  (* convenience methods to access components of an installed constant declaration *)
  val constType   : IDs.cid -> I.Exp		(* type of c or d *)
  val constDef    : IDs.cid -> I.Exp		(* definition of d *)
  val constDefOpt : IDs.cid -> I.Exp option
  val constImp    : IDs.cid -> int
  val constStatus : IDs.cid -> I.Status
  val constUni    : IDs.cid -> I.Uni
  val constBlock  : IDs.cid -> I.dctx * I.Dec list

  (* These functions are specific to the non-modular syntax (IntSyn) and independent of the module system.
     However, they must be declared in (or after) ModSyn because they need to look up and expand type definitions. *)
  val ancestor    : I.Exp -> I.Ancestor
  val defAncestor : IDs.cid -> I.Ancestor
  val targetFamOpt: I.Exp -> IDs.cid option  (* target type family or NONE *)
  val targetFam   : I.Exp -> IDs.cid         (* target type family         *)

  (* Comments are always associated with the succeeding declaration.
     Therefore, it is convenient to store them inside the component that stores declarations. *)
  structure Comments : sig
     type comment = string * string  (* comment and position string as l.c-l.c *)
     val push    : comment -> unit
     val getCid  : IDs.cid -> comment option
     val getMid  : IDs.mid -> comment option
  end
end (* signature MODSYN *)