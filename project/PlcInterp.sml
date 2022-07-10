(* PlcInterp *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc

fun eval (e:expr) (p:plcVal env) : plcVal =
  case e of
      ConI(i) => IntV i
    | ConB(b) => BoolV b
    | ESeq(t) => SeqV []
    | Var(name) => lookup p name
    | Let(name, value, exp) => eval exp ((name, (eval value p))::p)
    | Letrec(funName, varType, varName, funType, funBody, prog) =>
      eval prog ((funName, Clos (funName, varName, funBody, p))::p)
    | Prim1 (operation, exp) =>
      let
        val value = eval exp p
      in
        case operation of
          ("!") =>
            (case value of
              (BoolV v) => BoolV (not v)
              | _ => raise Impossible)
        | ("-") =>
            (case value of
              (IntV i) => IntV (~ i)
              | _ => raise Impossible)
        | ("hd") => 
          (case value of
             SeqV (xs::t) => xs
            | SeqV ([]) => raise HDEmptySeq
            | _ => raise Impossible)
        | ("tl") => 
          (case value of
             SeqV (xs::t) => SeqV t
            | SeqV ([]) => raise TLEmptySeq
            | _ => raise Impossible)
        | ("ise") =>
          (case value of
            SeqV ([]) => BoolV true
            | SeqV (xs::t) => BoolV false
            | _ => raise Impossible)
        | ("print") => (print ((val2string value) ^ "\n"); ListV [])
        | _ => raise Impossible
      end
    | Prim2(operation, exp1, exp2) =>
      let
        val val1 = eval exp1 p;
        val val2 = eval exp2 p
      in
        case operation of
          ("&&") =>
            (case (val1, val2) of
              (BoolV v1, BoolV v2) => BoolV (v1 andalso v2)
              | _ => raise Impossible)
        | ("+") =>
            (case (val1, val2) of
              (IntV v1, IntV v2) => IntV (v1 + v2)
              | _ => raise Impossible)
        | ("-") =>
            (case (val1, val2) of
              (IntV v1, IntV v2) => IntV (v1 - v2)
              | _ => raise Impossible)
        | ("*") =>
            (case (val1, val2) of
              (IntV v1, IntV v2) => IntV (v1 * v2)
              | _ => raise Impossible)
        | ("/") =>
            (case (val1, val2) of
              (IntV v1, IntV v2) => IntV (v1 div v2)
              | _ => raise Impossible)
        | ("=") =>
            (case (val1, val2) of
              (BoolV v1, BoolV v2) => BoolV (v1 = v2)
              | (IntV v1, IntV v2) => BoolV (v1 = v2)
              | (ListV v1, ListV v2) => BoolV (v1 = v2)
              | _ => raise Impossible)
        | ("!=") =>
            (case (val1, val2) of
              (BoolV v1, BoolV v2) => BoolV (v1 <> v2)
              | (IntV v1, IntV v2) => BoolV (v1 <> v2)
              | (ListV v1, ListV v2) => BoolV (v1 <> v2)
              | _ => raise Impossible)
        | ("<") =>
            (case (val1, val2) of
              (IntV v1, IntV v2) => BoolV (v1 < v2)
              | _ => raise Impossible)
        | ("<=") =>
            (case (val1, val2) of
              (IntV v1, IntV v2) => BoolV (v1 <= v2)
              | _ => raise Impossible)
        | ("::") =>
            (case val2 of
              (SeqV []) => SeqV [val1]
            | (SeqV v2) => SeqV (val1::v2)
            | _ => raise Impossible)
        | (";") => val2
        | _ => raise Impossible
      end
    | If(cond, thenexp, elsexp) =>
      let
        val test = eval cond p
      in
        case test of
          (BoolV result) => if result then (eval thenexp p) else (eval elsexp p)
        | _ => raise Impossible
      end
    | Match(exp, options) =>
      let
        val what = eval exp p;
        fun tryMatch (next::rest) : plcVal =
            (case next of
              (SOME(condexp), option) =>
                let
                  val cond = eval condexp p
                in
                  if what = cond then eval option p else tryMatch rest
                end
            | (NONE, option) => eval option p)
          | tryMatch [] = raise ValueNotFoundInMatch;
      in
        tryMatch options
      end
    | Call(funName, valexp) =>
      let
        val funClos = eval funName p;
      in
        case funClos of 
          Clos(funName, varName, funBody, funP) =>
            let
              val value = eval valexp p;
              val recst = (varName, value)::(funName, funClos)::funP
            in
              eval funBody recst
            end
        | _ => raise NotAFunc
      end
    | List(items) =>
      let
        fun evalList (items:expr list) (p:plcVal env) : plcVal list =
          case items of
            [] => []
          | xs::t => (eval xs p)::(evalList t p)
      in
        ListV (evalList items p)
      end
    | Item(index, itemExp) =>
      let
        val itemEval = eval itemExp p;
        fun findIndex (curr: int) (xs::t : plcVal list) : plcVal =
            if (curr = index) then xs else if (curr > index) then raise Impossible else findIndex (curr + 1) t
          | findIndex _ [] = raise Impossible
      in
        case itemEval of
          ListV(items) => findIndex 1 items
        | _ => raise Impossible
      end
    | Anon(varType, varName, funBody) => Clos("", varName, funBody, p);