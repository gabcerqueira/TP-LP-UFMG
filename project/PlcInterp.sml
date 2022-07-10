(* PlcInterp *)

(* 
use "Environ.sml";
use "Absyn.sml"; *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc

fun deconstructIntV(v: plcVal) : int =
    case v of 
        IntV x => x
        | _ => raise Impossible

fun deconstructBoolV(v: plcVal) : bool =
    case v of 
        BoolV x => x
        | _ => raise Impossible

fun deconstructListTypes(v: plcVal) : plcVal list =
    case v of 
        ListV x => x
        | SeqV x => x
        | _ => raise Impossible

fun deconstructVar(v: expr) : string =
    case v of 
        Var x => x
        | _ => raise Impossible

  
fun eval(e: expr) (ro: plcVal env) : plcVal =
    case e of
        ConI e1 => IntV e1
        | ConB e1 => BoolV e1 
        | ESeq _ => SeqV []
        | Var x => lookup ro x
        | List [] => ListV []
        | List(x::xs: expr list) => let
          val e1 = eval x ro;
          val e2 = deconstructListTypes(eval(List xs) ro);
        in
          ListV (e1::e2)
        end
        | Prim2("&&", e1, e2) => let
          val e1b = deconstructBoolV(eval e1 ro);
          val e2b = deconstructBoolV(eval e2 ro)
        in
          BoolV(e1b andalso e2b)
        end 
        | Prim2("::", e1, ESeq _) => SeqV((eval e1 ro)::[])
        | Prim2("::", e1, e2) => let
          val ve2 = deconstructListTypes(eval e2 ro);
          val ve1 = eval e1 ro;
        in
          SeqV(ve1::ve2)
        end
        | Prim2(";", e1, e2) => let
          val e1 = eval e1 ro
        in
          eval e2 ro
        end
        | Prim2("+", ConI e1, ConI e2) => IntV(e1 + e2)
        | Prim2("-", ConI e1, ConI e2) => IntV(e1 - e2)
        | Prim2("*", ConI e1, ConI e2) => IntV(e1 * e2)
        | Prim2("/", ConI e1, ConI e2) => IntV(e1 div e2)
        | Prim2("<=", ConI e1, ConI e2) => BoolV(e1 <= e2)
        | Prim2("<", ConI e1, ConI e2) => BoolV(e1 < e2)
        | Prim2("=", e1, e2) => BoolV(e1 = e2)
        | Prim2("!=", e1, e2) => BoolV(not (e1 = e2))
        | Prim2(operation, e1, e2) => let
          val ve1 = deconstructIntV(eval e1 ro);
          val ve2 = deconstructIntV(eval e2 ro);
        in
          eval (Prim2(operation, ConI ve1, ConI ve2)) ro
        end
        | Item(e1, List e2) => eval (List.nth(e2, e1-1)) ro
        | Item(e1, e2) => let
          val ve2 = eval e2 ro;
          val newList = deconstructListTypes ve2
        in
          List.nth(newList, e1-1)
        end
        | If(e1, e2, e3) => if eval e1 ro = BoolV true then eval e2 ro else eval e3 ro
        | Prim1("!", ConB e1) => BoolV(not e1)
        | Prim1("!", e1) => BoolV(not (deconstructBoolV(eval e1 ro))) 
        | Prim1("-", ConI e1) => IntV(~e1)
        | Prim1("-", e1) => IntV(~(deconstructIntV(eval e1 ro)))
        | Prim1("hd", e1) => let
          val ve1 = eval e1 ro
        in
          case ve1 of
            SeqV (x::ts: plcVal list) => x
            | SeqV [] => raise HDEmptySeq
            | _ => raise Impossible
        end
        | Prim1("tl", e1) => let
          val ve1 = eval e1 ro
        in
          case ve1 of
            SeqV (x::ts: plcVal list) => SeqV(ts)
            | SeqV [] => raise TLEmptySeq
            | _ => raise Impossible
        end
        | Prim1("ise", e1) => let
          val ve1 = eval e1 ro
        in
          case ve1 of
            SeqV [] => BoolV true
            | _ => BoolV false
        end
        | Prim1("print", e1) => let
          val ve1 = eval e1 ro;
          val str = val2string(ve1);
        in
          print (str ^ "\n");
          ListV []
        end
        | Match(e1, hd::options: (expr option * expr) list) => let
          val ve1 = eval e1 ro;
          val (m, a) = hd
        in
          case m of
            SOME e2 => if ve1 = eval e2 ro then 
                        eval a ro 
                      else if options = [] then 
                        raise ValueNotFoundInMatch 
                      else 
                        eval(Match(e1, options)) ro
            | NONE => eval a ro
        end
        | Anon(e1, e2, e3) => Clos("", e2, e3, ro)
        | Let(e1, e2, e3) => let
          val ve2 = eval e2 ro
        in
          eval e3 ((e1, ve2)::ro)
        end
        | Letrec(nf, _, nv, _, e3, e4) => let
          val clo = Clos(nf, nv, e3, ro);
          val ro' = (nf, clo)::ro;
        in
          eval e4 ro'
        end
        | Call(Var vf, e) => let 
          val fv = lookup ro vf
        in
          case fv of
            Clos(vf, x, e1, fSt) => let
              val ve1 = eval e ro;
              val ro' = (x, ve1) :: (vf, fv) :: fSt
            in
              eval e1 ro'
            end
            | _ => raise NotAFunc
        end 
        | Call(Call f, e) => let 
          val vf = eval (Call f) ro;
        in
          case vf of
            Clos(f, x, e1, fSt) => let
              val ve1 = eval e ro;
              val ro' = (x, ve1) :: (f, vf) :: fSt
            in
              eval e1 ro'
            end
            | _ => raise NotAFunc
        end 
        | _ => raise Impossible