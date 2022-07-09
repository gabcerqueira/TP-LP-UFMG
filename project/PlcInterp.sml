(* PlcInterp *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc

fun eval (e:expr) (p: plcVal env) =
    case e of
        Var s               => lookup p s
    |   ConI x              => IntV x
    |   ConB x              => BoolV x
    |   List l              => 
        if length l > 0
        then ListV (map (fn x => (eval x p)) l)
        else ListV []
    |   ESeq (SeqT t)       => SeqV []
    |   Let (s, e1, e2)     => 
        let
            val v1      = eval e1 p
            val newP    = p @ [(s, v1)]
        in
            eval e2 newP
        end
    |   Anon (t, x, e)      => Clos ("", x, e, p)
    |   Call (e1, e2)       =>
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case v1 of
                Clos (f, s, expr, oldP) => eval expr (oldP @ [(f, v1)] @ [(s, v2)])
            |   _                       => raise NotAFunc
        end
    |   If (cond, et, ef)   => 
        let
            val vcond = eval cond p
        in
            if (vcond = (BoolV true)) then eval et p else eval ef p
        end
    |   Match(e1, l)        =>
        let
            val v1 = eval e1 p
        in
            if length l > 0
            then (
                let
                    val m = hd l
                in
                    case m of 
                        (SOME e1, r1)   => if (v1 = (eval e1 p)) then eval r1 p else eval (Match(e1, tl l)) p
                    |   (NONE, r1)      => eval r1 p
                end
            )
            else raise ValueNotFoundInMatch

        end
    |   Prim1 ("!", e1)     => 
        let
            val v1 = eval e1 p
        in
            case v1 of
                BoolV b => BoolV (not b)
            |   _       => raise Impossible
        end
    |   Prim1 ("-", e1)     => 
        let
            val v1 = eval e1 p
        in
            case v1 of
                IntV n  => IntV (~ n)
            |   _       => raise Impossible
        end
    |   Prim1 ("hd", e1)    => 
        let
            val v1 = eval e1 p
        in
            case v1 of
                SeqV l  => if length l > 0 then hd l else raise HDEmptySeq
            |   _       => raise Impossible
        end
    |   Prim1 ("ise", e1)        => 
        let
            val v1 = eval e1 p
        in
            case v1 of
                SeqV [] => BoolV true
            |   SeqV l  => BoolV false
            |   _       => raise Impossible
        end
    |   Prim1 ("tl", e1)    => 
        let
            val v1 = eval e1 p
        in
            case v1 of
                SeqV l  => if length l > 0 then SeqV (tl l) else raise TLEmptySeq
            |   _       => raise Impossible
        end
    |   Prim1 ("print", e1)        => 
        let
            val v1 = eval e1 p
            val s = (val2string v1) ^ "\n"
        in
            print s;
            ListV []
        end
    |   Prim2 ("&&", e1, e2)    => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case (v1, v2) of
                (BoolV a, BoolV b)  => BoolV (a andalso b)
            |   _                   => raise Impossible
        end
    |   Prim2 ("::", e1, e2)    => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case v1 of
                SeqV a  =>(
                    case v2 of 
                        SeqV b  => SeqV (a @ b)
                    |   _       => SeqV (v2 :: a)
                )
            |   _       =>(
                case v2 of
                    SeqV([])    =>  SeqV (v1 :: [])
                |   SeqV b      =>  SeqV (v1 :: b)
            )
        end
    |   Prim2 (";", e1, e2)     => eval e2 p
    |   Prim2 ("=", e1, e2)     => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            if(v1 = v2)
            then BoolV true
            else BoolV false
        end
    |   Prim2 ("!=", e1, e2)     => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            if(v1 = v2)
            then BoolV false
            else BoolV true
        end
    |   Prim2 ("+", e1, e2)     => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case (v1,v2) of 
                (IntV a, IntV b)    => IntV (a+b)
            |   _                   => raise Impossible
        end
    |   Prim2 ("-", e1, e2)     => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case (v1,v2) of 
                (IntV a, IntV b)    => IntV (a-b)
            |   _                   => raise Impossible
        end
    |   Prim2 ("*", e1, e2)     => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case (v1,v2) of 
                (IntV a, IntV b)    => IntV (a*b)
            |   _                   => raise Impossible
        end
    |   Prim2 ("/", e1, e2)     => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case (v1,v2) of 
                (IntV a, IntV b)    => IntV (a div b)
            |   _                   => raise Impossible
        end
    |   Prim2 ("<", e1, e2)     => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case (v1,v2) of 
                (IntV a, IntV b)    => BoolV (a < b)
            |   _                   => raise Impossible
        end
    |   Prim2 ("<=", e1, e2)     => 
        let
            val v1 = eval e1 p
            val v2 = eval e2 p
        in
            case (v1,v2) of 
                (IntV a, IntV b)    => BoolV (a <= b)
            |   _                   => raise Impossible
        end
    |   Item(n, e1)             =>
        let
            val v1 = eval e1 p
        in
            case v1 of
                ListV l => 
                let
                    val maxIndex = length l
                    val index = n
                in
                    if ( n = 0 orelse (n > maxIndex))
                    then raise Impossible
                    else List.nth(l, index - 1)
                end
            |   _       => raise Impossible
        end
    |   Letrec (fName, _, varName, _, e1, e2) => 
        case e2 of
            Call(_, varExpr)    => (
                let
                    val pWithFunValue   = p @ [(fName, (Clos (fName , varName, e1, p)))]
                in
                    eval e2 pWithFunValue
                end
            )
        |   _                   => raise Impossible
