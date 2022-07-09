(* PlcChecker *)

exception EmptySeq
exception UnknownType
exception NotEqTypes
exception WrongRetType
exception DiffBrTypes
exception IfCondNotBool
exception NoMatchResults
exception MatchResTypeDiff
exception MatchCondTypesDiff
exception CallTypeMisM
exception NotFunc
exception ListOutOfRange
exception OpNonList

fun makeSet l s =
    case l of 
        []      => s
    |   (x::xs) => if (not (List.exists(fn item => item = x) s)) then makeSet xs (x::s) else makeSet xs s

fun isEqualityType (p: plcType) = 
    case p of
        IntT            => true
    |   BoolT           => true
    |   ListT l         => if length l > 0 then (isEqualityType (hd l)) andalso (isEqualityType (ListT (tl l))) else true
    |   _               => false



fun teval (e:expr) (p: plcType env) =
            case e of
(*1*)           Var s               => lookup p s
(*2*)       |   ConI _              => IntT
(*3/4*)     |   ConB _              => BoolT
(*5/6*)     |   List l              => 
                if length l > 0
                then ListT (map (fn x => (teval x p)) l)
                else ListT []
(*7a*)      |   ESeq (SeqT t)       => SeqT t
(*7b*)      |   ESeq _              => raise EmptySeq
(*8*)       |   Let (s, e1, e2)     => 
                let
                    val t1      = teval e1 p
                    val newP    = p @ [(s, t1)]
                in
                    teval e2 newP
                end
(*9*)       |   Letrec (fName, varType, varName, codomainType, e1, e2) => 
                let
                   val newP1    = p @ [(fName, FunT(varType, codomainType))]
                   val newP2    = newP1 @ [(varName, varType)]
                   val t1       = teval e1 newP2
                in
                    if (t1 = codomainType)
                    then teval e2 newP1
                    else raise WrongRetType
                end
(*10*)      |   Anon (t, s, e)         =>
                let
                    val newP = p @ [(s, t)]
                    val resultType = teval e newP
                in
                    FunT (t, resultType)
                end
(*11*)      |   Call (e2,e1)            =>
                let
                    val t2 = teval e2 p
                    val t1 = teval e1 p
                in
                    case t2 of 
                    FunT (a,b)  => if (a = t1) then b else raise CallTypeMisM
                    | _         => raise NotFunc
                end
(*12*)      |   If (cond, et, ef)       => 
                let
                    val cond1 = ((teval cond p) = BoolT)
                    val cond2 = ((teval et p) = (teval ef p))
                in
                    if cond1
                    then
                        if cond2
                        then teval et p
                        else raise DiffBrTypes
                    else
                        raise IfCondNotBool
                end
(*13*)      |   Match (e1, l)    => 
                let
                    val t1 = teval e1 p
                    val ste = makeSet (map ( fn x => case x of (SOME e, r) => (teval e p) | (NONE, r) => t1 ) l) []
                    val str = makeSet (map ( fn x => case x of (SOME e, r) => (teval r p) | (NONE, r) => (teval r p) ) l) []
                in
                    let
                        val v1 = length ste
                        val v2 = length str
                    in
                        if (length l = 0) 
                        then raise NoMatchResults
                        else
                            if (v1 > 1) 
                            then raise MatchCondTypesDiff
                            else 
                                if (v2 > 1) 
                                then raise MatchResTypeDiff
                                else (List.nth(str,0))
                    end
                    
                end
(*14*)      |   Prim1 ("!", e1)         => if ((teval e1 p) = BoolT) then BoolT else raise UnknownType
(*15*)      |   Prim1 ("-", e1)         => if ((teval e1 p) = IntT) then IntT else raise UnknownType
(*16*)      |   Prim1 ("hd", e1)        => 
                let
                    val t1 = teval e1 p
                in
                    case t1 of
                        SeqT t              => t
                    |   _                   => raise UnknownType
                end
(*17*)      |   Prim1 ("tl", e1)        => 
                let
                    val t1 = teval e1 p
                in
                    case t1 of
                        SeqT t              => SeqT t
                    |   _                   => raise UnknownType
                end
(*18*)      |   Prim1 ("ise", e1)        => 
                let
                    val t1 = teval e1 p
                in
                    case t1 of
                        SeqT _  => BoolT
                    |   _       => raise UnknownType
                end
(*19*)      |   Prim1 ("print", e1)     => ListT []
(*20*)      |   Prim2 ("&&", e1, e2)    => if ((teval e1 p) = BoolT andalso (teval e2 p) = BoolT) then BoolT else raise NotEqTypes
(*21*)      |   Prim2 ("::", e1, e2)    => 
                let
                    val t1 = teval e1 p
                    val t2 = teval e2 p
                in
                    case e2 of
                        (ESeq (SeqT t))     => if (t1 = t) then SeqT t else raise NotEqTypes
                    |   _                   => if ((SeqT t1) = t2) then t2 else raise NotEqTypes
                end
(*26*)      |   Prim2 (";", e1, e2)     => teval e2 p
(*24a*)     |   Prim2 ("=", e1, e2)     => 
                let
                    val t1 = teval e1 p
                    val t2 = teval e2 p
                    val cond = isEqualityType t1
                in
                    if(t1 = t2)
                    then
                        if (cond)
                        then BoolT
                        else raise UnknownType
                    else raise NotEqTypes
                end
(*24b*)     |   Prim2 ("!=", e1, e2)     => 
                let
                    val t1 = teval e1 p
                    val t2 = teval e2 p
                    val cond = isEqualityType t1
                in
                    if(t1 = t2)
                    then
                        if (cond)
                        then BoolT
                        else raise UnknownType
                    else raise NotEqTypes
                end
(*22/23*)   |   Prim2 (s, e1, e2)       => 
                let
                    val cond1 = (s = "+" orelse s = "-" orelse s = "*" orelse s = "/")
                    val cond2 = (s = "<" orelse s = "<=")
                    val cond3 = ((teval e1 p) = IntT andalso (teval e2 p) = IntT)
                in
                    if (not cond3)
                    then raise NotEqTypes
                    else
                        if cond1 
                        then IntT 
                        else
                            if cond2 
                            then BoolT
                            else raise UnknownType
                end
(*25*)      |   Item(n, e1)             =>
                let
                    val t1 = teval e1 p
                in
                    case t1 of
                        ListT l => 
                        let
                            val maxIndex = length l
                            val index = n
                        in
                            if ( n = 0 orelse (n > maxIndex))
                            then raise ListOutOfRange
                            else List.nth(l, index - 1)
                        end
                    |   _       => raise OpNonList
                end


