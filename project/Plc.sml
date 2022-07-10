(* Plc interpreter main file *)



fun run (e:expr) = 
    val2string(eval e []) ^ " : " ^ type2string (teval e [])

    handle SymbolNotFound  => "EnvironError: Couldn't find value or type in the environment"
    
    | Impossible           => "EvalError: This is impossible"
    | HDEmptySeq           => "EvalError: Trying to access the head of an empty list"
    | TLEmptySeq           => "EvalError: Trying to access the tail of an empty list"
    | ValueNotFoundInMatch => "EvalError: Couldn't match the provided value"
    | NotAFunc             => "EvalError: Trying to call an expression that is not a function"
    
    | EmptySeq             => "TypeError: Provided sequence is empty"
    | UnknownType          => "TypeError: Unknown error type"
    | NotEqTypes           => "TypeError: Comparison is using different types"
    | WrongRetType         => "TypeError: Return type is not the same as the codomain of the function"
    | DiffBrTypes          => "TypeError: Return type from then and else branches are differ"
    | IfCondNotBool        => "TypeError: Condition not boolean"
    | NoMatchResults       => "TypeError: No expressions to match with"
    | MatchResTypeDiff     => "TypeError: In the list of expressions to match , there are different types of return"
    | MatchCondTypesDiff   => "TypeError: In the list of expressions to match , there are different types of conditions"
    | CallTypeMisM         => "TypeError: Input and function domain type differ"
    | NotFunc              => "TypeError: Trying to call a non function type"
    | ListOutOfRange       => "TypeError: Trying to access element out of range "
    | OpNonList            => "TypeError: Trying to access element of expression that is not a list"
