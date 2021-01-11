
type ide = string;;


(* Tipi di Insieme *)
type setTypes =
    | Int
    | Bool
    | String


(* Abstract Sintax Tree *)
type exp =
    | CstInt of int
    | CstTrue 
    | CstFalse
    | CstString of string
    | Den of ide
    | Sum of exp * exp
    | Sub of exp * exp
    | Times of exp * exp
    | Ifthenelse of exp * exp * exp
    | Eq of exp * exp
    | Let of ide * exp * exp
    | Fun of ide * exp
    | Letrec of ide * ide * exp * exp
    | Apply of exp * exp
    | Empty of setTypes
    | Singleton of setTypes * exp
    | Of of setTypes * args
    | IsEmpty of exp
    | ExistsIn of exp * exp
    | ContainsSet of exp * exp
    | Put of exp * exp
    | Remove of exp * exp
    | Union of exp * exp
    | Intersection of exp * exp
    | Difference of exp * exp
    | MaxOf of exp
    | MinOf of exp
    | For_all of exp * exp
    | Exists of exp * exp
    | Filter of exp * exp
    | Map of exp * exp
and args =
    | Elem of exp * args
    | Nil;;


type 'v env = (string * 'v) list;;


(* Valori Esprimibili *)
type evT =
    | Int of int
    | Bool of bool
    | String of string
    | Set of string * evT list
    | Closure of ide * exp * evT env
    | RecClosure of ide * ide * exp * evT env
    | Unbound;;


(* Definizione dell'Ambiente + Operazioni sull'Ambiente *)
let emptyEnv = [("", Unbound)];;

let bind (s:evT env) (i:string) (x:evT) = (i,x) :: s;;

let rec lookup (s:evT env) (i:string) =
    match s with
    | [] ->  Unbound
    | (j,v)::sl when j = i -> v
    | _::sl -> lookup sl i;;



(* Operazione di conversione di tipo evT -> exp *)
let switch_evTexp (v:evT) =
    match v with
    | Int(u) -> CstInt(u)
    | Bool(u) -> if u = true then CstTrue else CstFalse
    | String(u) -> CstString(u)
    | _ -> failwith("switch_evTexp:not a valid type");;

(* Operazione di conversione di tipo setTypes -> string *)
let switch_setTypesString (t:setTypes) =
    match t with
    | (Int:setTypes) -> "int"
    | (Bool:setTypes) -> "bool"
    | (String:setTypes) -> "string";;

(* Operazione di conversione value of evT -> setTypes *)
let switch_evTsetTypes (v:evT) =
    match v with
    | Int(u) -> (Int:setTypes)
    | Bool(u) -> (Bool:setTypes)
    | String(u) -> (String:setTypes)
    | _ -> failwith("switch_evTsetTypes: not a valid type")



(* Typechecker *)
let rec checkList (t:string) l =
    match l with
    | h::tail ->
        if switch_setTypesString (switch_evTsetTypes h) = t
        then checkList t tail
        else false
    | [] -> true;;

let typecheck ((x:string),(y:evT)) =
    match x with	
    | "int" ->  (match y with 
                | Int(u) -> true
                | _ -> false)
    | "bool" -> (match y with 
                | Bool(u) -> true
                | _ -> false)
    | "set" ->  (match y with
                | Set(t,l) ->
                    (match t with
                    | "int" | "bool" | "string" -> checkList t l
                    | _ -> false)
                | _ -> false)
    | _ -> failwith("typecheck: not a valid type");;



(* Operazioni per Insiemi *)
let emptySet (t:setTypes) = Set(switch_setTypesString t,[]);;

let set_isEmpty (set:evT) =
    match set with
    | Set(t,l) -> if l = [] then Bool(true) else Bool(false)
    | _ -> failwith("set_isEmpty: not a valid type");;

let set_existsIn (v:evT) (set:evT) =
    match (typecheck("set",set), set) with
    | (true, Set(t,l)) ->
        if switch_setTypesString (switch_evTsetTypes v) = t then
            let rec search v l =
                (match l with
                | h::tail -> if h = v then true else search v tail
                | [] -> false)
            in search v l
        else failwith("set_existsIn: not a valid type")
    | (_,_) -> failwith("set_existsIn: not a valid type");;

let set_put (v:evT) (set:evT) =
    match (set_existsIn v set, set) with
    | (true, Set(t,l)) -> Set(t,l)
    | (false, Set(t,l)) -> Set(t,v::l)
    | (_,_) -> failwith("set_put: not a valid type");;

let set_singleton (t:setTypes) (v:evT) = let set = emptySet t in set_put v set;;

let rec set_remove (v:evT) (set:evT) = 
    match (typecheck("set",set), set) with
    | (true, Set(t,l)) -> 
        if t == switch_setTypesString (switch_evTsetTypes v) then
            let rec deleteVal (v:evT) (l:evT list) =
                (match l with
                | h::tail -> if h <> v then h::(deleteVal v tail) else deleteVal v tail
                | [] -> [])
            in Set(t, deleteVal v l)
        else failwith("set_remove: not a valid type")
    | (_,_) -> failwith("set_remove: not a valid type");;

let rec set_containsSet (set:evT) (set1:evT) =
    match (set, set1) with
    | (Set(t,l), Set(t1,l1)) ->
        let rec containsList l l1 =
            (match l1 with
            | h::tail -> if set_existsIn h (Set(t,l)) then containsList l tail else false
            | [] -> true)
        in
        if t = t1 then Bool(containsList l l1)
        else failwith("set_containsSet: not a valid type")
    | (_,_) -> failwith("set_containsSet: not a valid type");;

let rec deleteDuplicates (t:string) l lret =
    match l with
    | h::tail -> if set_existsIn h (Set(t,tail)) then deleteDuplicates t tail lret else deleteDuplicates t tail (h::lret)
    | [] -> lret;;

let set_of (t:setTypes) (l:evT list) = 
    match typecheck("set", (Set(switch_setTypesString t,l))) with
    | true -> Set(switch_setTypesString t, deleteDuplicates (switch_setTypesString t) l [])
    | false -> failwith("set_of: not a valid type");;

let rec maxInt (l:evT list) (max:int) =
    match l with
    | h::tail ->
        (match h with
        | Int(v) -> if v > max then maxInt tail v else maxInt tail max
        | _ -> failwith("maxInt: not a valid type"))
    | [] -> max;;

let set_maxOf (set:evT) =
    match set with
    | Set(t,l) -> if t = "int" then Int(maxInt l 0) else failwith("set_maxOf: not a valid type")
    | _ -> failwith("set_maxOf: not a valid type");;

let rec minInt (l:evT list) (min:int) =
    match l with
    | h::tail ->
        (match h with
        | Int(v) -> if v < min then minInt tail v else minInt tail min
        | _ -> failwith("minInt: not a valid type"))
    | [] -> min;;

let set_minOf (set:evT) =
    match set with
    | Set(t,l) -> if t = "int" then Int(minInt l Int.max_int) else failwith("set_minOf: not a valid type")
    | _ -> failwith("set_minOf: not a valid type");;

let set_union (set1:evT) (set2:evT) =
    match (set1, set2) with
    | (Set(t1,l1), Set(t2,l2)) ->
        if t1 = t2 then Set(t1, deleteDuplicates t1 (l1@l2) [])
        else failwith("set_union: not a valid type")
    | (_,_) -> failwith("set_union: not a valid type");;

let rec commonElems (t:string) l1 l2 lret =
    match l1 with
    | h::tail -> if set_existsIn h (Set(t,l2)) then commonElems t tail l2 (h::lret) else commonElems t tail l2 lret
    | [] -> lret;;

let set_intersection (set1:evT) (set2:evT) =
    match (set1, set2) with
    | (Set(t1,l1), Set(t2,l2)) ->
        if t1 = t2 then Set(t1, commonElems t1 l1 l2 [])
        else failwith("set_intersection: not a valid type")
    | (_,_) -> failwith("set_intersection: not a valid type");;

let rec uncommonElems (t:string) l1 l2 lret =
    match l1 with
    | h::tail ->
        if set_existsIn h (Set(t,l2)) then uncommonElems t tail l2 lret
        else uncommonElems t tail l2 (h::lret)
    | [] -> lret;;

let set_difference (set1:evT) (set2:evT) = 
    match (set1, set2) with
    | (Set(t1,l1), Set(t2,l2)) ->
        if t1 = t2 then Set(t1, uncommonElems t1 l1 l2 [])
        else failwith("set_intersection: not a valid type")
    | (_,_) -> failwith("set_intersection: not a valid type");;


(* Operazioni per Interi *)
let int_eq(x,y) =   
    match (typecheck("int",x), typecheck("int",y), x, y) with
    | (true, true, Int(v), Int(w)) -> Bool(v = w)
    | (_,_,_,_) -> failwith("int_eq:run-time error");;
       
let int_plus(x, y) = 
    match(typecheck("int",x), typecheck("int",y), x, y) with
    | (true, true, Int(v), Int(w)) -> Int(v + w)
    | (_,_,_,_) -> failwith("int_plus:run-time error");;

let int_sub(x, y) = 
    match(typecheck("int",x), typecheck("int",y), x, y) with
    | (true, true, Int(v), Int(w)) -> Int(v - w)
    | (_,_,_,_) -> failwith("int_sub:run-time error");;

let int_times(x, y) = 
    match(typecheck("int",x), typecheck("int",y), x, y) with
    | (true, true, Int(v), Int(w)) -> Int(v * w)
    | (_,_,_,_) -> failwith("int_times:run-time error");;


(* Interprete *)
let rec eval  (e:exp) (s:evT env) =
    match e with
    | CstInt(n) -> Int(n)
    | CstTrue -> Bool(true)
    | CstFalse -> Bool(false)
    | CstString(x) -> String(x)
    | Den(i) -> lookup s i
    | Eq(e1,e2) -> int_eq((eval e1 s), (eval e2 s))
    | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
    | Sum(e1,e2) -> int_plus((eval e1 s), (eval e2 s))
    | Sub(e1,e2) -> int_sub((eval e1 s), (eval e2 s))
    | Ifthenelse(e1,e2,e3) ->
        let g = eval e1 s in
        (match (typecheck("bool", g), g) with
        | (true, Bool(true)) -> eval e2 s
        | (true, Bool(false)) -> eval e3 s
        | (_,_) -> failwith ("nonboolean guard"))
    | Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
    | Fun(arg, ebody) -> Closure(arg,ebody,s)
    | Letrec(f, arg, fBody, letBody) -> 
        let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in (eval letBody benv)
    | Apply(eF, eArg) ->
        let fclosure = eval eF s in
        (match fclosure with 
        | Closure(arg, fbody, fDecEnv) ->
            let aVal = eval eArg s in
            let aenv = bind fDecEnv arg aVal in eval fbody aenv
        | RecClosure(f, arg, fbody, fDecEnv) ->
            let aVal = eval eArg s in
            let rEnv = bind fDecEnv f fclosure in
            let aenv = bind rEnv arg aVal in eval fbody aenv
        | _ -> failwith("non functional value"))
    | Empty(t) -> emptySet t
    | Singleton(t,v) -> set_singleton t (eval v s)
    | Of(t,argL) -> 
        let rec evalList (args:args) lret =
            (match args with
            | Elem(v,arg) ->
                let v' = eval v s in
                if typecheck(switch_setTypesString t, v') then evalList arg (v'::lret)
                else failwith("Of:not a valid type")
            | Nil -> lret)
        in set_of t (evalList argL [])
    | IsEmpty(set) -> set_isEmpty (eval set s)
    | ExistsIn(v,set) -> Bool(set_existsIn (eval v s) (eval set s))
    | ContainsSet(set,set1) -> set_containsSet (eval set s) (eval set1 s)
    | Put(v,set) -> set_put (eval v s) (eval set s)
    | Remove(v,set) -> set_remove (eval v s) (eval set s)
    | Union(set1,set2) -> set_union (eval set1 s) (eval set2 s)
    | Intersection(set1,set2) -> set_intersection (eval set1 s) (eval set2 s)
    | Difference(set1,set2) -> set_difference (eval set1 s) (eval set2 s)
    | MaxOf(set) -> set_maxOf (eval set s)
    | MinOf(set) -> set_minOf (eval set s)
    | For_all(pred,set) ->
        let eSet = eval set s in
        (match (typecheck("set",eSet), eSet, (eval pred s)) with
        | (true, Set(t,l), Closure(arg,fbody,fenv)) ->
            let env0 = emptyEnv in
            let rec checkPredAll l =
                (match l with
                | h::tail ->
                    let fVal = eval (Apply(pred,switch_evTexp h)) env0 in
                    if fVal = Bool(true) then checkPredAll tail else Bool(false)
                | [] -> Bool(true))
            in checkPredAll l
        | (_,_,_) -> failwith("For_all:not a set or not a functional value"))
    | Exists(pred,set) ->
        let eSet = eval set s in
        (match (typecheck("set",eSet), eSet, (eval pred s)) with
        | (true, Set(t,l), Closure(arg,fbody,fenv)) ->
            let env0 = emptyEnv in
            let rec checkPredExists l =
                (match l with
                | h::tail ->
                    let fVal = eval (Apply(pred, switch_evTexp h)) env0 in
                    if fVal = Bool(false) then checkPredExists tail else Bool(true)
                | [] -> Bool(false))
            in checkPredExists l
        | (_,_,_) -> failwith("Exists:not a set or not a functional value"))
    | Filter(pred,set) ->
        let eSet = eval set s in
        (match (typecheck("set",eSet), eSet, (eval pred s)) with
        | (true, Set(t,l), Closure(arg,fbody,fenv)) ->
            let env0 = emptyEnv in
            let rec checkPredFilter l lret =
                (match l with
                | h::tail ->
                    let fVal = eval (Apply(pred, switch_evTexp h)) env0 in
                    (match fVal with
                    | Bool(true) -> checkPredFilter tail (h::lret)
                    | Bool(false) -> checkPredFilter tail lret
                    | _ -> failwith("Filter:not a valid type"))
                | [] -> lret)
            in Set(t, checkPredFilter l [])
        | (_,_,_) -> failwith("Filter:not a set or not a functional value"))
    | Map(func,set) ->
        let eSet = eval set s in
        (match (typecheck("set",eSet), eSet, (eval func s)) with
        | (true, Set(t,l), Closure(arg,fbody,fenv)) ->
            let env0 = emptyEnv in
            let rec checkPredMap l lret =
                (match l with
                | h::tail ->
                    let fVal = eval (Apply(func, switch_evTexp h)) env0 in
                    checkPredMap tail (fVal::lret)
                | [] -> lret)
            in Set(t, deleteDuplicates t (checkPredMap l []) [])
        | (_,_,_) -> failwith("Map:not a set or not a functional value"));;




(**************************************** TEST *******************************************)

(* Creazione degli Insiemi *)
let env = emptyEnv;;
let setInt = Of(Int, Elem(CstInt(1),Elem(CstInt(2),Elem(CstInt(3),Elem(CstInt(4),Nil)))));;
let setInt2 = Of(Int, Elem(CstInt(1),Elem(CstInt(2),Nil)));;
let setBool = Empty(Bool);;
let setStr = Singleton(String, CstString("hello"));;
print_string " -  setInt " ; eval setInt env;;
print_string " -  setInt2 " ; eval setInt2 env;;
print_string " -  setBool " ; eval setBool env;;
print_string " -  setStr " ; eval setStr env;;

(* Operazioni di aggiunta/rimozione elementi *)
let setInt1 = Put(CstInt(10), Remove(CstInt(3), Remove(CstInt(9), setInt)));;
let setStr = Put(CstString("hi"), setStr);;
print_string " -  setInt1 = Put(CstInt(10), Remove(CstInt(3), Remove(CstInt(9), setInt))) " ; eval setInt1 env;;
print_string " -  setStr = Put(CstString(\"hi\"), setStr) " ; eval setStr env;;

(* Operazioni di controllo *)
print_string " -  IsEmpty(setInt) " ; eval (IsEmpty(setInt)) env;;
print_string " -  IsEmpty(setBool) " ; eval (IsEmpty(setBool)) env;;
print_string " -  ExistsIn(CstInt(1), setInt1) " ; eval (ExistsIn(CstInt(1), setInt1)) env;;
print_string " -  ExistsIn(CstInt(11), setInt1) " ; eval (ExistsIn(CstInt(11), setInt1)) env;;
print_string " -  ContainsSet(setInt1, setInt2) " ; eval (ContainsSet(setInt1, setInt2)) env;;
print_string " -  ContainsSet(setInt1, Remove(CstInt(1), setInt2)) " ; eval (ContainsSet(setInt1, Remove(CstInt(1), setInt2))) env;;

(* Operazioni su Insiemi *)
let setI = Intersection(setInt1, setInt2);;
let setU = Union(setInt1, setInt2);;
let setD = Difference(setInt1, setInt2);;
print_string " -  Intersection(setInt1, setInt2) " ; eval setI env;;
print_string " -  Union(setInt1, setInt2) " ; eval setU env;;
print_string " -  Difference(setInt1, setInt2) " ; eval setD env;;

(* Ricerca di Max e Min in un Insieme *)
print_string " -  MaxOf(setInt) " ; eval (MaxOf(setInt)) env;;
print_string " -  MinOf(setInt) " ; eval (MinOf(setInt)) env;;
print_string " -  MaxOf(setI) " ; eval (MaxOf(setI)) env;;
print_string " -  MinOf(setI) " ; eval (MinOf(setI)) env;;

(* Operazioni Funzionali *)
let pred_is2 = Fun("x", Ifthenelse(Eq(Den("x"),CstInt(2)),
                                CstTrue,
                                CstFalse));;
let fBitMap_2 = Fun("x", Times(Den("x"), CstInt(2)));;

print_string " -  For_all(pred_is2, setInt1) " ; eval (For_all(pred_is2, setInt1)) env;;
print_string " -  Exists(pred_is2, setInt1) " ; eval (Exists(pred_is2, setInt1)) env;;
print_string " -  Filter(pred_is2, setInt1) " ; eval (Filter(pred_is2, setInt1)) env;;
print_string " -  Map(fBitMap_2, setInt1) " ; eval (Map(fBitMap_2, setInt1)) env;;

print_string " -  For_all(pred_is2, setI) " ; eval (For_all(pred_is2, setI)) env;;
print_string " -  Exists(pred_is2, setI) " ; eval (Exists(pred_is2, setI)) env;;
print_string " -  Filter(pred_is2, setI) " ; eval (Filter(pred_is2, setI)) env;;
print_string " -  Map(fBitMap_2, setI) " ; eval (Map(fBitMap_2, setI)) env;;



(************************************** TEST RUNTIME ERRORS **************************************)

(*eval (Of(Int, Elem(CstString("hello"),Elem(CstInt(2),Elem(CstInt(1),Nil))))) env;;*)
(*eval (Singleton(String, CstInt(1))) env;;*)
(*eval (Put(CstString("hi"), setInt)) env;;*)
(*eval (Remove(CstString("hi"), setInt)) env;;*)
(*eval (IsEmpty(CstInt(1))) env;;*)
(*eval (ExistsIn(CstString("hello"), setInt1)) env;;*)
(*eval (ContainsSet(setInt1, setStr)) env;;*)
(*eval (MaxOf(setStr)) env;;*)
(*eval (MinOf(setStr)) env;;*)
(*eval (For_all(pred_is2, setStr)) env;;*)
(*eval (Exists(pred_is2, CstInt(1))) env;;*)
(*eval (Map(setInt, setInt)) env;;*)
(*eval (Map(pred_is2, setStr)) env;;*)