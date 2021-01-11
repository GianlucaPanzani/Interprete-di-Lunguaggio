
type ide = string;;


(* Valori che rappresentano tipi *)
type tval =
    | TInt
    | TBool
    | TString
    | TSet of tval
    | TFun of tval * tval
    | TUnbound;;


(* Typechecker per gli Insiemi *)
let setTypeCheck t =
    match t with
    | TInt | TBool | TString -> t
    | _ -> failwith("typeSwitch: not a valid type");;


(* Albero di Sintassi Astratta *)
type texp =
    | CstInt of int
    | CstTrue 
    | CstFalse
    | CstString of string
    | Den of ide
    | Sum of texp * texp
    | Sub of texp * texp
    | Times of texp * texp
    | Ifthenelse of texp * texp * texp
    | Eq of texp * texp
    | Let of ide * texp * texp
    | Fun of ide * tval * texp
    | Letrec of ide * ide * tval * tval * texp * texp
    | Apply of texp * texp
    | Empty of tval
    | Singleton of tval * texp
    | Of of tval * args
    | IsEmpty of texp
    | ExistsIn of texp * texp
    | ContainsSet of texp * texp
    | Put of texp * texp
    | Remove of texp * texp
    | Union of texp * texp
    | Intersection of texp * texp
    | Difference of texp * texp
    | MaxOf of texp
    | MinOf of texp
    | For_all of texp * texp
    | Exists of texp * texp
    | Filter of texp * texp
    | Map of texp * texp
and args =
    | Elem of texp * args
    | Nil;;

type 't tenv = (string * 't) list;;


(* Operazioni sull'ambiente *)
let emptyEnv = [("", TUnbound)];;

let bind (s:tval tenv) (i:string) (x:tval) = (i,x) :: s;;

let rec lookup (s:tval tenv) (i:string) =
    match s with
    | [] ->  TUnbound
    | (j,v)::sl when j = i -> v
    | _::sl -> lookup sl i;;


(* Interprete per la valutazione del tipo delle espressioni *)
let rec teval (e:texp) (s:tval tenv) =
    match e with
    | CstInt(n) -> TInt
    | CstTrue -> TBool
    | CstFalse -> TBool
    | CstString(x) -> TString
    | Den(i) -> lookup s i
    | Eq(e1,e2) -> if (teval e1 s) = (teval e2 s) then TBool else failwith("Eq:not a valid type")
    | Times(e1,e2) | Sum(e1,e2) | Sub(e1,e2) ->
        (match ((teval e1 s),(teval e2 s)) with
        | (TInt, TInt) -> TInt
        | (_,_) -> failwith("Times/Sum/Sub:not a valid type"))
    | Ifthenelse(e1,e2,e3) ->
        (match ((teval e1 s), ((teval e2 s)=(teval e3 s))) with
        | (TBool, true) -> teval e2 s
        | (_,_) -> failwith("Ifthenelse:non boolean guard or expressions of different types"))
    | Let(i, e, ebody) -> teval ebody (bind s i (teval e s))
    | Fun(arg, aType, ebody) -> TFun(aType, teval ebody (bind s arg aType))
    | Letrec(f, arg, aType, rType, fBody, lBody) ->
        let fEnv = bind s f (TFun(aType,rType)) in
        let aEnv = bind fEnv arg aType in
        let t = teval fBody aEnv in
        if t = (teval lBody aEnv) then t else failwith("Letrec:not a valid type")
    | Apply(eF, eArg) ->
        (match teval eF s with 
        | TFun(t1,t2) -> if t1 = (teval eArg s) then t2 else failwith("Apply:not a valid type")
        | _ -> failwith("Apply:non functional type"))
    | Empty(t) -> TSet(setTypeCheck t)
    | Singleton(t,v) ->
        if (teval v s) = setTypeCheck t
        then TSet(t)
        else failwith("Singleton:not a valid type")
    | Of(t,argL) -> 
        let t' = setTypeCheck t in
        let rec checkList args =
            (match args with
            | Elem(v,argL) -> if (teval v s) = t' then checkList argL else failwith("Of:not a valid type")
            | Nil -> TSet(t'))
        in checkList argL
    | MaxOf(set) | MinOf(set) ->
        (match teval set s with
        | TSet(TInt) -> TInt
        | _ -> failwith("MinOf/MaxOf:not a valid type"))
    | IsEmpty(set) ->
        (match teval set s with
        | TSet(TInt) | TSet(TBool) | TSet(TString) -> TBool
        | _ -> failwith("IsEmpty:not a valid type"))
    | ExistsIn(v,set) ->
        (match (teval v s, teval set s) with
        | (t, TSet(t')) -> if t = t' then TBool else failwith("ExistsIn:not a valid type")
        | (_,_) -> failwith("ExistsIn:not a valid type"))
    | ContainsSet(set1,set2) ->
        (match (teval set1 s, teval set2 s) with
        | (TSet(t1), TSet(t2)) -> if t1 = t2 then TBool else failwith("ExistsIn:not a valid type")
        | (_,_) -> failwith("ContainsSet:not a valid type"))
    | Put(v,set) | Remove(v,set) ->
        (match (teval v s, teval set s) with
        | (t, TSet(t')) -> if t = t' then TSet(t) else failwith("Put/Remove:not a valid type")
        | (_,_) -> failwith("Put/Remove:not a valid type"))
    | Union(set1,set2) | Intersection(set1,set2) | Difference(set1,set2) ->
        (match (teval set1 s, teval set2 s) with
        | (TSet(t1), TSet(t2)) ->
            if t1 = t2 then TSet(t1)
            else failwith("Union/Intersection/Difference:not a valid type")
        | (_,_) -> failwith("Union/Intersection/Difference:not a valid type"))
    | For_all(pred,set) | Exists(pred,set) | Filter(pred,set) ->
        (match (teval pred s, teval set s) with
        | (TFun(t1,t2), TSet(t)) ->
            if (t = t1) && (t2 = TBool) then TBool
            else failwith("Filter/Exists/For_all:not a valid type")
        | (_,_) -> failwith("Filter/Exists/For_all:not a valid type"))
    | Map(func,set) -> 
        (match (teval func s, teval set s) with
        | (TFun(t1,t2), TSet(t)) -> if t = t1 then t2 else failwith("Map:not a valid type")
        | (_,_) -> failwith("Map:not a valid type"));;




(**************************************** TEST *******************************************)

(* Creazione degli Insiemi *)
let env = emptyEnv;;
let setInt = Of(TInt, Elem(CstInt(1),Elem(CstInt(2),Elem(CstInt(3),Elem(CstInt(4),Nil)))));;
let setInt2 = Of(TInt, Elem(CstInt(1),Elem(CstInt(2),Nil)));;
let setBool = Empty(TBool);;
let setStr = Singleton(TString, CstString("hello"));;
print_string " -  setInt " ; teval setInt env;;
print_string " -  setInt2 " ; teval setInt2 env;;
print_string " -  setBool " ; teval setBool env;;
print_string " -  setStr " ; teval setStr env;;

(* Operazioni di aggiunta/rimozione elementi *)
let setInt1 = Put(CstInt(10), Remove(CstInt(3), Remove(CstInt(9), setInt)));;
let setStr = Put(CstString("hi"), setStr);;
print_string " -  setInt1 = Put(CstInt(10), Remove(CstInt(3), Remove(CstInt(9), setInt))) " ; teval setInt1 env;;
print_string " -  setStr = Put(CstString(\"hi\"), setStr) " ; teval setStr env;;

(* Operazioni di controllo *)
print_string " -  IsEmpty(setInt) " ; teval (IsEmpty(setInt)) env;;
print_string " -  IsEmpty(setBool) " ; teval (IsEmpty(setBool)) env;;
print_string " -  ExistsIn(CstInt(1), setInt1) " ; teval (ExistsIn(CstInt(1), setInt1)) env;;
print_string " -  ExistsIn(CstInt(11), setInt1) " ; teval (ExistsIn(CstInt(11), setInt1)) env;;
print_string " -  ContainsSet(setInt1, setInt2) " ; teval (ContainsSet(setInt1, setInt2)) env;;
print_string " -  ContainsSet(setInt1, Remove(CstInt(1), setInt2)) " ; teval (ContainsSet(setInt1, Remove(CstInt(1), setInt2))) env;;

(* Operazioni su Insiemi *)
let setI = Intersection(setInt1, setInt2);;
let setU = Union(setInt1, setInt2);;
let setD = Difference(setInt1, setInt2);;
print_string " -  Intersection(setInt1, setInt2) " ; teval setI env;;
print_string " -  Union(setInt1, setInt2) " ; teval setU env;;
print_string " -  Difference(setInt1, setInt2) " ; teval setD env;;

(* Ricerca di Max e Min in un Insieme *)
print_string " -  MaxOf(setInt) " ; teval (MaxOf(setInt)) env;;
print_string " -  MinOf(setInt) " ; teval (MinOf(setInt)) env;;
print_string " -  MaxOf(setI) " ; teval (MaxOf(setI)) env;;
print_string " -  MinOf(setI) " ; teval (MinOf(setI)) env;;

(* Operazioni Funzionali *)
let pred_is2 = Fun("x", TInt, Ifthenelse(Eq(Den("x"),CstInt(2)),
                                CstTrue,
                                CstFalse));;
let fBitMap_2 = Fun("x", TInt, Times(Den("x"), CstInt(2)));;

print_string " -  For_all(pred_is2, setInt1) " ; teval (For_all(pred_is2, setInt1)) env;;
print_string " -  Exists(pred_is2, setInt1) " ; teval (Exists(pred_is2, setInt1)) env;;
print_string " -  Filter(pred_is2, setInt1) " ; teval (Filter(pred_is2, setInt1)) env;;
print_string " -  Map(fBitMap_2, setInt1) " ; teval (Map(fBitMap_2, setInt1)) env;;

print_string " -  For_all(pred_is2, setI) " ; teval (For_all(pred_is2, setI)) env;;
print_string " -  Exists(pred_is2, setI) " ; teval (Exists(pred_is2, setI)) env;;
print_string " -  Filter(pred_is2, setI) " ; teval (Filter(pred_is2, setI)) env;;
print_string " -  Map(fBitMap_2, setI) " ; teval (Map(fBitMap_2, setI)) env;;



(************************************** TEST RUNTIME ERRORS **************************************)

(*teval (Of(TInt, Elem(CstString("hello"),Elem(CstInt(2),Elem(CstInt(1),Nil))))) env;;*)
(*teval (Singleton(TString, CstInt(1))) env;;*)
(*teval (Put(CstString("hi"), setInt)) env;;*)
(*teval (Remove(CstString("hi"), setInt)) env;;*)
(*teval (IsEmpty(CstInt(1))) env;;*)
(*teval (ExistsIn(CstString("hello"), setInt1)) env;;*)
(*teval (ContainsSet(setInt1, setStr)) env;;*)
(*teval (MaxOf(setStr)) env;;*)
(*teval (MinOf(setStr)) env;;*)
(*teval (For_all(pred_is2, setStr)) env;;*)
(*teval (Exists(pred_is2, CstInt(1))) env;;*)
(*teval (Map(setInt, setInt)) env;;*)
(*teval (Map(pred_is2, setStr)) env;;*)