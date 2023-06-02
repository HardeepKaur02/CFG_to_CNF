module BASE

type node = 
    | NonTerm: s:string -> node 
    | Term: s:string -> node 

type rule = { 
    _LHS: x:node{NonTerm? x}; 
    _RHS: list node; 
    isStart: bool
}

val get_name: node -> Tot string
let get_name n = match n with
    | NonTerm s -> s
    | Term s -> s

val powerset: #a:Type -> list a -> Tot (list (list a))
let rec powerset #a = function
    | [] -> [[]]
    | x::xs -> List.Tot.collect (fun subset -> [subset; List.Tot.append [x] subset]) (powerset xs)

val remove_dup: #a:eqtype -> list a -> Tot (list a)
let remove_dup l = 
    let helper acc x = 
        match acc with 
            | [] -> [x]
            | _ -> if List.Tot.contains x acc then acc else x::acc in 
    List.Tot.fold_left helper [] l 

val isStartRule: rule -> Tot bool
let isStartRule r = r.isStart
