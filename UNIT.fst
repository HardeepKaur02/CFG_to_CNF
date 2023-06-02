module UNIT
open BASE

val isUnitRule: rule -> Tot bool 

let isUnitRule r = 
    (List.Tot.length r._RHS = 1) && (NonTerm? (List.Tot.hd r._RHS))

type unit_rule = _rule: (rule){isUnitRule _rule}

type non_unit_rule = _rule: (rule){ not (isUnitRule _rule)}

val helper: list (x:node{NonTerm? x}) -> (list (x:node{NonTerm? x} * y:node{NonTerm? y})) -> iter:nat -> Tot (list (x:node{NonTerm? x})) (decreases %[iter]) 

let rec helper curr_unit_RHS unit_pairs iter = 
    let l = List.Tot.filter (fun p -> List.Tot.contains (fst p) curr_unit_RHS) unit_pairs in 
    let new_unit_RHS = remove_dup (List.Tot.append curr_unit_RHS (List.Tot.map snd l)) in 
    if List.Tot.length curr_unit_RHS = List.Tot.length new_unit_RHS || iter<=1 then curr_unit_RHS  
    else helper new_unit_RHS unit_pairs (iter-1)

val get_unit_RHS: list (x:node{NonTerm? x} * y:node{NonTerm? y}) -> x:node{NonTerm? x} -> Tot (x:node{NonTerm? x} * list (y:node{NonTerm? y}))

let get_unit_RHS unit_pairs x = 
    let curr_RHS_list = List.Tot.map snd (List.Tot.filter (fun p -> (fst p) = x) unit_pairs) in 
    let all_unit_RHS = helper curr_RHS_list unit_pairs (List.Tot.length unit_pairs) in 
    (x,all_unit_RHS)

val f: unit_rule -> Tot (x:node{NonTerm? x} * y: node{NonTerm? y})
let f r = (r._LHS,List.Tot.hd r._RHS)

val lift: l:(list rule){forall r. List.Tot.contains r l ==> isUnitRule r} -> Tot (list unit_rule)
let rec lift l = match l with 
    | [] -> []
    | hd::tl -> 
        assert(isUnitRule hd);
        assert((List.Tot.length hd._RHS = 1) && (NonTerm? (List.Tot.hd hd._RHS)));
        let nl:unit_rule = hd in nl::lift(tl)

val lift2: l:(list rule){forall r. List.Tot.contains r l ==> not (isUnitRule r)} -> Tot (list non_unit_rule)
let rec lift2 l = match l with 
    | [] -> []
    | hd::tl -> 
        assert(not (isUnitRule hd));
        let nl:non_unit_rule = hd in nl::lift2(tl)

val get_unit_pairs: list rule -> Tot (list ((x:node{NonTerm? x}) * (list (y:node{NonTerm? y})) ))

let get_unit_pairs rules = 
    let unit_rules = List.Tot.filter isUnitRule rules in 
    List.Tot.Base.mem_filter_forall isUnitRule rules ;
    let unit_rules: list unit_rule = lift unit_rules in 
    let unit_pairs = List.Tot.map f unit_rules in
    let lhs_list = remove_dup (List.Tot.map fst unit_pairs) in 
    List.Tot.map (get_unit_RHS unit_pairs) lhs_list 
    
val rename: x:node{NonTerm? x} -> non_unit_rule -> Tot non_unit_rule  
let rename x rul = {_LHS=x;_RHS=rul._RHS;isStart=rul.isStart}

val ff: list (x:node{NonTerm? x}) -> non_unit_rule -> Tot bool
let ff l r = List.Tot.contains r._LHS l

val new_Rules: list rule -> ((x:node{NonTerm? x}) * (list (y:node{NonTerm? y})) ) -> Tot (list non_unit_rule) 
let new_Rules rules unitTuple = 
    let unitLHS = fst unitTuple in 
    let unitRHS = snd unitTuple in  
    let non_unit_rules = List.Tot.filter (fun r -> not (isUnitRule r)) rules in 
    List.Tot.Base.mem_filter_forall (fun r -> not (isUnitRule r)) rules ;
    let non_unit_rules: list non_unit_rule = lift2 non_unit_rules in
    let req_rules = List.Tot.filter (ff unitRHS) non_unit_rules in 
    List.Tot.map (rename unitLHS) req_rules 

val exists_lemma: #a:eqtype -> f:(a->bool) -> l:(list a){List.Tot.existsb f l} -> Lemma (not (List.Tot.isEmpty (List.Tot.filter f l)))
let rec exists_lemma f l = match l with
    hd::tl -> if (f hd) then let res = (List.Tot.filter f l) in assert(List.Tot.contains hd res) else exists_lemma f tl

val modifyStart: x:node{NonTerm? x} -> non_unit_rule -> non_unit_rule
let modifyStart x r =
    if r._LHS = x then 
        let nr = {_LHS = r._LHS; _RHS = r._RHS; isStart=true} in
        assert(not (isUnitRule nr));
        nr
    else r

val deleteChainRules: l:(list rule){List.Tot.existsb isStartRule l} -> Tot (list non_unit_rule)  

let deleteChainRules rules = 
    let start_rule = List.Tot.filter isStartRule rules in 
    exists_lemma isStartRule rules;
    assert(not (List.Tot.isEmpty start_rule));
    let startNT = (List.Tot.hd start_rule)._LHS in 
    let all_rules: list non_unit_rule = remove_dup (List.Tot.collect (new_Rules rules) (get_unit_pairs rules)) in
    List.Tot.map (modifyStart startNT) all_rules 
