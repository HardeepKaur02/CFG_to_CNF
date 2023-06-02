module DEL
open BASE

// returns true if RHS of a rule is not epsilon
val not_nullable: r:rule -> Tot bool 
let not_nullable r = not (List.isEmpty r._RHS) 

// returns list of Non Terminals A s.t. A -> epsilon
val nullables: list rule -> Tot (list string) 
let nullables rules =
    List.Tot.map (fun r -> NonTerm?.s r._LHS) (List.Tot.filter (fun r -> List.isEmpty r._RHS) rules)

// length of a list obtained by applying a filter is less than original
val filter_lemma: #a:Type -> l: list a -> Lemma(forall f. List.Tot.length (List.Tot.filter f l) <= List.Tot.length l)
let rec filter_lemma l = match l with
    | [] -> ()
    | hd::tl -> filter_lemma tl

// returns elements of list2, not present in list1 
val complement: #a:eqtype -> l1:list a -> l2:list a -> Tot (l:list a{List.Tot.length l <= List.Tot.length l2})
let complement list1 list2 = 
    let res = List.Tot.filter (fun x-> not (List.Tot.mem x list1)) list2 in 
    filter_lemma list2;
    assert(List.Tot.length res <= List.Tot.length list2);
    res

// returns true if A -> C1C2...Cn where Ci are all nullable
val is_nullable_weak: (list string) -> rule -> Tot bool
let is_nullable_weak non_nullables r = 
    List.Tot.for_all (fun e -> ((NonTerm? e) && not (List.Tot.contains (get_name e) non_nullables))) r._RHS 

// returns list of non terminals in LHS of rules in the given list
val get_all_NT: list rule -> list string -> Tot (list string)
let rec get_all_NT rules curr_NT = 
    match rules with 
    | [] -> remove_dup(curr_NT)
    | hd::tl -> get_all_NT tl ((NonTerm?.s hd._LHS)::curr_NT)
    
// returns list of Non Terminals A s.t. A ->* epsilon doesn't hold
val non_nullable_helper: list rule -> curr_non_null: list string -> Tot (list string) (decreases %[List.Tot.length curr_non_null])
let rec non_nullable_helper rules curr_non_null = 
    let null_rules = List.Tot.filter (is_nullable_weak curr_non_null) rules in
    let new_null = get_all_NT null_rules [] in
    let new_non_null = complement new_null curr_non_null in 
    assert(List.Tot.length new_non_null <= List.Tot.length curr_non_null);
    if List.Tot.length curr_non_null = List.Tot.length new_non_null then curr_non_null
    else non_nullable_helper rules new_non_null

// packs the arguments into a rule
val make_rule: x:node{NonTerm? x} -> bool -> list node -> Tot rule 
let make_rule lhs isstart node_list = {_LHS=lhs; _RHS=node_list; isStart=isstart} 


// returns a list of new rules that would replace an original rule, by considering all possibilities of nullable NTs in RHS 
val newRules: list string -> _rule:rule -> Tot (list rule) 
let newRules nullable_NT r = 
    let _RHS_NT = List.Tot.filter (NonTerm?) r._RHS in  
    let nullable_RHS_NT = List.Tot.filter (fun x -> List.Tot.contains (get_name x) nullable_NT) _RHS_NT in 
    let non_nullable_RHS = List.Tot.filter (fun x -> not (List.Tot.contains x nullable_RHS_NT)) r._RHS in 
    let powerSet = powerset r._RHS in 
    let would_be_rules = List.Tot.filter (fun node_list -> List.Tot.for_all (fun e -> List.Tot.contains e node_list) non_nullable_RHS) powerSet in 
    List.Tot.map (make_rule r._LHS r.isStart) would_be_rules

// returns final rules after deleting epsilon rules
val deleteEpsRule: list rule -> Tot (rules: list rule {forall r . List.Tot.mem r rules ==> (r.isStart || (not_nullable r))}) 
let deleteEpsRule rules = 
    let all_NT = get_all_NT rules [] in 
    let direct_null = nullables rules in
    let not_direct_null = complement direct_null all_NT in 
    let all_non_null = non_nullable_helper rules not_direct_null in 
    let all_null = complement all_non_null all_NT in 
    let all_new_rules = List.Tot.map (newRules all_null) rules in 
    let flat_new_rules = List.Tot.flatten all_new_rules in 
    let final_rules = List.Tot.filter (fun r -> r.isStart || (not_nullable r)) flat_new_rules in 
    final_rules

