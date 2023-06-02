module START 
open BASE


val findStart: rules: list rule -> Tot string

let rec findStart rules = 
    match rules with 
    | hd::tl -> if hd.isStart then (get_name hd._LHS) else findStart tl 
    | [] -> ""
    

val removeStart: list rule -> list rule -> Tot (list rule) 
let rec removeStart rules_in rules_out = 
    match rules_in with 
    | [] -> rules_out  
    | hd::tl -> let hd2 = {_LHS = hd._LHS; _RHS = hd._RHS; isStart=false} in 
    removeStart tl (List.Tot.append rules_out [hd2])


val remove_len_lemma: l1:list rule -> l2:list rule -> Lemma(List.Tot.length (removeStart l1 l2) = List.Tot.length l1 + List.Tot.length l2)
let rec remove_len_lemma l1 l2 = 
    match l1 with 
    | [] -> ()
    | hd::tl -> tail_len_lemma l1; 
      assert(List.Tot.length l1 = List.Tot.length tl + 1);
      let hd2 = {_LHS = hd._LHS; _RHS = hd._RHS; isStart=false} in 
      let l2' = List.Tot.append l2 [hd2] in
      List.Tot.Properties.append_length l2 [hd2];
      assert(List.Tot.length l2' = List.Tot.length l2 + 1);
      remove_len_lemma tl l2'

// assumptions: 
// 1. if S is the start symbol, then S0 is not a NT in input grammar
// 2. there is a unique start symboll in the input grammar
val addStart: rules_in: list rule -> Tot (rules_out: list rule {List.Tot.existsb isStartRule rules_out /\ (List.Tot.length rules_out = List.Tot.length rules_in+1)})
let addStart rules = 
    let currStart = findStart rules in 
    let startRule = {_LHS = NonTerm (currStart^(string_of_int 0));
                     _RHS = [NonTerm currStart];
                     isStart = true} in
    let mod_rules = removeStart rules [] in 
    remove_len_lemma rules [];
    assert(List.Tot.length mod_rules = List.Tot.length rules);
    let final_rules = List.Tot.append rules [startRule] in
    assert(startRule.isStart=true);
    assert(isStartRule startRule);
    List.Tot.Properties.append_mem rules [startRule] startRule;
    assert(List.Tot.contains startRule final_rules);
    List.Tot.Properties.memP_existsb isStartRule final_rules;
    assert(List.Tot.existsb isStartRule final_rules);
    List.Tot.Properties.append_length rules [startRule];
    final_rules





// module Welcome
// (*open FSTar.List.Tot.Properties*)
// (*open FSTar.Math.Lib*)

// type node = 
//     | NonTerm: s:string -> node 
//     | Term: s:string -> node 

// type rule = { 
//     _LHS: x:node{NonTerm? x}; 
//     _RHS: list node; 
//     isStart: bool
// }

// type bin_rule = _rule: (rule){List.Tot.length _rule._RHS <= 2}

// type unit_rule = _rule: (rule){ (List.Tot.length _rule._RHS) = 1 && NonTerm? (List.Tot.hd _rule._RHS)}

// type non_unit_rule = _rule: (rule){ (List.Tot.length _rule._RHS) <> 1 || Term? (List.Tot.hd _rule._RHS)}


// val get_name: node -> Tot string
// let get_name n = match n with
//     | NonTerm s -> s
//     | Term s -> s

// val powerset: #a:Type -> list a -> Tot (list (list a))
// let rec powerset #a = function
//     | [] -> [[]]
//     | x::xs -> List.Tot.collect (fun subset -> [subset; List.Tot.append [x] subset]) (powerset xs)

// val remove_dup: #a:eqtype -> list a -> Tot (list a)
// let remove_dup l = 
//     let helper acc x = 
//         match acc with 
//             | [] -> [x]
//             | _ -> if List.Tot.contains x acc then acc else x::acc in 
//     List.Tot.fold_left helper [] l 

// val rev_len_lemma: #a:Type -> l: list a -> Lemma (List.Tot.length l = List.Tot.length (List.Tot.rev l))
// let rev_len_lemma #a l = List.Tot.Properties.rev_acc_length l []

// val tail_len_lemma: #a:Type -> l: list a{Cons? l} -> Lemma (List.Tot.length l = 1 + List.Tot.length (List.Tot.tl l))
// let tail_len_lemma l = ()


// /////////////////////////////////////////////UNIT//////////////////


// val isUnitRule: rule -> Tot bool 

// let isUnitRule r = 
//     List.Tot.length r._RHS = 1 && (NonTerm? (List.Tot.hd r._RHS))

// val helper: list node -> (list (node * node)) -> iter:nat -> Tot (list node) (decreases %[iter]) 


// (*val unit_is_Cons: l: list rule -> Lemma(forall r. List.Tot.contains r l && isUnitRule r ==> Cons? r._RHS) *)
// (*let rec unit_is_Cons l = match l with*)
// (*    | [] -> ()*)
// (*    | hd::tl -> unit_is_Cons tl*)


// let rec helper curr_unit_RHS unit_pairs iter = 
//     let l = List.Tot.filter (fun p -> List.Tot.contains (fst p) curr_unit_RHS) unit_pairs in 
//     let new_unit_RHS = remove_dup (List.Tot.append curr_unit_RHS (List.Tot.map snd l)) in 
//     if List.Tot.length curr_unit_RHS = List.Tot.length new_unit_RHS || iter<=1 then curr_unit_RHS  
//     else helper new_unit_RHS unit_pairs (iter-1)

// val get_unit_RHS: list (node * node) -> node -> Tot (node * list node)

// let get_unit_RHS unit_pairs x = 
//     let curr_RHS_list = List.Tot.map snd (List.Tot.filter (fun p -> (fst p) = x) unit_pairs) in 
//     let all_unit_RHS = helper curr_RHS_list unit_pairs (List.Tot.length unit_pairs) in 
//     (x,all_unit_RHS)

// val get_unit_pairs: list rule -> Tot (list (node * list node))

// let get_unit_pairs rules = 
//     let unit_rules = List.Tot.filter isUnitRule rules in 
//     List.Tot.Base.mem_filter_forall isUnitRule rules ;
//     assert(forall r. List.Tot.contains r unit_rules ==> isUnitRule r);
//     assert(forall r. isUnitRule r ==> List.Tot.length r._RHS = 1 );
//     assert(forall r. List.Tot.contains r unit_rules ==> List.Tot.length r._RHS = 1 );
//     assert(forall r. List.Tot.contains r unit_rules ==> (Cons? r._RHS) );
//     let unit_pairs = List.Tot.map (fun r -> (r._LHS, List.Tot.hd r._RHS)) unit_rules in 
//     let lhs_list = remove_dup (List.Tot.map fst unit_pairs) in 
//     List.Tot.map (get_unit_RHS unit_pairs) lhs_list 
    
// val rename: x:node{NonTerm? x} -> non_unit_rule -> Tot non_unit_rule  
// let rename x rul = {_LHS=x;_RHS=rul._RHS;isStart=rul.isStart}

// val newRules: list rule -> (x:node{NonTerm? x} * list node) -> Tot (list non_unit_rule) 
// let newRules rules unitTuple = 
//     let unitLHS = fst unitTuple in 
//     let unitRHS = snd unitTuple in  
//     let non_unit_rules = List.Tot.filter (fun r -> not (isUnitRule r)) rules in 
//     let req_rules = List.Tot.filter (fun r -> List.Tot.contains r._LHS unitRHS) non_unit_rules in 
//     List.Tot.map (rename unitLHS) req_rules 

// val deleteChainRules: l:(list rule){List.Tot.existsb (fun r -> r.isStart=true) l} -> Tot (list non_unit_rule)  

// let deleteChainRules rules = 
//     List.Tot.Properties.memP_existsb (fun r -> r.isStart=true) rules;
//     let startNT = (List.Tot.hd (List.Tot.filter (fun r -> r.isStart) rules))._LHS in 
//     let all_rules = remove_dup (List.Tot.collect (newRules rules) (get_unit_pairs rules)) in
//     // let all_non_unit_rules = filter (not isUnitRule) all_rules in 
//     List.Tot.map (fun r -> if r._LHS = startNT then {_LHS = r._LHS; _RHS = r._RHS; isStart=true} else r) all_rules 




// /////////////////////////////////////////////START//////////////////

// val findStart: rules: list rule -> Tot string

// let rec findStart rules = 
//     match rules with 
//     | hd::tl -> if hd.isStart then (get_name hd._LHS) else findStart tl 
//     | [] -> ""
    

// val removeStart: list rule -> list rule -> Tot (list rule) 
// let rec removeStart rules_in rules_out = 
//     match rules_in with 
//     | [] -> rules_out  
//     | hd::tl -> let hd2 = {_LHS = hd._LHS; _RHS = hd._RHS; isStart=false} in 
//     removeStart tl (List.Tot.append rules_out [hd2])


// val remove_len_lemma: l1:list rule -> l2:list rule -> Lemma(List.Tot.length (removeStart l1 l2) = List.Tot.length l1 + List.Tot.length l2)
// let rec remove_len_lemma l1 l2 = 
//     match l1 with 
//     | [] -> ()
//     | hd::tl -> tail_len_lemma l1; 
//       assert(List.Tot.length l1 = List.Tot.length tl + 1);
//       let hd2 = {_LHS = hd._LHS; _RHS = hd._RHS; isStart=false} in 
//       let l2' = List.Tot.append l2 [hd2] in
//       List.Tot.Properties.append_length l2 [hd2];
//       assert(List.Tot.length l2' = List.Tot.length l2 + 1);
//       remove_len_lemma tl l2'

// val addStart: rules_in: list rule -> Tot (rules_out: list rule {List.Tot.existsb (fun r -> r.isStart=true) rules_out /\ (List.Tot.length rules_out = List.Tot.length rules_in+1)})

// //assumption: if S is the start symbol, then S0 is not a NT in input grammar
// let addStart rules = 
//     let currStart = findStart rules in 
//     let startRule = {_LHS = NonTerm (currStart^(string_of_int 0));
//                      _RHS = [NonTerm currStart];
//                      isStart = true} in
//     let mod_rules = removeStart rules [] in 
//     remove_len_lemma rules [];
//     assert(List.Tot.length mod_rules = List.Tot.length rules);
//     let final_rules = List.Tot.append rules [startRule] in
//     assert(startRule.isStart=true);
//     List.Tot.Properties.append_mem rules [startRule] startRule;
//     assert(List.Tot.contains startRule final_rules);
//     List.Tot.Properties.memP_existsb (fun r -> r.isStart=true) final_rules;
//     assert(List.Tot.existsb (fun r -> r.isStart=true) final_rules);
//     List.Tot.Properties.append_length rules [startRule];
//     final_rules


// // returns true if RHS of a rule is not epsilon
// val not_nullable: r:rule -> Tot bool 
// let not_nullable r = not (List.isEmpty r._RHS) 

// // returns list of Non Terminals A s.t. A -> epsilon
// val nullables: list rule -> Tot (list string) 
// let nullables rules =
//     List.Tot.map (fun r -> NonTerm?.s r._LHS) (List.Tot.filter (fun r -> List.isEmpty r._RHS) rules)


// val filter_lemma: #a:Type -> l: list a -> Lemma(forall f. List.Tot.length (List.Tot.filter f l) <= List.Tot.length l)
// let rec filter_lemma l = match l with
//     | [] -> ()
//     | hd::tl -> filter_lemma tl

// // returns elements of list2, not present in list1 
// val complement: #a:eqtype -> l1:list a -> l2:list a -> Tot (l:list a{List.Tot.length l <= List.Tot.length l2})
// let complement list1 list2 = 
//     let res = List.Tot.filter (fun x-> not (List.Tot.mem x list1)) list2 in 
//     filter_lemma list2;
//     assert(List.Tot.length res <= List.Tot.length list2);
//     res

// // returns true if A -> C1C2...Cn where Ci are all nullable
// val is_nullable_weak: (list string) -> rule -> Tot bool
// let is_nullable_weak non_nullables r = 
//     List.Tot.for_all (fun e -> ((NonTerm? e) && not (List.Tot.contains (get_name e) non_nullables))) r._RHS 

// // returns list of non terminals in LHS of rules in the given list
// val get_all_NT: list rule -> list string -> Tot (list string)
// let rec get_all_NT rules curr_NT = 
//     match rules with 
//     | [] -> remove_dup(curr_NT)
//     | hd::tl -> get_all_NT tl ((NonTerm?.s hd._LHS)::curr_NT)
    
// // returns list of Non Terminals A s.t. A ->* epsilon doesn't hold
// val non_nullable_helper: list rule -> curr_non_null: list string -> Tot (list string) (decreases %[List.Tot.length curr_non_null])
// let rec non_nullable_helper rules curr_non_null = 
//     let null_rules = List.Tot.filter (is_nullable_weak curr_non_null) rules in
//     let new_null = get_all_NT null_rules [] in
//     let new_non_null = complement new_null curr_non_null in 
//     assert(List.Tot.length new_non_null <= List.Tot.length curr_non_null);
//     if List.Tot.length curr_non_null = List.Tot.length new_non_null then curr_non_null
//     else non_nullable_helper rules new_non_null

// val make_rule: x:node{NonTerm? x} -> bool -> list node -> Tot rule 
// let make_rule lhs isstart node_list = {_LHS=lhs; _RHS=node_list; isStart=isstart} 


// (*// returns a list of new rules that would replace an original rule, by considering all possibilities of nullable NTs in RHS *)
// (*val newRules: list string -> _rule:rule -> Tot (list rule) *)
// (*let newRules nullable_NT r = *)
// (*    let _RHS_NT = List.Tot.filter (NonTerm?) r._RHS in  *)
// (*    let nullable_RHS_NT = List.Tot.filter (fun x -> List.Tot.contains (get_name x) nullable_NT) _RHS_NT in *)
// (*    let non_nullable_RHS = List.Tot.filter (fun x -> not (List.Tot.contains x nullable_RHS_NT)) r._RHS in *)
// (*    let powerSet = powerset r._RHS in *)
// (*    let would_be_rules = List.Tot.filter (fun node_list -> List.Tot.for_all (fun e -> List.Tot.contains e node_list) non_nullable_RHS) powerSet in *)
// (*    List.Tot.map (make_rule r._LHS r.isStart) would_be_rules*)
// (**)
// (*// returns final rules after deleting epsilon rules*)
// (*val deleteEpsRule: list rule -> Tot (rules: list rule {forall r . List.Tot.mem r rules ==> (r.isStart || (not_nullable r))}) *)
// (*let deleteEpsRule rules = *)
// (*    let all_NT = get_all_NT rules [] in *)
// (*    let direct_null = nullables rules in*)
// (*    let not_direct_null = complement direct_null all_NT in *)
// (*    let all_non_null = non_nullable_helper rules not_direct_null in *)
// (*    let all_null = complement all_non_null all_NT in *)
// (*    let all_new_rules = List.Tot.map (newRules all_null) rules in *)
// (*    let flat_new_rules = List.Tot.flatten all_new_rules in *)
// (*    let final_rules = List.Tot.filter (fun r -> r.isStart || (not_nullable r)) flat_new_rules in *)
// (*    final_rules*)
// (**)
// (**)
// (**)
// (**)
// (**)
// (**)
// (**)






// (*type bin_rule = _rule: (rule){List.Tot.length _rule._RHS <= 2}*)
// (**)
// (**)
// (*val splitRule: rule_store: list bin_rule -> _rule:rule -> Tot (list bin_rule) (decreases %[List.Tot.length _rule._RHS])*)
// (**)
// (*let rec splitRule rule_store _rule= *)
// (*    if List.Tot.length _rule._RHS > 2 then (*)
// (*        let old_len = List.Tot.length _rule._RHS in *)
// (*        let reverse = List.Tot.rev _rule._RHS in*)
// (*        rev_len_lemma _rule._RHS;*)
// (*        assert(List.Tot.length reverse = old_len); *)
// (*        let hd1::tl1 = reverse in*)
// (*        tail_len_lemma reverse;*)
// (*        assert(List.Tot.length tl1 = old_len - 1);*)
// (*        let hd2::tl2 = tl1 in *)
// (*        tail_len_lemma tl1;*)
// (*        assert(List.Tot.length tl2 = List.Tot.length tl1 - 1);*)
// (*        assert(List.Tot.length tl2 = old_len - 2);*)
// (*        let n = List.Tot.length rule_store in *)
// (*        let newLHS = NonTerm ((NonTerm?.s _rule._LHS)^(string_of_int n)) in*)
// (*        let newRule:bin_rule = {_LHS = newLHS; *)
// (*                       _RHS = hd2::[hd1];*)
// (*                       isStart = false} in *)
// (*        let modifiedRHS = List.Tot.append (List.Tot.rev tl2) [newLHS] in*)
// (*        rev_len_lemma tl2;*)
// (*        List.Tot.Properties.append_length (List.Tot.rev tl2) [newLHS];*)
// (*        assert(List.Tot.length modifiedRHS = (List.Tot.length (List.Tot.rev tl2)) + 1);*)
// (*        assert(List.Tot.length modifiedRHS = List.Tot.length tl2 + 1);*)
// (*        assert(List.Tot.length modifiedRHS = old_len - 1);*)
// (*        let modifiedRule = {_LHS = _rule._LHS;*)
// (*                            _RHS = modifiedRHS;*)
// (*                            isStart = _rule.isStart} in*)
// (*        assert(List.Tot.length (modifiedRule._RHS) < List.Tot.length _rule._RHS);*)
// (*        splitRule (List.Tot.append rule_store [newRule]) modifiedRule*)
// (*    )*)
// (*    else List.Tot.append [_rule] rule_store*)
// (*                *)
// (*val splitRules: list rule -> Tot (list bin_rule)*)
// (**)
// (*let splitRules rules = *)
// (*    List.Tot.fold_left splitRule [] rules *)
// (**)
// (**)
// (**)








