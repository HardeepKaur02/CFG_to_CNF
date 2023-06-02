module TERM 
open BASE

let isTermRule r = 
    (List.Tot.length r._RHS = 1) || (List.Tot.for_all NonTerm? r._RHS)

type term_rule = _rule: (rule){isTermRule _rule}


val g1: node -> Tot (x:node{NonTerm? x} * (list term_rule))
let g1 x = if Term? x then(
                        let new_NT = NonTerm (get_name x) in 
                        let new_rul = {_LHS= new_NT; _RHS= [x]; isStart = false} in 
                        assert(List.Tot.length new_rul._RHS=1);
                        assert(isTermRule new_rul);
                        (new_NT,[new_rul]) 
                        )
                        else (x,[])

val g: l:(list node) -> Tot (list (x:node{NonTerm? x} * (list term_rule)))
let g rhs = List.Tot.map g1 rhs

val forget: pred:(node -> Tot bool) -> x:node{pred x} -> node
let forget p x = x

val modify: rule -> Tot (list term_rule)

let modify r = 
    if List.Tot.length r._RHS = 1 && (Term? (List.Tot.hd r._RHS)) then (assert(isTermRule r); [r]) else(
        let nt_and_newrules = g r._RHS in 
        let modifiedRHS: list (x:node{NonTerm? x}) = List.Tot.map fst nt_and_newrules in 
        let l' = List.Tot.filter NonTerm? (List.Tot.map (forget NonTerm?) modifiedRHS) in
        List.Tot.Base.mem_filter_forall NonTerm? (List.Tot.map (forget NonTerm?) modifiedRHS) ;
        assert(forall x . List.Tot.memP x l' ==> NonTerm? x);
        List.Tot.Base.for_all_mem NonTerm? l';
        assert(List.Tot.for_all NonTerm? l');
        let modifiedRule = {_LHS= r._LHS; _RHS= l'; isStart= r.isStart} in 
        assert(isTermRule modifiedRule);
        modifiedRule::(List.Tot.flatten (List.Tot.map snd nt_and_newrules))
    )

val modifyRules: list rule -> Tot (list term_rule)

let modifyRules rules =
    let rule_list = List.Tot.map modify rules in 
    remove_dup (List.Tot.flatten rule_list)
