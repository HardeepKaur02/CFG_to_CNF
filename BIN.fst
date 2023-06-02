module BIN
open BASE

type bin_rule = _rule: (rule){List.Tot.length _rule._RHS <= 2}

val rev_len_lemma: #a:Type -> l: list a -> Lemma (List.Tot.length l = List.Tot.length (List.Tot.rev l))
let rev_len_lemma #a l = List.Tot.Properties.rev_acc_length l []

val tail_len_lemma: #a:Type -> l: list a{Cons? l} -> Lemma (List.Tot.length l = 1 + List.Tot.length (List.Tot.tl l))
let tail_len_lemma l = ()

val splitRule: rule_store: list bin_rule -> _rule:rule -> Tot (list bin_rule) (decreases %[List.Tot.length _rule._RHS])

let rec splitRule rule_store _rule= 
    if List.Tot.length _rule._RHS > 2 then (
        let old_len = List.Tot.length _rule._RHS in 
        let reverse = List.Tot.rev _rule._RHS in
        rev_len_lemma _rule._RHS;
        assert(List.Tot.length reverse = old_len); 
        let hd1::tl1 = reverse in
        tail_len_lemma reverse;
        assert(List.Tot.length tl1 = old_len - 1);
        let hd2::tl2 = tl1 in 
        tail_len_lemma tl1;
        assert(List.Tot.length tl2 = List.Tot.length tl1 - 1);
        assert(List.Tot.length tl2 = old_len - 2);
        let n = List.Tot.length rule_store in 
        let newLHS = NonTerm ((NonTerm?.s _rule._LHS)^(string_of_int n)) in
        let newRule:bin_rule = {_LHS = newLHS; 
                       _RHS = hd2::[hd1];
                       isStart = false} in 
        let modifiedRHS = List.Tot.append (List.Tot.rev tl2) [newLHS] in
        rev_len_lemma tl2;
        List.Tot.Properties.append_length (List.Tot.rev tl2) [newLHS];
        assert(List.Tot.length modifiedRHS = (List.Tot.length (List.Tot.rev tl2)) + 1);
        assert(List.Tot.length modifiedRHS = List.Tot.length tl2 + 1);
        assert(List.Tot.length modifiedRHS = old_len - 1);
        let modifiedRule = {_LHS = _rule._LHS;
                            _RHS = modifiedRHS;
                            isStart = _rule.isStart} in
        assert(List.Tot.length (modifiedRule._RHS) < List.Tot.length _rule._RHS);
        splitRule (List.Tot.append rule_store [newRule]) modifiedRule
    )
    else List.Tot.append [_rule] rule_store
                
val splitRules: list rule -> Tot (list bin_rule)

let splitRules rules = 
    List.Tot.fold_left splitRule [] rules 
