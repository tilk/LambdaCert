(* Should be integrated with LibBag *)
Require Import Utils.
Require Import LibTactics LibLogic LibList LibOperation LibRelation.
Require Export LibBag.
Generalizable Variables A B T U.

(* TODO should go to LibBag later *)
(** printing \c #⊆# *)
(** printing \u #∪# *)
(** printing \n #∩# *)
(** printing \{} #Ø# *)
(** printing \in #∈# *)
(** printing \notin #∉# *)

Class BagFromList A T := { from_list : list A -> T }.
Class BagToList A T := { to_list : T -> list A }.
Class BagReadOption A B T := { read_option : T -> A -> option B }. 
Class BagFresh A T := { fresh : T -> A }.

Notation "m \( x ?)" := (read_option m x)
  (at level 33, format "m \( x ?)") : container_scope.

Class From_list_empty `{BagFromList A T} `{BagEmpty T} :=
    { from_list_empty : from_list nil = \{} }.

Class From_list_single `{BagFromList A T} `{BagUnion T} `{BagSingle A T} :=
    { from_list_single : forall L x, from_list (x :: L) = \{x} \u from_list L }.

Class From_list_update `{BagFromList (A * B) T} `{BagUpdate A B T} :=
    { from_list_update : forall L k x, from_list ((k, x) :: L) = from_list L \(k := x) }.

Class From_list_in_eq `{BagFromList A T} `{BagIn A T} := 
    { from_list_in_eq : forall L x, x \in from_list L = Mem x L }.

Class From_list_in `{BagFromList A T} `{BagIn A T} := 
    { from_list_in : forall L x, x \in from_list L -> Mem x L }.

Class From_list_in_inv `{BagFromList A T} `{BagIn A T} := 
    { from_list_in_inv : forall L x, Mem x L -> x \in from_list L }.

Class To_list_in_eq `{BagToList A T} `{BagIn A T} := 
    { to_list_in_eq : forall S x, Mem x (to_list S) = x \in S }.

Class To_list_in `{BagToList A T} `{BagIn A T} := 
    { to_list_in : forall S x, Mem x (to_list S) -> x \in S }.

Class To_list_in_inv `{BagToList A T} `{BagIn A T} := 
    { to_list_in_inv : forall S x, x \in S -> Mem x (to_list S) }.

Class From_to_list_id `{BagFromList A T} `{BagToList A T} :=
    { from_to_list_id : forall S, from_list (to_list S) = S }.

Class Incl_in_eq `{BagIn A T, BagIncl T} :=
    { incl_in_eq : forall E F, E \c F = (forall x, x \in E -> x \in F) }.

Class Incl_in_inv `{BagIn A T, BagIncl T} :=
    { incl_in_inv : forall E F, (forall x, x \in E -> x \in F) -> E \c F }.

Class Update_empty `{BagEmpty T} `{BagUpdate A B T} `{BagSingleBind A B T} := 
    { update_empty : forall k x, \{} \(k := x) = (k \:= x) }.

Class Update_union_assoc `{BagUpdate A B T} `{BagUnion T} :=
    { update_union_assoc : forall M1 M2 k x, M1 \(k := x) \u M2 = (M1 \u M2) \(k := x) }.

Class Single_bind_union `{BagSingleBind A B T} `{BagUpdate A B T} `{BagUnion T} :=
    { single_bind_union : forall M k x, (k \:= x) \u M = M \(k := x) }.

Class Remove_empty_l `{BagEmpty T} `{BagRemove T T} :=
    { remove_empty_l : absorb_l remove empty }.

Class Remove_empty_r `{BagEmpty T} `{BagRemove T T} :=
    { remove_empty_r : neutral_r remove empty }.

Class Union_inter_distrib_l `{BagUnion T} `{BagInter T} :=
    { union_inter_distrib_l : distrib_l union inter }.

Class Union_inter_distrib_r `{BagUnion T} `{BagInter T} :=
    { union_inter_distrib_r : distrib_r union inter }.

Class Inter_union_distrib_l `{BagUnion T} `{BagInter T} :=
    { inter_union_distrib_l : distrib_l inter union }.

Class Inter_union_distrib_r `{BagUnion T} `{BagInter T} :=
    { inter_union_distrib_r : distrib_r inter union }.

Class Remove_union_distrib_r `{BagUnion T} `{BagRemove T T} :=
    { remove_union_distrib_r : distrib_r remove union }.

Class Remove_inter_distrib_r `{BagInter T} `{BagRemove T T} :=
    { remove_inter_distrib_r : distrib_r remove inter }.

Class Disjoint_inter_eq `{BagDisjoint T} `{BagInter T} `{BagEmpty T} :=
    { disjoint_inter_eq : forall E F, E \# F = (E \n F = \{}) }.

Class Disjoint_inter `{BagDisjoint T} `{BagInter T} `{BagEmpty T} :=
    { disjoint_inter : forall E F, E \# F -> E \n F = \{} }.

Class Disjoint_inter_inv `{BagDisjoint T} `{BagInter T} `{BagEmpty T} :=
    { disjoint_inter_inv : forall E F, E \n F = \{} -> E \# F }.

Class Disjoint_in_eq `{BagDisjoint T} `{BagIn A T} :=
    { disjoint_in_eq : forall E F, E \# F = (forall x, x \in E -> x \notin F) }.

Class Disjoint_in `{BagDisjoint T} `{BagIn A T} :=
    { disjoint_in : forall E F x, E \# F -> x \in E -> x \notin F }.

Class Disjoint_in_inv `{BagDisjoint T} `{BagIn A T} :=
    { disjoint_in_inv : forall E F, (forall x, x \in E -> x \notin F) -> E \# F }.

Class Disjoint_sym `{BagDisjoint T} :=
    { disjoint_sym : sym disjoint }.

(* Extensionality for maps *)
Class Binds_double_eq `{BagBinds A B T} :=
    { binds_double_eq : forall E F, (forall k x, binds E k x = binds F k x) -> E = F }.

Class Binds_double `{BagBinds A B T} :=
    { binds_double : forall E F, (forall k x, binds E k x <-> binds F k x) -> E = F }.

Class Binds_deterministic `{BagBinds A B T} :=
    { binds_deterministic : forall E k x y, binds E k x -> binds E k y -> x = y }.

(***** PROPERTIES RELATED TO BINDS *****)

(* from_list *)
Class From_list_binds_eq `{BagFromList (A * B) T} `{BagBinds A B T} := 
    { from_list_binds_eq : forall L k x, binds (from_list L) k x = Assoc k x L }.

Class From_list_binds `{BagFromList (A * B) T} `{BagBinds A B T} := 
    { from_list_binds : forall L k x, binds (from_list L) k x -> Assoc k x L }.

Class From_list_binds_inv `{BagFromList (A * B) T} `{BagBinds A B T} := 
    { from_list_binds_inv : forall L k x, Assoc k x L -> binds (from_list L) k x }.

(* to_list *)
Class To_list_binds_eq `{BagToList (A * B) T} `{BagBinds A B T} := 
    { to_list_binds_eq : forall S k x, Assoc k x (to_list S) = binds S k x }.

Class To_list_binds `{BagToList (A * B) T} `{BagBinds A B T} := 
    { to_list_binds : forall S k x, Assoc k x (to_list S) -> binds S k x }.

Class To_list_binds_inv `{BagToList (A * B) T} `{BagBinds A B T} := 
    { to_list_binds_inv : forall S k x, binds S k x -> Assoc k x (to_list S) }.

(* read_option *)
Class Read_option_binds_eq `{BagReadOption A B T} `{BagBinds A B T} :=
    { read_option_binds_eq : forall M k x, (M \(k?) = Some x) = binds M k x }.

Class Read_option_binds `{BagReadOption A B T} `{BagBinds A B T} :=
    { read_option_binds : forall M k x, M \(k?) = Some x -> binds M k x }.

Class Read_option_binds_inv `{BagReadOption A B T} `{BagBinds A B T} :=
    { read_option_binds_inv : forall M k x, binds M k x -> M \(k?) = Some x }.

Class Read_option_not_index_eq `{BagReadOption A B T} `{BagIndex T A} :=
    { read_option_not_index_eq : forall M k, (M \(k?) = None) = ~index M k }.

Class Read_option_not_index `{BagReadOption A B T} `{BagIndex T A} :=
    { read_option_not_index : forall M k, M \(k?) = None -> ~index M k }.

Class Read_option_not_index_inv `{BagReadOption A B T} `{BagIndex T A} :=
    { read_option_not_index_inv : forall M k, ~index M k -> M \(k?) = None }.

(* empty *)
Class Binds_empty_eq `{BagBinds A B T} `{BagEmpty T} :=
    { binds_empty_eq : forall k x, binds \{} k x = False }.

Class Binds_empty `{BagBinds A B T} `{BagEmpty T} :=
    { binds_empty : forall k x, ~binds \{} k x }.

(* single_bind *)
Class Binds_single_bind_eq `{BagBinds A B T} `{BagSingleBind A B T} :=
    { binds_single_bind_eq : forall k k' x x', binds (k' \:= x') k x = (k = k' /\ x = x') }.

Class Binds_single_bind_same_eq `{BagBinds A B T} `{BagSingleBind A B T} :=
    { binds_single_bind_same_eq : forall k x x', binds (k \:= x') k x = (x = x') }.

Class Binds_single_bind_same `{BagBinds A B T} `{BagSingleBind A B T} :=
    { binds_single_bind_same : forall k x, binds (k \:= x) k x }.

Class Binds_single_bind_same_inv `{BagBinds A B T} `{BagSingleBind A B T} :=
    { binds_single_bind_same_inv : forall k x x', binds (k \:= x') k x -> (x = x') }.

Class Binds_single_bind_diff_eq `{BagBinds A B T} `{BagSingleBind A B T} :=
    { binds_single_bind_diff_eq : forall k k' x x', k <> k' -> binds (k' \:= x') k x = False }.

Class Binds_single_bind_diff `{BagBinds A B T} `{BagSingleBind A B T} :=
    { binds_single_bind_diff : forall k k' x x', k <> k' -> ~binds (k' \:= x') k x }.

(* union *)
Class Binds_union_eq `{BagBinds A B T} `{BagIndex T A} `{BagUnion T} :=
    { binds_union_eq : forall M1 M2 k x, binds (M1 \u M2) k x = (binds M1 k x \/ ~index M1 k /\ binds M2 k x) }.

Class Binds_union_l `{BagBinds A B T} `{BagUnion T} :=
    { binds_union_l : forall M1 M2 k x, binds M1 k x -> binds (M1 \u M2) k x }.

Class Binds_union_r `{BagBinds A B T} `{BagIndex T A} `{BagUnion T} :=
    { binds_union_r : forall M1 M2 k x, ~index M1 k -> binds M2 k x -> binds (M1 \u M2) k x }.

Class Binds_union_inv `{BagBinds A B T} `{BagIndex T A} `{BagUnion T} :=
    { binds_union_inv : forall M1 M2 k x, binds (M1 \u M2) k x -> binds M1 k x \/ ~index M1 k /\ binds M2 k x }.

(* remove *)
Class Binds_remove_eq `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1} :=
    { binds_remove_eq : forall M S k x, binds (M \- S) k x = (binds M k x /\ k \notin S) }.

Class Binds_remove_notin_eq `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1} :=
    { binds_remove_notin_eq : forall M S k x, k \notin S -> binds (M \- S) k x = binds M k x }.

Class Binds_remove_notin `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1} :=
    { binds_remove_notin : forall M S k x, k \notin S -> binds M k x -> binds (M \- S) k x }.

Class Binds_remove_notin_inv `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1} :=
    { binds_remove_notin_inv : forall M S k x, k \notin S -> binds (M \- S) k x -> binds M k x }.

Class Binds_remove_in_eq `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1} :=
    { binds_remove_in_eq : forall M S k x, k \in S -> binds (M \- S) k x = False }.

Class Binds_remove_in `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1} :=
    { binds_remove_in : forall M S k x, k \in S -> ~binds (M \- S) k x }.

Class Binds_remove_inv `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1} :=
    { binds_remove_inv : forall M S k x, binds (M \- S) k x -> binds M k x /\ k \notin S }.

(* restrict *)
Class Binds_restrict_eq `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1} :=
    { binds_restrict_eq : forall M S k x, binds (M \| S) k x = (binds M k x /\ k \in S) }.

Class Binds_restrict_in_eq `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1} :=
    { binds_restrict_in_eq : forall M S k x, k \in S -> binds (M \| S) k x = binds M k x }.

Class Binds_restrict_in `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1} :=
    { binds_restrict_in : forall M S k x, k \in S -> binds M k x -> binds (M \| S) k x }.

Class Binds_restrict_in_inv `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1} :=
    { binds_restrict_in_inv : forall M S k x, k \in S -> binds (M \| S) k x -> binds M k x }.

Class Binds_restrict_notin_eq `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1} :=
    { binds_restrict_notin_eq : forall M S k x, k \notin S -> binds (M \| S) k x = False }.

Class Binds_restrict_notin `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1} :=
    { binds_restrict_notin : forall M S k x, k \notin S -> ~binds (M \| S) k x }.

Class Binds_restrict_inv `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1} :=
    { binds_restrict_inv : forall M S k x, binds (M \| S) k x -> binds M k x /\ k \in S }.

(* update *)
Class Binds_update_eq `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_eq : forall M k k' x x', 
        binds (M \(k' := x')) k x = (k = k' /\ x = x' \/ k <> k' /\ binds M k x) }.

Class Binds_update_same_eq `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_same_eq : forall M k x x', binds (M \(k := x)) k x' = (x = x') }.

Class Binds_update_same `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_same : forall M k x, binds (M \(k := x)) k x }.

Class Binds_update_same_inv `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_same_inv : forall M k x x', binds (M \(k := x)) k x' -> x = x' }.

Class Binds_update_diff_eq `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_diff_eq : forall M k k' x x', k <> k' -> binds (M \(k' := x')) k x = binds M k x }.

Class Binds_update_diff `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_diff : forall M k k' x x', k <> k' -> binds M k x -> binds (M \(k' := x')) k x }.

Class Binds_update_diff_inv `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_diff_inv : forall M k k' x x', k <> k' -> binds (M \(k' := x')) k x -> binds M k x }.

(* disjoint *)

Class Disjoint_binds_eq `{BagDisjoint T} `{BagBinds A B T} :=
    { disjoint_binds_eq : forall E F, E \# F = (forall k x x', binds E k x -> ~binds F k x') }.

Class Disjoint_binds `{BagDisjoint T} `{BagBinds A B T} :=
    { disjoint_binds : forall E F k x x', E \# F -> binds E k x -> ~binds F k x' }.

Class Disjoint_binds_inv `{BagDisjoint T} `{BagBinds A B T} :=
    { disjoint_binds_inv : forall E F, (forall k x x', binds E k x -> ~binds F k x') -> E \# F }.

(***** PROPERTIES RELATED TO INDEX *****)

(* index *)
Class Index_binds_eq `{BagIndex T A} `{BagBinds A B T} :=
    { index_binds_eq : forall M k, index M k = exists x, binds M k x }.

Class Index_binds `{BagIndex T A} `{BagBinds A B T} :=
    { index_binds : forall M k, index M k -> exists x, binds M k x }.

Class Index_binds_inv `{BagIndex T A} `{BagBinds A B T} :=
    { index_binds_inv : forall M k x, binds M k x -> index M k }.

(* empty *)
Class Index_empty_eq `{BagIndex T A} `{BagEmpty T} :=
    { index_empty_eq : forall k, index \{} k = False }.

Class Index_empty `{BagIndex T A} `{BagEmpty T} :=
    { index_empty : forall k, ~index \{} k }.

(* single *)
Class Index_single_bind_eq `{BagIndex T A} `{BagSingleBind A B T} :=
    { index_single_bind_eq : forall k k' x', index (k' \:= x') k = (k = k') }.

Class Index_single_bind_same_eq `{BagIndex T A} `{BagSingleBind A B T} :=
    { index_single_bind_same_eq : forall k x, index (k \:= x) k = True }.

Class Index_single_bind_same `{BagIndex T A} `{BagSingleBind A B T} :=
    { index_single_bind_same : forall k x, index (k \:= x) k }.

Class Index_single_bind_diff_eq `{BagIndex T A} `{BagSingleBind A B T} :=
    { index_single_bind_diff_eq : forall k k' x', k <> k' -> index (k' \:= x') k = False }. 

Class Index_single_bind_diff `{BagIndex T A} `{BagSingleBind A B T} :=
    { index_single_bind_diff : forall k k' x', k <> k' -> ~index (k' \:= x') k }. 

(* union *)
Class Index_union_eq `{BagIndex T A} `{BagUnion T} :=
    { index_union_eq : forall M1 M2 k, index (M1 \u M2) k = (index M1 k \/ index M2 k) }.

Class Index_union_l `{BagIndex T A} `{BagUnion T} :=
    { index_union_l : forall M1 M2 k, index M1 k -> index (M1 \u M2) k }.

Class Index_union_r `{BagIndex T A} `{BagUnion T} :=
    { index_union_r : forall M1 M2 k, index M2 k -> index (M1 \u M2) k }.

Class Index_union_inv `{BagIndex T A} `{BagUnion T} :=
    { index_union_inv : forall M1 M2 k, index (M1 \u M2) k -> index M1 k \/ index M2 k }.

(* remove *)
Class Index_remove_eq `{BagIndex T A} `{BagIn A T1} `{BagRemove T T1} :=
    { index_remove_eq : forall M S k, index (M \- S) k = (index M k /\ k \notin S) }.

Class Index_remove_in_eq `{BagIndex T A} `{BagIn A T1} `{BagRemove T T1} :=
    { index_remove_in_eq : forall M S k, k \in S -> index (M \- S) k = False }.

Class Index_remove_in `{BagIndex T A} `{BagIn A T1} `{BagRemove T T1} :=
    { index_remove_in : forall M S k, k \in S -> ~index (M \- S) k }.

Class Index_remove_notin_eq `{BagIndex T A} `{BagIn A T1} `{BagRemove T T1} :=
    { index_remove_notin_eq : forall M S k, k \notin S -> index (M \- S) k = index M k }.

Class Index_remove_notin `{BagIndex T A} `{BagIn A T1} `{BagRemove T T1} :=
    { index_remove_notin : forall M S k, k \notin S -> index M k -> index (M \- S) k }.

Class Index_remove_notin_inv `{BagIndex T A} `{BagIn A T1} `{BagRemove T T1} :=
    { index_remove_notin_inv : forall M S k, k \notin S -> index (M \- S) k -> index M k }.

(* restrict *)
Class Index_restrict_eq `{BagIndex T A} `{BagIn A T1} `{BagRestrict T T1} :=
    { index_restrict_eq : forall M S k, index (M \| S) k = (index M k /\ k \in S) }.

Class Index_restrict_in_eq `{BagIndex T A} `{BagIn A T1} `{BagRestrict T T1} :=
    { index_restrict_in_eq : forall M S k, k \in S -> index (M \| S) k = index M k }.

Class Index_restrict_in `{BagIndex T A} `{BagIn A T1} `{BagRestrict T T1} :=
    { index_restrict_in : forall M S k, k \in S -> index M k -> index (M \| S) k }.

Class Index_restrict_in_inv `{BagIndex T A} `{BagIn A T1} `{BagRestrict T T1} :=
    { index_restrict_in_inv : forall M S k, k \in S -> index (M \| S) k -> index M k }.

Class Index_restrict_notin_eq `{BagIndex T A} `{BagIn A T1} `{BagRestrict T T1} :=
    { index_restrict_notin_eq : forall M S k, k \notin S -> index (M \| S) k = False }.

Class Index_restrict_notin `{BagIndex T A} `{BagIn A T1} `{BagRestrict T T1} :=
    { index_restrict_notin : forall M S k, k \notin S -> ~index (M \| S) k }.

(* update *)
Class Index_update_eq `{BagIndex T A} `{BagUpdate A B T} :=
    { index_update_eq : forall M k k' x', index (M \(k' := x')) k = (index M k \/ k = k') }.

Class Index_update_same_eq `{BagIndex T A} `{BagUpdate A B T} :=
    { index_update_same_eq : forall M k x, index (M \(k := x)) k = True }.

Class Index_update_same `{BagIndex T A} `{BagUpdate A B T} :=
    { index_update_same : forall M k x, index (M \(k := x)) k }.

Class Index_update_index `{BagIndex T A} `{BagUpdate A B T} :=
    { index_update_index : forall M k k' x', index M k -> index (M \(k' := x')) k }.

Class Index_update_diff_eq `{BagIndex T A} `{BagUpdate A B T} :=
    { index_update_diff_eq : forall M k k' x', k <> k' -> index (M \(k' := x')) k = index M k }.

Class Index_update_diff `{BagIndex T A} `{BagUpdate A B T} :=
    { index_update_diff : forall M k k' x', k <> k' -> index M k -> index (M \(k' := x')) k }.

Class Index_update_diff_inv `{BagIndex T A} `{BagUpdate A B T} :=
    { index_update_diff_inv : forall M k k' x', k <> k' -> index (M \(k' := x')) k -> index M k }.

(* dom *)

Class Dom_index_eq `{BagIndex T A} `{BagDom T T1} `{BagIn A T1} :=
    { dom_index_eq : forall M x, x \in dom M = index M x }.

Class Dom_index `{BagIndex T A} `{BagDom T T1} `{BagIn A T1} :=
    { dom_index : forall M x, x \in dom M -> index M x }.

Class Dom_index_inv `{BagIndex T A} `{BagDom T T1} `{BagIn A T1} :=
    { dom_index_inv : forall M x, index M x -> x \in dom M }.

Class Dom_empty `{BagEmpty T} `{BagEmpty T1} `{BagDom T T1} :=
    { dom_empty : dom \{} = \{} }.

Class Dom_single_bind `{BagSingleBind A B T} `{BagSingle A T1} `{BagDom T T1} :=
    { dom_single_bind : forall k v, dom (k \:= v) = \{k} }.

Class Dom_union `{BagUnion T} `{BagUnion T1} `{BagDom T T1} :=
    { dom_union : forall M1 M2, dom (M1 \u M2) = dom M1 \u dom M2 }.

Class Dom_remove `{BagRemove T T1} `{BagRemove T1 T1} `{BagDom T T1} :=
    { dom_remove : forall M S, dom (M \- S) = dom M \- S }.

Class Dom_restrict `{BagRestrict T T1} `{BagInter T1} `{BagDom T T1} :=
    { dom_restrict : forall M S, dom (M \| S) = dom M \n S }.

Class Dom_update `{BagUpdate A B T} `{BagSingle A T1} `{BagUnion T1} `{BagDom T T1} :=
    { dom_update : forall M k v, dom (M \(k := v)) = \{k} \u dom M }.

(* disjoint *)

Class Disjoint_index_eq `{BagDisjoint T} `{BagIndex T A} :=
    { disjoint_index_eq : forall E F, disjoint E F = (forall x, index E x -> ~index F x) }.

Class Disjoint_index `{BagDisjoint T} `{BagIndex T A} :=
    { disjoint_index : forall E F x, disjoint E F -> index E x -> ~index F x }.

Class Disjoint_index_inv `{BagDisjoint T} `{BagIndex T A} :=
    { disjoint_index_inv : forall E F, (forall x, index E x -> ~index F x) -> disjoint E F }.

(* fresh *)
Class Fresh_index_eq `{BagIndex T A} `{BagFresh A T} :=
    { fresh_index_eq : forall M, index M (fresh M) = False }.

Class Fresh_index `{BagIndex T A} `{BagFresh A T} :=
    { fresh_index : forall M, ~index M (fresh M) }.

(* incl *)
Class Incl_binds_eq `{BagIncl T} `{BagBinds A B T} :=
    { incl_binds_eq : forall M1 M2, M1 \c M2 = (forall k x, binds M1 k x -> binds M2 k x) }.

Class Incl_binds `{BagIncl T} `{BagBinds A B T} :=
    { incl_binds : forall M1 M2 k x, M1 \c M2 -> binds M1 k x -> binds M2 k x }.

Class Incl_binds_inv `{BagIncl T} `{BagBinds A B T} :=
    { incl_binds_inv : forall M1 M2, (forall k x, binds M1 k x -> binds M2 k x) -> M1 \c M2 }.

Class Incl_index `{BagIncl T} `{BagIndex T A} :=
    { incl_index : forall M1 M2 k, M1 \c M2 -> index M1 k -> index M2 k }.

Class Update_nindex_incl `{BagIncl T} `{BagUpdate A B T} `{BagIndex T A} :=
    { update_nindex_incl : forall M k x, ~index M k -> M \c M\(k := x) }.

Class Remove_incl `{BagIncl T} `{BagRemove T T1} :=
    { remove_incl : forall M S, M \- S \c M }.

Class Restrict_incl `{BagIncl T} `{BagRestrict T T1} :=
    { restrict_incl : forall M S, M \| S \c M }.

Hint Rewrite 
    @in_empty_eq @in_single_eq @in_union_eq @in_inter_eq
    @in_remove_eq @from_list_in_eq @to_list_in_eq
    using (eauto with typeclass_instances) : rew_in_eq.

Tactic Notation "rew_in_eq" :=
    autorewrite with rew_in_eq.
Tactic Notation "rew_in_eq" "in" hyp(H) :=
    autorewrite with rew_in_eq in H.
Tactic Notation "rew_in_eq" "in" "*" :=
    autorewrite with rew_in_eq in *.

Tactic Notation "rew_in_eq" "~" :=
    rew_in_eq; auto_tilde.
Tactic Notation "rew_in_eq" "*" :=
    rew_in_eq; auto_star.
Tactic Notation "rew_in_eq" "~" "in" hyp(H) :=
    rew_in_eq in H; auto_tilde.
Tactic Notation "rew_in_eq" "*" "in" hyp(H) :=
    rew_in_eq in H; auto_star.

Hint Rewrite 
    @index_empty_eq @index_single_bind_eq @index_union_eq 
    @index_remove_eq @index_restrict_eq @index_update_eq
    using (eauto with typeclass_instances) : rew_index_eq.

Tactic Notation "rew_index_eq" :=
    autorewrite with rew_index_eq.
Tactic Notation "rew_index_eq" "in" hyp(H) :=
    autorewrite with rew_index_eq in H.
Tactic Notation "rew_index_eq" "in" "*" :=
    autorewrite with rew_index_eq in *.

Tactic Notation "rew_index_eq" "~" :=
    rew_index_eq; auto_tilde.
Tactic Notation "rew_index_eq" "*" :=
    rew_index_eq; auto_star.
Tactic Notation "rew_index_eq" "~" "in" hyp(H) :=
    rew_index_eq in H; auto_tilde.
Tactic Notation "rew_index_eq" "*" "in" hyp(H) :=
    rew_index_eq in H; auto_star.

Hint Rewrite 
    @from_to_list_id
    @from_list_empty @from_list_update @from_list_single
    @union_inter_distrib_l @union_inter_distrib_r
    @inter_union_distrib_l @inter_union_distrib_r
    @remove_union_distrib_r
    @remove_inter_distrib_r
    @union_assoc @inter_assoc
    @union_empty_l @union_empty_r
    @inter_empty_l @inter_empty_r
    @remove_empty_l @remove_empty_r 
    @update_empty @update_union_assoc @single_bind_union
    @dom_empty @dom_single_bind @dom_union @dom_remove @dom_restrict @dom_update
    using (eauto with typeclass_instances) : rew_bag_simpl.

Tactic Notation "rew_bag_simpl" :=
    autorewrite with rew_bag_simpl.
Tactic Notation "rew_bag_simpl" "in" hyp(H) :=
    autorewrite with rew_bag_simpl in H.
Tactic Notation "rew_bag_simpl" "in" "*" :=
    autorewrite with rew_bag_simpl in *.

Tactic Notation "rew_bag_simpl" "~" :=
    rew_bag_simpl; auto_tilde.
Tactic Notation "rew_bag_simpl" "*" :=
    rew_bag_simpl; auto_star.
Tactic Notation "rew_bag_simpl" "~" "in" hyp(H) :=
    rew_bag_simpl in H; auto_tilde.
Tactic Notation "rew_bag_simpl" "*" "in" hyp(H) :=
    rew_bag_simpl in H; auto_star.

Global Instance from_list_empty_from_from_list_in_eq :
    forall `{BagFromList A T} `{BagEmpty T} `{BagIn A T},
    In_double -> From_list_in_eq -> In_empty_eq -> From_list_empty.
Proof.
    constructor. apply in_double. intros. rew_in_eq. 
    split; introv Hx; inverts Hx.
Qed.

Global Instance from_list_single_from_from_list_in_eq :
    forall `{BagFromList A T} `{BagSingle A T} `{BagUnion T} `{BagIn A T},
    In_double -> From_list_in_eq -> In_single_eq -> In_union_eq -> From_list_single.
Proof.
    constructor. intros. apply in_double. intros. rew_in_eq. 
    split; introv Hx.
    inverts Hx; iauto.
    inverts Hx.
    apply Mem_here.
    apply Mem_next; assumption.
Qed.

Global Instance from_list_in_from_from_list_in_eq :
    forall `{BagFromList A U} `{BagIn A U},
    From_list_in_eq -> From_list_in.
Proof. constructor. introv. rewrite from_list_in_eq. auto. Qed.

Global Instance from_list_inv_in_from_from_list_in_eq :
    forall `{BagFromList A U} `{BagIn A U},
    From_list_in_eq -> From_list_in_inv.
Proof. constructor. introv. rewrite <- from_list_in_eq. auto. Qed.

Global Instance to_list_in_from_to_list_in_eq :
    forall `{BagToList A U} `{BagIn A U},
    To_list_in_eq -> To_list_in.
Proof. constructor. introv. rewrite to_list_in_eq. auto. Qed.

Global Instance to_list_inv_in_from_to_list_in_eq :
    forall `{BagToList A U} `{BagIn A U},
    To_list_in_eq -> To_list_in_inv.
Proof. constructor. introv. rewrite <- to_list_in_eq. auto. Qed.

Global Instance From_to_list_id_from_from_to_list_in :
    forall `{BagFromList A U} `{BagToList A U} `{BagIn A U},
    In_double -> From_list_in_eq -> To_list_in_eq -> From_to_list_id.
Proof. 
    constructor. intros_all. apply in_double. intros.
    rewrite from_list_in_eq. rewrite to_list_in_eq.
    iauto.
Qed.

Section InclDouble.
Context `{BagIn A U} `{BagIncl U}.

Global Instance incl_order_from_incl_in :
    In_double -> Incl_in_eq -> Incl_order.
Proof.
    constructor. constructor; repeat unfolds.
    introv. rewrite incl_in_eq. auto.
    introv Hi1 Hi2. rewrites incl_in_eq in *. auto.
    introv Hi1 Hi2. rewrites incl_in_eq in *.
    apply in_double. iauto.
Qed.

Global Instance incl_in_from_incl_in_eq :
    Incl_in_eq -> Incl_in.
Proof. constructor. introv. rewrite incl_in_eq. auto. Qed.

Global Instance incl_in_inv_from_incl_in_eq :
    Incl_in_eq -> Incl_in_inv.
Proof. constructor. introv. rewrite incl_in_eq. auto. Qed.

Global Instance empty_incl_from_incl_in :
    forall `{BagEmpty U},
    In_empty_eq -> Incl_in_eq -> Empty_incl.
Proof. constructor. intro. rewrite incl_in_eq. intro. rewrite in_empty_eq. iauto. Qed.

Global Instance incl_empty_from_incl_in :
    forall `{BagEmpty U},
    In_double -> In_empty_eq -> Incl_in_eq -> Incl_empty.
Proof. 
    constructor. intro. rewrite incl_in_eq. 
    rew_logic. apply iff_intro.
    introv He. apply in_double. intro. apply iff_intro. auto. rewrite in_empty_eq. iauto.
    intros. substs. auto.
Qed.

End InclDouble.

Section DisjointDouble.
Context `{BagIn A U} `{BagDisjoint U}.

Global Instance disjoint_in_from_disjoint_in_eq :
    Disjoint_in_eq -> Disjoint_in.
Proof. constructor. introv. rewrite disjoint_in_eq. auto. Qed.

Global Instance disjoint_in_inv_from_disjoint_in_eq :
    Disjoint_in_eq -> Disjoint_in_inv.
Proof. constructor. introv. rewrite disjoint_in_eq. auto. Qed.

Global Instance disjoint_inter_eq_from_disjoint_in_eq :
    forall `{BagInter U} `{BagEmpty U},
    In_double -> In_inter_eq -> In_empty_eq -> Disjoint_in_eq -> Disjoint_inter_eq.
Proof.
    constructor. introv. 
    rewrite disjoint_in_eq. rew_logic. split; introv Hs.
    apply in_double. intro. rew_in_eq. split; introv Hr. 
    applys Hs; jauto.
    iauto.
    introv He Hf.
    erewrite <- in_empty_eq.
    rewrite <- Hs.
    rew_in_eq.
    iauto.
Qed.

Global Instance disjoint_inter_from_disjoint_inter_eq :
    forall `{BagInter U} `{BagEmpty U},
    Disjoint_inter_eq -> Disjoint_inter.
Proof. constructor. introv. rewrite disjoint_inter_eq. auto. Qed.    

Global Instance disjoint_inter_inv_from_disjoint_inter_eq :
    forall `{BagInter U} `{BagEmpty U},
    Disjoint_inter_eq -> Disjoint_inter_inv.
Proof. constructor. introv. rewrite disjoint_inter_eq. auto. Qed.    

Global Instance Disjoint_sym_from_disjoint_in_eq :
    Disjoint_in_eq -> Disjoint_sym. 
Proof. constructor. unfolds. introv. rewrite_all disjoint_in_eq. unfold notin. iauto. Qed.

End DisjointDouble.

Section UnionDouble.
Context `{BagIn A U} `{BagUnion U}.

Global Instance union_empty_l_from_in_union :
    forall `{BagEmpty U},
    In_double -> In_empty_eq -> In_union_eq -> Union_empty_l.
Proof. constructor. contain_by_in_double. Qed.

End UnionDouble.

Section InterDouble.
Context `{BagIn A U} `{BagInter U}.

Global Instance inter_empty_l_from_in_union :
    forall `{BagEmpty U},
    In_double -> In_empty_eq -> In_inter_eq -> Inter_empty_l.
Proof. constructor. contain_by_in_double. Qed.

End InterDouble.

Section RemoveDouble.
Context `{BagIn A U} `{BagRemove U U}.

Global Instance remove_empty_l_from_in_remove :
    forall `{BagEmpty U},
    In_double -> In_empty_eq -> In_remove_eq -> Remove_empty_l.
Proof. constructor. contain_by_in_double. Qed.

Global Instance remove_empty_r_from_in_remove :
    forall `{BagEmpty U},
    In_double -> In_empty_eq -> In_remove_eq -> Remove_empty_r.
Proof. constructor. contain_by_in_double. unfold notin. autorewrite with rew_in_eq; auto.  Qed. 
(* TODO fix contain_by_in_double *)

End RemoveDouble.

Section UnionInterDouble.
Context `{BagIn A U} `{BagUnion U} `{BagInter U}.

Global Instance union_inter_distrib_l_from_in_union_inter :
    In_double -> In_union_eq -> In_inter_eq -> Union_inter_distrib_l.
Proof. constructor. contain_by_in_double. Qed.

Global Instance union_inter_distrib_r_from_in_union_inter :
    In_double -> In_union_eq -> In_inter_eq -> Union_inter_distrib_r.
Proof. constructor. contain_by_in_double. Qed.

Global Instance inter_union_distrib_l_from_in_union_inter :
    In_double -> In_union_eq -> In_inter_eq -> Inter_union_distrib_l.
Proof. constructor. contain_by_in_double. Qed.

Global Instance inter_union_distrib_r_from_in_union_inter :
    In_double -> In_union_eq -> In_inter_eq -> Inter_union_distrib_r.
Proof. constructor. contain_by_in_double. Qed.

End UnionInterDouble.

Section RemoveUnionDouble.
Context `{BagIn A U} `{BagUnion U} `{BagRemove U U}.

Global Instance remove_union_distrib_r_from_in_union_remove :
    In_double -> In_union_eq -> In_remove_eq -> Remove_union_distrib_r.
Proof. constructor. contain_by_in_double. Qed.

End RemoveUnionDouble.

Section RemoveInterDouble.
Context `{BagIn A U} `{BagInter U} `{BagRemove U U}.

Global Instance remove_inter_distrib_r_from_in_union_remove :
    In_double -> In_inter_eq -> In_remove_eq -> Remove_inter_distrib_r.
Proof. constructor. contain_by_in_double. Qed.

End RemoveInterDouble.

Global Instance Binds_double_eq_from_binds_double :
    forall `{BagBinds A B T},
    Binds_double -> Binds_double_eq.
Proof. constructor. introv I. apply binds_double. intros. rewrite I. iauto. Qed.

Global Instance Binds_deterministic_from_read_option_binds :
    forall `{BagBinds A B T} `{BagReadOption A B T},
    Read_option_binds_eq -> Binds_deterministic.
Proof. 
    constructor. introv. rewrite_all <- read_option_binds_eq.
    introv Hx Hy.
    rewrite Hx in Hy.
    injects Hy.
    reflexivity.
Qed.

Global Instance From_list_binds_from_from_list_binds_eq :
    forall `{BagFromList (A * B) T} `{BagBinds A B T},
    From_list_binds_eq -> From_list_binds.
Proof. constructor. introv. rewrite from_list_binds_eq. auto. Qed.

Global Instance From_list_binds_inv_from_from_list_binds_eq :
    forall `{BagFromList (A * B) T} `{BagBinds A B T},
    From_list_binds_eq -> From_list_binds_inv.
Proof. constructor. introv. rewrite from_list_binds_eq. auto. Qed.

Global Instance To_list_binds_from_to_list_binds_eq :
    forall `{BagToList (A * B) T} `{BagBinds A B T},
    To_list_binds_eq -> To_list_binds.
Proof. constructor. introv. rewrite to_list_binds_eq. auto. Qed.

Global Instance To_list_binds_inv_from_to_list_binds_eq :
    forall `{BagToList (A * B) T} `{BagBinds A B T},
    To_list_binds_eq -> To_list_binds_inv.
Proof. constructor. introv. rewrite to_list_binds_eq. auto. Qed.

Global Instance From_to_list_id_from_from_to_list_binds :
    forall `{BagFromList (A * B) T} `{BagToList (A * B) T} `{BagBinds A B T},
    Binds_double -> From_list_binds_eq -> To_list_binds_eq -> From_to_list_id.
Proof.
    constructor. intros. apply binds_double. intros.
    rewrite from_list_binds_eq. rewrite to_list_binds_eq.
    iauto.
Qed.

Global Instance read_option_binds_from_read_option_binds_eq : 
    forall `{BagReadOption A B T} `{BagBinds A B T},
    Read_option_binds_eq -> Read_option_binds.
Proof. constructor. introv I. rewrite <- read_option_binds_eq. assumption. Qed.

Global Instance read_option_binds_inv_from_read_option_binds_eq : 
    forall `{BagReadOption A B T} `{BagBinds A B T},
    Read_option_binds_eq -> Read_option_binds_inv.
Proof. constructor. introv I. rewrite read_option_binds_eq. assumption. Qed.

Global Instance read_option_not_index_eq_from_read_option_binds_eq : 
    forall `{BagReadOption A B T} `{BagBinds A B T} `{BagIndex T A},
    Read_option_binds_eq -> Index_binds_eq -> Read_option_not_index_eq.
Proof. 
    constructor. introv.
    rewrite index_binds_eq.
    rew_logic.
    split; introv I.
    intros. rewrite <- read_option_binds_eq. intro Heq. rewrite Heq in I. tryfalse.
    apply not_not_elim.
    intro.
    sets_eq o : (M\(k?)).
    destruct o; tryfalse.
    applys I b.
    rewrite <- read_option_binds_eq.
    auto.
Qed.

Global Instance read_option_not_index_from_read_option_not_index_eq :
    forall `{BagReadOption A B T} `{BagIndex T A},
    Read_option_not_index_eq -> Read_option_not_index.
Proof. constructor. introv I. rewrite <- read_option_not_index_eq. assumption. Qed.

Global Instance read_option_not_index_inv_from_read_option_not_index_eq :
    forall `{BagReadOption A B T} `{BagIndex T A},
    Read_option_not_index_eq -> Read_option_not_index_inv.
Proof. constructor. introv I. rewrite read_option_not_index_eq. assumption. Qed.

(* empty *)
Section BindsEmpty.
Context `{BagBinds A B T} `{BagEmpty T}.

Global Instance binds_empty_from_binds_empty_eq :
    Binds_empty_eq -> Binds_empty.
Proof. constructor. introv. rewrite binds_empty_eq. auto. Qed.

End BindsEmpty.

(* single_bind *)
Section BindsSingleBind.
Context `{BagBinds A B T} `{BagSingleBind A B T}.

Global Instance binds_single_bind_same_eq_from_binds_single_bind_eq :
    Binds_single_bind_eq -> Binds_single_bind_same_eq. 
Proof. 
    constructor. intros. rewrite binds_single_bind_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Global Instance binds_single_bind_same_from_binds_single_bind_same_eq :
    Binds_single_bind_same_eq -> Binds_single_bind_same. 
Proof. constructor. intros. rewrite binds_single_bind_same_eq. reflexivity. Qed.

Global Instance binds_single_bind_same_inv_from_binds_single_bind_same_eq :
    Binds_single_bind_same_eq -> Binds_single_bind_same_inv. 
Proof. constructor. introv I. rewrite binds_single_bind_same_eq in I. assumption. Qed.

Global Instance binds_single_bind_diff_eq_from_binds_single_bind_eq :
    Binds_single_bind_eq -> Binds_single_bind_diff_eq. 
Proof. 
    constructor. intros. rewrite binds_single_bind_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Global Instance binds_single_bind_diff_from_binds_single_bind_diff_eq :
    Binds_single_bind_diff_eq -> Binds_single_bind_diff. 
Proof. constructor. introv Hd. rewrite binds_single_bind_diff_eq; auto. Qed.

End BindsSingleBind.

(* union *)
Section BindsUnion.
Context `{BagBinds A B T} `{BagIndex T A} `{BagUnion T}.

Global Instance binds_union_l_from_binds_union_eq :
    Binds_union_eq -> Binds_union_l.
Proof. constructor. introv. rewrite binds_union_eq. auto. Qed.

Global Instance binds_union_r_from_binds_union_eq :
    Binds_union_eq -> Binds_union_r.
Proof. constructor. introv. rewrite binds_union_eq. auto. Qed.

Global Instance binds_union_inv_from_binds_union_eq :
    Binds_union_eq -> Binds_union_inv.
Proof. constructor. introv. rewrite binds_union_eq. auto. Qed.

End BindsUnion.

(* remove *)
Section BindsRemove.
Context `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1}.

Global Instance binds_remove_notin_eq_from_binds_remove_eq :
    Binds_remove_eq -> Binds_remove_notin_eq.
Proof. constructor. introv Hin. rewrite binds_remove_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Global Instance binds_remove_notin_from_binds_remove_notin_eq :
    Binds_remove_notin_eq -> Binds_remove_notin.
Proof. constructor. introv Hin I. rewrite binds_remove_notin_eq; auto. Qed.

Global Instance binds_remove_notin_inv_from_binds_remove_notin_eq :
    Binds_remove_notin_eq -> Binds_remove_notin_inv.
Proof. constructor. introv Hin I. rewrite binds_remove_notin_eq in I; auto. Qed.

Global Instance binds_remove_in_eq_from_binds_remove_eq :
    Binds_remove_eq -> Binds_remove_in_eq.
Proof. constructor. introv Hin. rewrite binds_remove_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Global Instance binds_remove_in_from_binds_remove_in_eq :
    Binds_remove_in_eq -> Binds_remove_in.
Proof. constructor. introv Hin.  rewrite binds_remove_in_eq; auto. Qed.

Global Instance binds_remove_inv_from_binds_remove_eq :
    Binds_remove_eq -> Binds_remove_inv.
Proof. constructor. introv Hb. rewrite binds_remove_eq in Hb. auto. Qed.

End BindsRemove.

(* restrict *)
Section BindsRestrict.
Context `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1}.

Global Instance binds_restrict_in_eq_from_binds_restrict_eq :
    Binds_restrict_eq -> Binds_restrict_in_eq.
Proof. constructor. introv Hin. rewrite binds_restrict_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Global Instance binds_restrict_in_from_binds_restrict_in_eq :
    Binds_restrict_in_eq -> Binds_restrict_in.
Proof. constructor. introv Hin I. rewrite binds_restrict_in_eq; auto. Qed.

Global Instance binds_restrict_in_inv_from_binds_restrict_in_eq :
    Binds_restrict_in_eq -> Binds_restrict_in_inv.
Proof. constructor. introv Hin I. rewrite binds_restrict_in_eq in I; auto. Qed.

Global Instance binds_restrict_notin_eq_from_binds_restrict_eq :
    Binds_restrict_eq -> Binds_restrict_notin_eq.
Proof. constructor. introv Hin. rewrite binds_restrict_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Global Instance binds_restrict_notin_from_binds_restrict_notin_eq :
    Binds_restrict_notin_eq -> Binds_restrict_notin.
Proof. constructor. introv Hin.  rewrite binds_restrict_notin_eq; auto. Qed.

Global Instance binds_restrict_inv_from_binds_restrict_eq :
    Binds_restrict_eq -> Binds_restrict_inv.
Proof. constructor. introv Hb. rewrite binds_restrict_eq in Hb. auto. Qed.

End BindsRestrict.

(* update *)
Section BindsUpdate.
Context `{BagBinds A B T} `{BagUpdate A B T}.

Global Instance binds_update_same_eq_from_binds_update_eq :
    Binds_update_eq -> Binds_update_same_eq.
Proof. 
    constructor. intros. rewrite binds_update_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Global Instance binds_update_same_from_binds_update_same_eq :
    Binds_update_same_eq -> Binds_update_same.
Proof. constructor. intros. rewrite binds_update_same_eq. reflexivity. Qed.

Global Instance binds_update_same_inv_from_binds_update_same_eq :
    Binds_update_same_eq -> Binds_update_same_inv.
Proof. constructor. introv I. rewrite binds_update_same_eq in I. assumption. Qed.

Global Instance binds_update_diff_eq_from_binds_update_eq :
    Binds_update_eq -> Binds_update_diff_eq.
Proof. 
    constructor. intros. rewrite binds_update_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Global Instance binds_update_diff_from_binds_update_diff_eq :
    Binds_update_diff_eq -> Binds_update_diff.
Proof. constructor. intros. rewrite binds_update_diff_eq; assumption. Qed.

Global Instance binds_update_diff_inv_from_binds_update_diff_eq :
    Binds_update_diff_eq -> Binds_update_diff_inv.
Proof. constructor. introv Hd I. rewrite binds_update_diff_eq in I; assumption. Qed.

End BindsUpdate.

(* index binds *)
Section IndexBinds.
Context `{BagIndex T A} `{BagBinds A B T}.

Global Instance index_binds_from_index_binds_eq :
    Index_binds_eq -> Index_binds.
Proof. constructor. introv I. rewrite index_binds_eq in I. assumption. Qed.

Global Instance index_binds_inv_from_index_binds_eq :
    Index_binds_eq -> Index_binds_inv.
Proof. constructor. introv I. rewrite index_binds_eq. eauto. Qed.

End IndexBinds.

(* empty *)
Section IndexEmpty.
Context `{BagIndex T A} `{BagEmpty T}.

Global Instance index_empty_from_index_empty_eq :
    Index_empty_eq -> Index_empty.
Proof. constructor. introv. rewrite index_empty_eq. auto. Qed. 

End IndexEmpty.

(* single_bind *)
Section IndexSingleBind.
Context `{BagIndex T A} `{BagSingleBind A B T}.

Global Instance index_single_bind_same_eq_from_index_single_bind_eq :
    Index_single_bind_eq -> Index_single_bind_same_eq.
Proof. constructor. introv. rewrite index_single_bind_eq. auto. Qed.

Global Instance index_single_bind_same_from_index_single_bind_same_eq :
    Index_single_bind_same_eq -> Index_single_bind_same.
Proof. constructor. introv. rewrite index_single_bind_same_eq. auto. Qed.

Global Instance index_single_bind_diff_eq_from_index_single_bind_eq :
    Index_single_bind_eq -> Index_single_bind_diff_eq.
Proof. constructor. introv. rewrite index_single_bind_eq. auto. Qed.

Global Instance index_single_bind_diff_from_index_single_bind_diff_eq :
    Index_single_bind_diff_eq -> Index_single_bind_diff.
Proof. constructor. introv Hd. rewrite index_single_bind_diff_eq; auto. Qed.

End IndexSingleBind.

(* union *)
Section IndexUnion.
Context `{BagIndex T A} `{BagUnion T}.

Global Instance index_union_l_from_index_union_eq :
    Index_union_eq -> Index_union_l.
Proof. constructor. introv. rewrite index_union_eq. auto. Qed.

Global Instance index_union_r_from_index_union_eq :
    Index_union_eq -> Index_union_inv.
Proof. constructor. introv. rewrite index_union_eq. auto. Qed.

Global Instance index_union_inv_from_index_union_eq :
    Index_union_eq -> Index_union_inv.
Proof. constructor. introv. rewrite index_union_eq. auto. Qed.

End IndexUnion.

(* remove *)
Section IndexRemove.
Context `{BagIndex T A} `{BagIn A T1} `{BagRemove T T1}.

Global Instance index_remove_in_eq_from_index_remove_eq :
    Index_remove_eq -> Index_remove_in_eq.
Proof. 
    constructor. introv I. rewrite index_remove_eq. rew_logic. 
    apply iff_intro; intro; jauto; tryfalse.
Qed.

Global Instance index_remove_in_from_index_remove_in_eq :
    Index_remove_in_eq -> Index_remove_in.
Proof. constructor. introv Hi. rewrite index_remove_in_eq; auto. Qed.

Global Instance index_remove_notin_eq_from_index_remove_eq :
    Index_remove_eq -> Index_remove_notin_eq.
Proof. 
    constructor. introv I. rewrite index_remove_eq. rew_logic. 
    apply iff_intro; intro; jauto; tryfalse.
Qed.

Global Instance index_remove_notin_from_index_remove_notin_eq :
    Index_remove_notin_eq -> Index_remove_notin.
Proof. constructor. introv Hi. rewrite index_remove_notin_eq; auto. Qed.

Global Instance index_remove_notin_inv_from_index_remove_notin_eq :
    Index_remove_notin_eq -> Index_remove_notin_inv.
Proof. constructor. introv Hi. rewrite index_remove_notin_eq; auto. Qed.

End IndexRemove.

(* restrict *)
Section IndexRestrict.
Context `{BagIndex T A} `{BagIn A T1} `{BagRestrict T T1}.

Global Instance index_restrict_notin_eq_from_index_restrict_eq :
    Index_restrict_eq -> Index_restrict_notin_eq.
Proof. 
    constructor. introv I. rewrite index_restrict_eq. rew_logic. 
    apply iff_intro; intro; jauto; tryfalse.
Qed.

Global Instance index_restrict_notin_from_index_restrict_notin_eq :
    Index_restrict_notin_eq -> Index_restrict_notin.
Proof. constructor. introv Hi. rewrite index_restrict_notin_eq; auto. Qed.

Global Instance index_restrict_in_eq_from_index_restrict_eq :
    Index_restrict_eq -> Index_restrict_in_eq.
Proof. 
    constructor. introv I. rewrite index_restrict_eq. rew_logic. 
    apply iff_intro; intro; jauto; tryfalse.
Qed.

Global Instance index_restrict_in_from_index_restrict_in_eq :
    Index_restrict_in_eq -> Index_restrict_in.
Proof. constructor. introv Hi. rewrite index_restrict_in_eq; auto. Qed.

Global Instance index_restrict_in_inv_from_index_restrict_in_eq :
    Index_restrict_in_eq -> Index_restrict_in_inv.
Proof. constructor. introv Hi. rewrite index_restrict_in_eq; auto. Qed.

End IndexRestrict.

(* update *)
Section IndexUpdate.
Context `{BagIndex T A} `{BagUpdate A B T}.

Global Instance index_update_same_eq_from_index_update_eq : 
    Index_update_eq -> Index_update_same_eq.
Proof. constructor. introv. rewrite index_update_eq. auto. Qed.

Global Instance index_update_same_from_index_update_same_eq :
    Index_update_same_eq -> Index_update_same.
Proof. constructor. introv. rewrite index_update_same_eq. auto. Qed.

Global Instance index_update_index_from_index_update_eq : 
    Index_update_eq -> Index_update_index.
Proof. constructor. introv. rewrite index_update_eq. auto. Qed.

Global Instance index_update_diff_eq_from_index_update_eq : 
    Index_update_eq -> Index_update_diff_eq.
Proof. 
    constructor. introv Hd. rewrite index_update_eq. rew_logic.
    apply iff_intro; intro; intuition jauto.
Qed.

Global Instance index_update_diff_from_index_update_diff_eq :
    Index_update_diff_eq -> Index_update_diff.
Proof. constructor. introv Hd. rewrite index_update_diff_eq; eauto. Qed.

Global Instance index_update_diff_inv_from_index_update_diff_eq :
    Index_update_diff_eq -> Index_update_diff_inv.
Proof. constructor. introv Hd. rewrite index_update_diff_eq; auto. Qed.

End IndexUpdate.

Global Instance fresh_index_from_fresh_index_eq : 
    forall `{BagIndex T A} `{BagFresh A T}, 
    Fresh_index_eq -> Fresh_index.
Proof. constructor. introv. rewrite fresh_index_eq. auto. Qed.

Section InclBinds.
Context `{BagIncl T} `{BagBinds A B T}.

Global Instance incl_order_from_incl_binds :
    Binds_double -> Incl_binds_eq -> Incl_order.
Proof.
    constructor. constructor; repeat unfolds.
    introv. rewrite incl_binds_eq. auto.
    introv Hi1 Hi2. rewrites incl_binds_eq in *. auto.
    introv Hi1 Hi2. rewrites incl_binds_eq in *.
    apply binds_double. iauto.
Qed.

Global Instance incl_binds_from_incl_binds_eq :
    Incl_binds_eq -> Incl_binds.
Proof. constructor. introv. rewrite incl_binds_eq. auto. Qed.

Global Instance incl_binds_inv_from_incl_binds_eq : 
    Incl_binds_eq -> Incl_binds_inv.
Proof. constructor. introv. rewrite incl_binds_eq. auto. Qed.

Global Instance incl_index_from_incl_binds :
    forall `{BagIndex T A},
    Index_binds_eq -> Incl_binds -> Incl_index.
Proof. 
    constructor. introv. rewrite_all index_binds_eq.
    hint incl_binds. introv Hincl (x&Hbinds). iauto.
Qed.

Global Instance empty_incl_from_incl_binds :
    forall `{BagEmpty T},
    Binds_empty_eq -> Incl_binds_eq -> Empty_incl.
Proof. constructor. intro. rewrite incl_binds_eq. introv. rewrite binds_empty_eq. iauto. Qed.

Global Instance incl_empty_from_incl_binds :
    forall `{BagEmpty T},
    Binds_double -> Binds_empty_eq -> Incl_binds_eq -> Incl_empty.
Proof. 
    constructor. intro. rewrite incl_binds_eq.
    rew_logic. apply iff_intro.
    introv He. apply binds_double. introv. apply iff_intro. auto. rewrite binds_empty_eq. iauto.
    intros. substs. auto.
Qed.

End InclBinds.

Section DisjointBinds.
Context `{BagDisjoint T} `{BagBinds A B T}.

Global Instance disjoint_binds_from_disjoint_binds_eq :
    Disjoint_binds_eq -> Disjoint_binds.
Proof. constructor. introv. rewrite disjoint_binds_eq. eauto. Qed.

Global Instance disjoint_binds_inv_from_disjoint_binds_eq :
    Disjoint_binds_eq -> Disjoint_binds_inv.
Proof. constructor. introv. rewrite disjoint_binds_eq. eauto. Qed.

Global Instance disjoint_index_eq_from_disjoint_binds_eq :
    forall `{BagIndex T A},
    Disjoint_binds_eq -> Index_binds_eq -> Disjoint_index_eq.
Proof. 
    constructor. introv. rewrite disjoint_binds_eq. 
    rew_logic. split; introv Hb; introv.
    rewrite_all index_binds_eq. rew_logic. jauto.
    specializes Hb k.
    rewrite_all index_binds_eq in Hb.
    jauto.
Qed.

Global Instance Disjoint_sym_from_disjoint_binds_eq :
    Disjoint_binds_eq -> Disjoint_sym. 
Proof. constructor. unfolds. introv. rewrite_all disjoint_binds_eq. iauto. Qed.

End DisjointBinds.

Section DisjointIndex.
Context `{BagDisjoint T} `{BagIndex T A}.

Global Instance disjoint_index_from_disjoint_index_eq :
    Disjoint_index_eq -> Disjoint_index.
Proof. constructor. introv. rewrite disjoint_index_eq. eauto. Qed.

Global Instance disjoint_binds_inv_from_disjoint_index_eq :
    Disjoint_index_eq -> Disjoint_index_inv.
Proof. constructor. introv. rewrite disjoint_index_eq. eauto. Qed.

End DisjointIndex.

Section DomIndex.
Context `{BagDom T T1} `{BagIndex T A} `{BagIn A T1}.

Global Instance dom_index_from_dom_index_eq :
    Dom_index_eq -> Dom_index.
Proof. constructor. introv. rewrite dom_index_eq. auto. Qed.

Global Instance dom_index_inv_from_dom_index_eq :
    Dom_index_eq -> Dom_index_inv.
Proof. constructor. introv. rewrite dom_index_eq. auto. Qed.

Global Instance dom_empty_from_dom_index :
    forall `{BagEmpty T} `{BagEmpty T1},
    In_double -> Dom_index_eq -> In_empty_eq -> Index_empty_eq -> Dom_empty.
Proof. 
    constructor. apply in_double. intros. 
    rew_in_eq. rewrite_all dom_index_eq. rew_index_eq. iauto.
Qed.

Global Instance dom_union_from_dom_index :
    forall `{BagUnion T} `{BagUnion T1},
    In_double -> Dom_index_eq -> In_union_eq -> Index_union_eq -> Dom_union. 
Proof.
    constructor. intros. apply in_double. intros.
    rew_in_eq. rewrite_all dom_index_eq. rew_index_eq. iauto.
Qed.

Global Instance dom_remove_from_dom_index :
    forall `{BagRemove T T1} `{BagRemove T1 T1},
    In_double -> Dom_index_eq -> In_remove_eq -> Index_remove_eq -> Dom_remove. 
Proof.
    constructor. intros. apply in_double. intros.
    rew_in_eq. unfolds notin. rewrite_all dom_index_eq. rewrite index_remove_eq. iauto.
Qed.

Global Instance dom_restrict_from_dom_index :
    forall `{BagRestrict T T1} `{BagInter T1},
    In_double -> Dom_index_eq -> In_inter_eq -> Index_restrict_eq -> Dom_restrict. 
Proof.
    constructor. intros. apply in_double. intros.
    rew_in_eq. rewrite_all dom_index_eq. rewrite index_restrict_eq. iauto.
Qed.

Global Instance dom_single_bind_from_dom_index :
    forall `{BagSingleBind A B T} `{BagSingle A T1},
    In_double -> Dom_index_eq -> In_single_eq -> Index_single_bind_eq -> Dom_single_bind. 
Proof.
    constructor. intros. apply in_double. intros.
    rew_in_eq. rewrite_all dom_index_eq. rew_index_eq. iauto.
Qed.

Global Instance dom_update_from_dom_index :
    forall `{BagUpdate A B T} `{BagUnion T1} `{BagSingle A T1},
    In_double -> Dom_index_eq -> In_union_eq -> In_single_eq -> Index_update_eq -> Dom_update. 
Proof.
    constructor. intros. apply in_double. intros.
    rew_in_eq. rewrite_all dom_index_eq. rew_index_eq. iauto.
Qed.

End DomIndex.

Create HintDb bag discriminated.

Hint Resolve 
    @in_empty @in_single_self
    @in_union_l @in_union_r
    @in_inter
    @binds_empty @binds_single_bind_same @binds_single_bind_diff
    @binds_union_l @binds_union_r
    @binds_remove_in @binds_remove_notin
    @binds_restrict_in @binds_restrict_notin
    @binds_update_same @binds_update_diff 
    @index_empty @index_single_bind_same @index_single_bind_diff
    @index_union_l @index_union_r
    @index_remove_in @index_remove_notin
    @index_restrict_in @index_restrict_notin
    @index_update_same @index_update_index @index_update_diff
    @index_binds_inv @fresh_index 
    @incl_in @incl_index @incl_binds 
    @update_nindex_incl @remove_incl @restrict_incl
    @disjoint_in @disjoint_index @disjoint_binds
: bag.

Hint Extern 0 (?x \c ?x) => solve [apply incl_refl] : bag.
Hint Extern 0 (?A \c ?C) => 
    match goal with
    | H : A \c ?B |- _ => apply (@incl_trans _ _ _ B A C H) 
    | H : ?B \c C |- _ => apply ((fun bs1 bs2 => @incl_trans _ _ _ B A C bs2 bs1) H) 
    end : bag. 

Tactic Notation "prove_bag" :=
    solve [ eauto with bag typeclass_instances ].

Hint Rewrite 
    @binds_empty_eq @binds_single_bind_eq @binds_union_eq
    @binds_remove_eq @binds_restrict_eq
    @binds_update_eq @incl_binds_eq @index_binds_eq  
    @from_list_binds_eq @to_list_binds_eq
    using (eauto 10 with typeclass_instances) : rew_binds_eq.

Tactic Notation "rew_binds_eq" :=
    autorewrite with rew_binds_eq.
Tactic Notation "rew_binds_eq" "in" hyp(H) :=
    autorewrite with rew_binds_eq in H.
Tactic Notation "rew_binds_eq" "in" "*" :=
    autorewrite with rew_binds_eq in *.

Tactic Notation "rew_binds_eq" "~" :=
    rew_binds_eq; auto_tilde.
Tactic Notation "rew_binds_eq" "*" :=
    rew_binds_eq; auto_star.
Tactic Notation "rew_binds_eq" "~" "in" hyp(H) :=
    rew_binds_eq in H; auto_tilde.
Tactic Notation "rew_binds_eq" "*" "in" hyp(H) :=
    rew_binds_eq in H; auto_star.

Ltac binds_determine_then :=
    match goal with
    | H1 : binds ?m ?k ?v1, H2 : binds ?m ?k ?v2 |- _ =>
        not constr_eq v1 v2; 
        not is_hyp (v1 = v2);
        let H := fresh "H" in asserts H : (v1 = v2); [eauto using binds_deterministic | idtac]; 
        revert H2; revert H
    end.

Ltac binds_determine_eq := binds_determine_then; intro; intro.
Ltac binds_determine := binds_determine_then; 
    let H := fresh "H" in let H1 := fresh "H" in intro H; intro H1; try (subst_hyp H; clear H1).

Global Instance from_list_empty_from_from_list_binds_eq :
    forall `{BagFromList (A * B) T} `{BagEmpty T} `{BagBinds A B T},
    Binds_double -> From_list_binds_eq -> Binds_empty_eq -> From_list_empty.
Proof.
    constructor. apply binds_double. intros. rew_binds_eq. 
    split; introv Hx; inverts Hx.
Qed.

Global Instance from_list_update_from_from_list_binds_eq :
    forall `{BagFromList (A * B) T} `{BagUpdate A B T} `{BagBinds A B T},
    Binds_double -> From_list_binds_eq -> Binds_update_eq -> From_list_update.
Proof.
    constructor. intros. apply binds_double. intros. rew_binds_eq. 
    split; introv Hx.
    inverts Hx; iauto.
    destruct Hx as [(Hx1&Hx2)|(Hx1&Hx2)].
    substs.
    apply Assoc_here.
    apply Assoc_next; assumption.
Qed.

Global Instance update_empty_from_binds_update :
    forall `{BagBinds A B T} `{BagUpdate A B T} `{BagSingleBind A B T} `{BagEmpty T},
    Binds_double -> Binds_update_eq -> Binds_empty_eq -> Binds_single_bind_eq -> Update_empty.
Proof.
    constructor. intros. apply binds_double. intros.
    rew_binds_eq. rew_logic. iauto.
Qed.

Global Instance update_union_assoc_from_binds_union :
    forall `{BagBinds A B T} `{BagIndex T A} `{BagUpdate A B T} `{BagUnion T},
    Binds_double -> Binds_update_eq -> Index_update_eq -> Binds_union_eq -> Update_union_assoc.
Proof.
    constructor. intros. apply binds_double. intros.
    rew_binds_eq. rewrite_all binds_union_eq. rew_binds_eq. rew_index_eq.
    rew_logic. iauto.
Qed.

Global Instance single_bind_union_from_binds_union :
    forall `{BagUpdate A B T} `{BagBinds A B T} `{BagIndex T A} `{BagSingleBind A B T} `{BagUnion T},
    Binds_double -> Binds_update_eq -> Binds_union_eq -> Index_single_bind_eq -> Binds_single_bind_eq -> 
    Single_bind_union.
Proof.
    constructor. intros. apply binds_double. intros.
    rewrite binds_update_eq.
    rew_binds_eq. rewrite_all binds_union_eq. rew_binds_eq. rew_index_eq. iauto. 
Qed.

Global Instance union_empty_l_from_binds_union :
    forall `{BagBinds A B T} `{BagIndex T A} `{BagUnion T} `{BagEmpty T},
    Binds_double -> Index_empty_eq -> Binds_empty_eq -> Binds_union_eq -> Union_empty_l.
Proof.
    constructor. unfolds. intros. eapply binds_double. intros. 
    rewrite binds_union_eq, index_empty_eq. rew_binds_eq. rew_logic. iauto.
Qed. 

Global Instance union_empty_r_from_binds_union :
    forall `{BagBinds A B T} `{BagIndex T A} `{BagUnion T} `{BagEmpty T},
    Binds_double -> Index_empty_eq -> Binds_empty_eq -> Binds_union_eq -> Union_empty_r.
Proof.
    constructor. unfolds. intros. eapply binds_double. intros. 
    rewrite binds_union_eq. rew_binds_eq. rew_logic. iauto.
Qed. 

Global Instance update_nindex_incl_inst :
    forall `{BagIncl T} `{BagUpdate A B T} `{BagIndex T A} `{BagBinds A B T},
    Index_binds_eq -> Incl_binds_eq -> Binds_update_eq -> Update_nindex_incl.
Proof.
    constructor. introv.
    rewrite incl_binds_eq, index_binds_eq. 
    rew_logic. intros. 
    rew_binds_eq.
    right. split.
    intro. substs. jauto.
    auto. 
Qed.

Global Instance remove_incl_inst :
    forall `{BagIncl T} `{BagRemove T T1} `{BagIn A T1} `{BagBinds A B T},
    Binds_remove_eq -> Incl_binds_eq -> Remove_incl.
Proof.
    constructor. introv.
    rewrite incl_binds_eq. introv. 
    rewrite binds_remove_eq.
    iauto.
Qed.

Global Instance restrict_incl_inst :
    forall `{BagIncl T} `{BagRestrict T T1} `{BagIn A T1} `{BagBinds A B T},
    Binds_restrict_eq -> Incl_binds_eq -> Restrict_incl.
Proof.
    constructor. introv.
    rewrite incl_binds_eq. introv.
    rewrite binds_restrict_eq.
    iauto.
Qed.

Global Instance index_empty_eq_inst : 
    forall `{BagIndex T A} `{BagBinds A B T} `{BagEmpty T},
    Index_binds_eq -> Binds_empty_eq -> Index_empty_eq.
Proof.
    constructor. introv. rewrite index_binds_eq. 
    rew_logic; apply iff_intro; intro. 
    jauto_set. rewrites binds_empty_eq in *. trivial.
    tryfalse.
Qed.

Global Instance index_single_bind_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagSingleBind A B T},
    Index_binds_eq -> Binds_single_bind_eq -> Index_single_bind_eq. 
Proof.
    constructor. introv. rewrite index_binds_eq. 
    rew_logic; apply iff_intro; 
    jauto_set; rew_binds_eq in *; jauto.
Qed.

Global Instance index_union_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagUnion T},
    Index_binds_eq -> Binds_union_eq -> Index_union_eq.
Proof.
    constructor. introv. rewrite_all index_binds_eq.
    rew_logic; apply iff_intro; introv Hi.
    jauto_set; rewrites binds_union_eq in *; iauto.
    apply case_classic_l in Hi.
    destruct Hi; jauto_set; rewrites binds_union_eq; rewrites index_binds_eq; iauto.
Qed.

Global Instance index_remove_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1},
    Index_binds_eq -> Binds_remove_eq -> Index_remove_eq.
Proof.
    constructor. introv. rewrite_all index_binds_eq.
    rew_logic; apply iff_intro; 
    jauto_set; rewrites binds_remove_eq in *; jauto.
Qed.

Global Instance index_restrict_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1},
    Index_binds_eq -> Binds_restrict_eq -> Index_restrict_eq.
Proof.
    constructor. introv. rewrite_all index_binds_eq.
    rew_logic; apply iff_intro; 
    jauto_set; rewrites binds_restrict_eq in *; jauto.
Qed.

Global Instance index_update_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagUpdate A B T},
    Index_binds_eq -> Binds_update_eq -> Index_update_eq.
Proof.
    constructor. introv. rewrite_all index_binds_eq.
        rew_logic; apply iff_intro.
    jauto_set; rewrites binds_update_eq in *; intuition jauto.
    introv Hyp.
    apply case_classic_r in Hyp.
    destruct Hyp; jauto_set; rewrites binds_update_eq in *; intuition jauto.
Qed.
