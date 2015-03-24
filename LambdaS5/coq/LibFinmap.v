Require Import LibTactics LibList LibListSorted.
Require Import LibSet LibMap LibLogic LibEqual LibReflect LibOrder LibRelation.
Require Import LibFinset.
Generalizable Variable A R U B T.

Import ListNotations.
Open Scope list_scope.

(* TODO utitities *)
Definition rel_fst {A B} (R : binary A) : binary (A * B) := fun x y => R (fst x) (fst y).

(* TODO this should get to TLC LibBag later *)
Class BagReadOption A B T := { read_option : T -> A -> option B }. 
Class BagFresh A T := { fresh : T -> A }.

Notation "m \( x ?)" := (read_option m x)
  (at level 33, format "m \( x ?)") : container_scope.

(* Extensionality for maps *)
Class Binds_double_eq `{BagBinds A B T} :=
    { binds_double_eq : forall E F, (forall k x, binds E k x = binds F k x) -> E = F }.

Class Binds_double `{BagBinds A B T} :=
    { binds_double : forall E F, (forall k x, binds E k x <-> binds F k x) -> E = F }.

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

Instance Binds_double_eq_from_binds_double :
    forall `{BagBinds A B T},
    Binds_double -> Binds_double_eq.
Proof. constructor. introv I. apply binds_double. intros. rewrite I. iauto. Qed.

Instance From_list_binds_from_from_list_binds_eq :
    forall `{BagFromList (A * B) T} `{BagBinds A B T},
    From_list_binds_eq -> From_list_binds.
Proof. constructor. introv. rewrite from_list_binds_eq. auto. Qed.

Instance From_list_binds_inv_from_from_list_binds_eq :
    forall `{BagFromList (A * B) T} `{BagBinds A B T},
    From_list_binds_eq -> From_list_binds_inv.
Proof. constructor. introv. rewrite from_list_binds_eq. auto. Qed.

Instance To_list_binds_from_to_list_binds_eq :
    forall `{BagToList (A * B) T} `{BagBinds A B T},
    To_list_binds_eq -> To_list_binds.
Proof. constructor. introv. rewrite to_list_binds_eq. auto. Qed.

Instance To_list_binds_inv_from_to_list_binds_eq :
    forall `{BagToList (A * B) T} `{BagBinds A B T},
    To_list_binds_eq -> To_list_binds_inv.
Proof. constructor. introv. rewrite to_list_binds_eq. auto. Qed.

Instance From_to_list_id_from_from_to_list_binds :
    forall `{BagFromList (A * B) T} `{BagToList (A * B) T} `{BagBinds A B T},
    Binds_double -> From_list_binds_eq -> To_list_binds_eq -> From_to_list_id.
Proof.
    constructor. intros. apply binds_double. intros.
    rewrite from_list_binds_eq. rewrite to_list_binds_eq.
    iauto.
Qed.

Instance read_option_binds_from_read_option_binds_eq : 
    forall `{BagReadOption A B T} `{BagBinds A B T},
    Read_option_binds_eq -> Read_option_binds.
Proof. constructor. introv I. rewrite <- read_option_binds_eq. assumption. Qed.

Instance read_option_binds_inv_from_read_option_binds_eq : 
    forall `{BagReadOption A B T} `{BagBinds A B T},
    Read_option_binds_eq -> Read_option_binds_inv.
Proof. constructor. introv I. rewrite read_option_binds_eq. assumption. Qed.

(* empty *)
Section BindsEmpty.
Context `{BagBinds A B T} `{BagEmpty T}.

Instance binds_empty_from_binds_empty_eq :
    Binds_empty_eq -> Binds_empty.
Proof. constructor. introv. rewrite binds_empty_eq. auto. Qed.

End BindsEmpty.

(* single_bind *)
Section BindsSingleBind.
Context `{BagBinds A B T} `{BagSingleBind A B T}.

Instance binds_single_bind_same_eq_from_binds_single_bind_eq :
    Binds_single_bind_eq -> Binds_single_bind_same_eq. 
Proof. 
    constructor. intros. rewrite binds_single_bind_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_single_bind_same_from_binds_single_bind_same_eq :
    Binds_single_bind_same_eq -> Binds_single_bind_same. 
Proof. constructor. intros. rewrite binds_single_bind_same_eq. reflexivity. Qed.

Instance binds_single_bind_same_inv_from_binds_single_bind_same_eq :
    Binds_single_bind_same_eq -> Binds_single_bind_same_inv. 
Proof. constructor. introv I. rewrite binds_single_bind_same_eq in I. assumption. Qed.

Instance binds_single_bind_diff_eq_from_binds_single_bind_eq :
    Binds_single_bind_eq -> Binds_single_bind_diff_eq. 
Proof. 
    constructor. intros. rewrite binds_single_bind_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_single_bind_diff_from_binds_single_bind_diff_eq :
    Binds_single_bind_diff_eq -> Binds_single_bind_diff. 
Proof. constructor. introv Hd. rewrite binds_single_bind_diff_eq; auto. Qed.

End BindsSingleBind.

(* union *)
Section BindsUnion.
Context `{BagBinds A B T} `{BagIndex T A} `{BagUnion T}.

Instance binds_union_l_from_binds_union_eq :
    Binds_union_eq -> Binds_union_l.
Proof. constructor. introv. rewrite binds_union_eq. auto. Qed.

Instance binds_union_r_from_binds_union_eq :
    Binds_union_eq -> Binds_union_r.
Proof. constructor. introv. rewrite binds_union_eq. auto. Qed.

Instance binds_union_inv_from_binds_union_eq :
    Binds_union_eq -> Binds_union_inv.
Proof. constructor. introv. rewrite binds_union_eq. auto. Qed.

End BindsUnion.

(* remove *)
Section BindsRemove.
Context `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1}.

Instance binds_remove_notin_eq_from_binds_remove_eq :
    Binds_remove_eq -> Binds_remove_notin_eq.
Proof. constructor. introv Hin. rewrite binds_remove_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_remove_notin_from_binds_remove_notin_eq :
    Binds_remove_notin_eq -> Binds_remove_notin.
Proof. constructor. introv Hin I. rewrite binds_remove_notin_eq; auto. Qed.

Instance binds_remove_notin_inv_from_binds_remove_notin_eq :
    Binds_remove_notin_eq -> Binds_remove_notin_inv.
Proof. constructor. introv Hin I. rewrite binds_remove_notin_eq in I; auto. Qed.

Instance binds_remove_in_eq_from_binds_remove_eq :
    Binds_remove_eq -> Binds_remove_in_eq.
Proof. constructor. introv Hin. rewrite binds_remove_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_remove_in_from_binds_remove_in_eq :
    Binds_remove_in_eq -> Binds_remove_in.
Proof. constructor. introv Hin.  rewrite binds_remove_in_eq; auto. Qed.

Instance binds_remove_inv_from_binds_remove_eq :
    Binds_remove_eq -> Binds_remove_inv.
Proof. constructor. introv Hb. rewrite binds_remove_eq in Hb. auto. Qed.

End BindsRemove.

(* restrict *)
Section BindsRestrict.
Context `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1}.

Instance binds_restrict_in_eq_from_binds_restrict_eq :
    Binds_restrict_eq -> Binds_restrict_in_eq.
Proof. constructor. introv Hin. rewrite binds_restrict_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_restrict_in_from_binds_restrict_in_eq :
    Binds_restrict_in_eq -> Binds_restrict_in.
Proof. constructor. introv Hin I. rewrite binds_restrict_in_eq; auto. Qed.

Instance binds_restrict_in_inv_from_binds_restrict_in_eq :
    Binds_restrict_in_eq -> Binds_restrict_in_inv.
Proof. constructor. introv Hin I. rewrite binds_restrict_in_eq in I; auto. Qed.

Instance binds_restrict_notin_eq_from_binds_restrict_eq :
    Binds_restrict_eq -> Binds_restrict_notin_eq.
Proof. constructor. introv Hin. rewrite binds_restrict_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_restrict_notin_from_binds_restrict_notin_eq :
    Binds_restrict_notin_eq -> Binds_restrict_notin.
Proof. constructor. introv Hin.  rewrite binds_restrict_notin_eq; auto. Qed.

Instance binds_restrict_inv_from_binds_restrict_eq :
    Binds_restrict_eq -> Binds_restrict_inv.
Proof. constructor. introv Hb. rewrite binds_restrict_eq in Hb. auto. Qed.

End BindsRestrict.

(* update *)
Section BindsUpdate.
Context `{BagBinds A B T} `{BagUpdate A B T}.

Instance binds_update_same_eq_from_binds_update_eq :
    Binds_update_eq -> Binds_update_same_eq.
Proof. 
    constructor. intros. rewrite binds_update_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_update_same_from_binds_update_same_eq :
    Binds_update_same_eq -> Binds_update_same.
Proof. constructor. intros. rewrite binds_update_same_eq. reflexivity. Qed.

Instance binds_update_same_inv_from_binds_update_same_eq :
    Binds_update_same_eq -> Binds_update_same_inv.
Proof. constructor. introv I. rewrite binds_update_same_eq in I. assumption. Qed.

Instance binds_update_diff_eq_from_binds_update_eq :
    Binds_update_eq -> Binds_update_diff_eq.
Proof. 
    constructor. intros. rewrite binds_update_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_update_diff_from_binds_update_diff_eq :
    Binds_update_diff_eq -> Binds_update_diff.
Proof. constructor. intros. rewrite binds_update_diff_eq; assumption. Qed.

Instance binds_update_diff_inv_from_binds_update_diff_eq :
    Binds_update_diff_eq -> Binds_update_diff_inv.
Proof. constructor. introv Hd I. rewrite binds_update_diff_eq in I; assumption. Qed.

End BindsUpdate.

(* index binds *)
Section IndexBinds.
Context `{BagIndex T A} `{BagBinds A B T}.

Instance index_binds_from_index_binds_eq :
    Index_binds_eq -> Index_binds.
Proof. constructor. introv I. rewrite index_binds_eq in I. assumption. Qed.

Instance index_binds_inv_from_index_binds_eq :
    Index_binds_eq -> Index_binds_inv.
Proof. constructor. introv I. rewrite index_binds_eq. eauto. Qed.

End IndexBinds.

(* empty *)
Section IndexEmpty.
Context `{BagIndex T A} `{BagEmpty T}.

Instance index_empty_from_index_empty_eq :
    Index_empty_eq -> Index_empty.
Proof. constructor. introv. rewrite index_empty_eq. auto. Qed. 

End IndexEmpty.

(* single_bind *)
Section IndexSingleBind.
Context `{BagIndex T A} `{BagSingleBind A B T}.

Instance index_single_bind_same_eq_from_index_single_bind_eq :
    Index_single_bind_eq -> Index_single_bind_same_eq.
Proof. constructor. introv. rewrite index_single_bind_eq. auto. Qed.

Instance index_single_bind_same_from_index_single_bind_same_eq :
    Index_single_bind_same_eq -> Index_single_bind_same.
Proof. constructor. introv. rewrite index_single_bind_same_eq. auto. Qed.

Instance index_single_bind_diff_eq_from_index_single_bind_eq :
    Index_single_bind_eq -> Index_single_bind_diff_eq.
Proof. constructor. introv. rewrite index_single_bind_eq. auto. Qed.

Instance index_single_bind_diff_from_index_single_bind_diff_eq :
    Index_single_bind_diff_eq -> Index_single_bind_diff.
Proof. constructor. introv Hd. rewrite index_single_bind_diff_eq; auto. Qed.

End IndexSingleBind.

(* union *)
Section IndexUnion.
Context `{BagIndex T A} `{BagUnion T}.

Instance index_union_l_from_index_union_eq :
    Index_union_eq -> Index_union_l.
Proof. constructor. introv. rewrite index_union_eq. auto. Qed.

Instance index_union_r_from_index_union_eq :
    Index_union_eq -> Index_union_inv.
Proof. constructor. introv. rewrite index_union_eq. auto. Qed.

Instance index_union_inv_from_index_union_eq :
    Index_union_eq -> Index_union_inv.
Proof. constructor. introv. rewrite index_union_eq. auto. Qed.

End IndexUnion.

(* remove *)
Section IndexRemove.
Context `{BagIndex T A} `{BagIn A T1} `{BagRemove T T1}.

Instance index_remove_in_eq_from_index_remove_eq :
    Index_remove_eq -> Index_remove_in_eq.
Proof. 
    constructor. introv I. rewrite index_remove_eq. rew_logic. 
    apply iff_intro; intro; jauto; tryfalse.
Qed.

Instance index_remove_in_from_index_remove_in_eq :
    Index_remove_in_eq -> Index_remove_in.
Proof. constructor. introv Hi. rewrite index_remove_in_eq; auto. Qed.

Instance index_remove_notin_eq_from_index_remove_eq :
    Index_remove_eq -> Index_remove_notin_eq.
Proof. 
    constructor. introv I. rewrite index_remove_eq. rew_logic. 
    apply iff_intro; intro; jauto; tryfalse.
Qed.

Instance index_remove_notin_from_index_remove_notin_eq :
    Index_remove_notin_eq -> Index_remove_notin.
Proof. constructor. introv Hi. rewrite index_remove_notin_eq; auto. Qed.

Instance index_remove_notin_inv_from_index_remove_notin_eq :
    Index_remove_notin_eq -> Index_remove_notin_inv.
Proof. constructor. introv Hi. rewrite index_remove_notin_eq; auto. Qed.

End IndexRemove.

(* restrict *)
Section IndexRestrict.
Context `{BagIndex T A} `{BagIn A T1} `{BagRestrict T T1}.

Instance index_restrict_notin_eq_from_index_restrict_eq :
    Index_restrict_eq -> Index_restrict_notin_eq.
Proof. 
    constructor. introv I. rewrite index_restrict_eq. rew_logic. 
    apply iff_intro; intro; jauto; tryfalse.
Qed.

Instance index_restrict_notin_from_index_restrict_notin_eq :
    Index_restrict_notin_eq -> Index_restrict_notin.
Proof. constructor. introv Hi. rewrite index_restrict_notin_eq; auto. Qed.

Instance index_restrict_in_eq_from_index_restrict_eq :
    Index_restrict_eq -> Index_restrict_in_eq.
Proof. 
    constructor. introv I. rewrite index_restrict_eq. rew_logic. 
    apply iff_intro; intro; jauto; tryfalse.
Qed.

Instance index_restrict_in_from_index_restrict_in_eq :
    Index_restrict_in_eq -> Index_restrict_in.
Proof. constructor. introv Hi. rewrite index_restrict_in_eq; auto. Qed.

Instance index_restrict_in_inv_from_index_restrict_in_eq :
    Index_restrict_in_eq -> Index_restrict_in_inv.
Proof. constructor. introv Hi. rewrite index_restrict_in_eq; auto. Qed.

End IndexRestrict.

(* update *)
Section IndexUpdate.
Context `{BagIndex T A} `{BagUpdate A B T}.

Instance index_update_same_eq_from_index_update_eq : 
    Index_update_eq -> Index_update_same_eq.
Proof. constructor. introv. rewrite index_update_eq. auto. Qed.

Instance index_update_same_from_index_update_same_eq :
    Index_update_same_eq -> Index_update_same.
Proof. constructor. introv. rewrite index_update_same_eq. auto. Qed.

Instance index_update_index_from_index_update_eq : 
    Index_update_eq -> Index_update_index.
Proof. constructor. introv. rewrite index_update_eq. auto. Qed.

Instance index_update_diff_eq_from_index_update_eq : 
    Index_update_eq -> Index_update_diff_eq.
Proof. 
    constructor. introv Hd. rewrite index_update_eq. rew_logic.
    apply iff_intro; intro; intuition jauto.
Qed.

Instance index_update_diff_from_index_update_diff_eq :
    Index_update_diff_eq -> Index_update_diff.
Proof. constructor. introv Hd. rewrite index_update_diff_eq; eauto. Qed.

Instance index_update_diff_inv_from_index_update_diff_eq :
    Index_update_diff_eq -> Index_update_diff_inv.
Proof. constructor. introv Hd. rewrite index_update_diff_eq; auto. Qed.

End IndexUpdate.

Instance fresh_index_from_fresh_index_eq : 
    forall `{BagIndex T A} `{BagFresh A T}, 
    Fresh_index_eq -> Fresh_index.
Proof. constructor. introv. rewrite fresh_index_eq. auto. Qed.

Instance incl_binds_from_incl_binds_eq :
    forall `{BagIncl T} `{BagBinds A B T},
    Incl_binds_eq -> Incl_binds.
Proof. constructor. introv. rewrite incl_binds_eq. auto. Qed.

Instance incl_binds_inv_from_incl_binds_eq : 
    forall `{BagIncl T} `{BagBinds A B T},
    Incl_binds_eq -> Incl_binds_inv.
Proof. constructor. introv. rewrite incl_binds_eq. auto. Qed.

Instance incl_index_from_incl_binds :
    forall `{BagIncl T} `{BagIndex T A} `{BagBinds A B T},
    Index_binds_eq -> Incl_binds -> Incl_index.
Proof. 
    constructor. introv. rewrite_all index_binds_eq.
    hint incl_binds. introv Hincl (x&Hbinds). iauto.
Qed.

Instance empty_incl_from_incl_binds :
    forall `{BagIncl T} `{BagEmpty T} `{BagBinds A B T},
    Binds_empty_eq -> Incl_binds_eq -> Empty_incl.
Proof. constructor. intro. rewrite incl_binds_eq. introv. rewrite binds_empty_eq. iauto. Qed.

Instance incl_empty_from_incl_binds :
    forall `{BagIncl T} `{BagEmpty T} `{BagBinds A B T},
    Binds_double -> Binds_empty_eq -> Incl_binds_eq -> Incl_empty.
Proof. 
    constructor. intro. rewrite incl_binds_eq.
    rew_logic. apply iff_intro.
    introv He. apply binds_double. introv. apply iff_intro. auto. rewrite binds_empty_eq. iauto.
    intros. substs. auto.
Qed.

Create HintDb bag discriminated.

Hint Resolve 
    @binds_empty @binds_single_bind_same @binds_single_bind_diff
    @binds_union_l @binds_union_r
    @binds_remove_in @binds_remove_notin
    @binds_restrict_in @binds_restrict_notin
    @binds_update_same @binds_update_diff 
    @index_binds_inv @fresh_index 
    @incl_binds @update_nindex_incl 
    @remove_incl @restrict_incl
    @index_empty @index_single_bind_same @index_single_bind_diff
    @index_union_l @index_union_r
    @index_remove_in @index_remove_notin
    @index_restrict_in @index_restrict_notin
    @index_update_same @index_update_index @index_update_diff
: bag.

Tactic Notation "prove_bag" :=
    solve [ eauto with bag typeclass_instances ].

Hint Rewrite @binds_empty_eq @binds_single_bind_eq @binds_union_eq
    @binds_remove_eq @binds_restrict_eq
    @binds_update_eq @incl_binds_eq @index_binds_eq  
    using (eauto with typeclass_instances) : rew_binds_eq.

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

Instance update_nindex_incl_inst :
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

Instance remove_incl_inst :
    forall `{BagIncl T} `{BagRemove T T1} `{BagIn A T1} `{BagBinds A B T},
    Binds_remove_eq -> Incl_binds_eq -> Remove_incl.
Proof.
    constructor. introv.
    rewrite incl_binds_eq. introv. 
    rewrite binds_remove_eq.
    iauto.
Qed.

Instance restrict_incl_inst :
    forall `{BagIncl T} `{BagRestrict T T1} `{BagIn A T1} `{BagBinds A B T},
    Binds_restrict_eq -> Incl_binds_eq -> Restrict_incl.
Proof.
    constructor. introv.
    rewrite incl_binds_eq. introv.
    rewrite binds_restrict_eq.
    iauto.
Qed.

Instance index_empty_eq_inst : 
    forall `{BagIndex T A} `{BagBinds A B T} `{BagEmpty T},
    Index_binds_eq -> Binds_empty_eq -> Index_empty_eq.
Proof.
    constructor. introv. rewrite index_binds_eq. 
    rew_logic; apply iff_intro; intro. 
    jauto_set. rewrites binds_empty_eq in *. trivial.
    tryfalse.
Qed.

Instance index_single_bind_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagSingleBind A B T},
    Index_binds_eq -> Binds_single_bind_eq -> Index_single_bind_eq. 
Proof.
    constructor. introv. rewrite index_binds_eq. 
    rew_logic; apply iff_intro; 
    jauto_set; rew_binds_eq in *; jauto.
Qed.

Instance index_union_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagUnion T},
    Index_binds_eq -> Binds_union_eq -> Index_union_eq.
Proof.
    constructor. introv. rewrite_all index_binds_eq.
    rew_logic; apply iff_intro; introv Hi.
    jauto_set; rewrites binds_union_eq in *; iauto.
    apply case_classic_l in Hi.
    destruct Hi; jauto_set; rewrites binds_union_eq; rewrites index_binds_eq; iauto.
Qed.

Instance index_remove_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagIn A T1} `{BagRemove T T1},
    Index_binds_eq -> Binds_remove_eq -> Index_remove_eq.
Proof.
    constructor. introv. rewrite_all index_binds_eq.
    rew_logic; apply iff_intro; 
    jauto_set; rewrites binds_remove_eq in *; jauto.
Qed.

Instance index_restrict_eq_inst :
    forall `{BagIndex T A} `{BagBinds A B T} `{BagIn A T1} `{BagRestrict T T1},
    Index_binds_eq -> Binds_restrict_eq -> Index_restrict_eq.
Proof.
    constructor. introv. rewrite_all index_binds_eq.
    rew_logic; apply iff_intro; 
    jauto_set; rewrites binds_restrict_eq in *; jauto.
Qed.

Instance index_update_eq_inst :
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

(* TODO this should get to TLC LibOrder *)
Class Minimal A := { minimal : A }.
Class PickGreater A := { pick_greater : A -> A }.

Class Minimal_lt `{Lt A} `{Minimal A} := { minimal_lt : forall a, lt minimal a }.
Class PickGreater_lt `{Lt A} `{PickGreater A} := { pick_greater_lt : forall a, lt a (pick_greater a) }.

Instance minimal_inst_nat : Minimal nat := 
    { minimal := 0 }.
Instance pick_greater_inst_nat : PickGreater nat := 
    { pick_greater := S }.

(* Map signature (for hiding the implementation *)

Module Type FinmapSig.
Section Definitions. 

Variables (A B : Type).

Parameter finmap : forall (A B : Type), Type.

Set Implicit Arguments.

Parameter from_list_impl : list (A * B) -> finmap A B.
Parameter to_list_impl : finmap A B -> list (A * B).

Parameter empty_impl : finmap A B.
Parameter single_bind_impl : A -> B -> finmap A B.
Parameter index_impl : finmap A B -> A -> Prop.
Parameter binds_impl : finmap A B -> A -> B -> Prop.
Parameter incl_impl : finmap A B -> finmap A B -> Prop.
Parameter read_impl : Inhab B -> finmap A B -> A -> B.
Parameter read_option_impl : finmap A B -> A -> option B.
Parameter union_impl : finmap A B -> finmap A B -> finmap A B.
Parameter remove_impl : finmap A B -> finset A -> finmap A B.
Parameter restrict_impl : finmap A B -> finset A -> finmap A B.
Parameter update_impl : finmap A B -> A -> B -> finmap A B.
Parameter card_impl : finmap A B -> nat.
Parameter fresh_impl : Minimal A -> PickGreater A -> finmap A B -> A. (* TODO good typeclasses *)

Parameter binds_double_impl : forall M M', (forall k x, binds_impl M k x <-> binds_impl M' k x) -> M = M'.

Parameter incl_binds_eq_impl : forall M1 M2, incl_impl M1 M2 = forall k x, binds_impl M1 k x -> binds_impl M2 k x.
Parameter read_option_binds_eq_impl : forall M k x, (read_option_impl M k = Some x) = binds_impl M k x.
Parameter binds_empty_eq_impl : forall k x, binds_impl empty_impl k x = False.
Parameter binds_single_bind_eq_impl : forall k k' x x', 
    binds_impl (single_bind_impl k' x') k x = (k = k' /\ x = x').
Parameter binds_union_eq_impl : forall M1 M2 k x,
    binds_impl (union_impl M1 M2) k x = (binds_impl M1 k x \/ ~index_impl M1 k /\ binds_impl M2 k x).
Parameter binds_remove_eq_impl : forall M S k x,
    binds_impl (remove_impl M S) k x = (binds_impl M k x /\ k \notin S).
Parameter binds_restrict_eq_impl : forall M S k x,
    binds_impl (restrict_impl M S) k x = (binds_impl M k x /\ k \in S).
Parameter binds_update_eq_impl : forall M k k' x x', 
    binds_impl (update_impl M k' x') k x = (k = k' /\ x = x' \/ k <> k' /\ binds_impl M k x).
Parameter index_binds_eq_impl : forall M k, index_impl M k = exists x, binds_impl M k x.
Parameter fresh_index_eq_impl : forall M c1 c2, index_impl M (fresh_impl c1 c2 M) = False.

Parameter from_list_binds_eq_impl : forall L k x, binds_impl (from_list_impl L) k x = Assoc k x L.
Parameter to_list_binds_eq_impl : forall M k x, Assoc k x (to_list_impl M) = binds_impl M k x.

End Definitions.
End FinmapSig.

(* Implementation *)

Module Export FinmapImpl : FinmapSig.
Section Definitions.

Variables (A B : Type).
Context {LTA : Lt A}.
Context {IA : Inhab A}.
Context {IB : Inhab B}.
Context {MMA : Minimal A}.
Context {PGA : PickGreater A}.
Context {ST : Lt_strict_total_order }.

Definition finite (M : map A B) :=
  exists (S : finset A), forall x, index M x -> x \in S.

Definition finmap := sig finite.

Implicit Types k : A.
Implicit Types x : B.
Implicit Types M : finmap.

Definition build_finmap `(F:finite U) : finmap := exist finite U F.

(* TODO: most properties should follow from finset and map properties.
   Nice prerequisite: lib-bag-ize LibMap. *)

Set Implicit Arguments.

Lemma finite_empty : finite \{}.
Proof.
  exists (\{} : finset A). 
Admitted.

Lemma single_bind_finite : forall k x, finite (k \:= x).
Proof.
  intros. exists \{k}. intros y. 
Admitted.

Lemma union_finite : forall U V : map A B,
  finite U -> finite V -> finite (U \u V).
Proof.
  introv [S1 E1] [S2 E2]. exists (S1 \u S2). intros x.
  rewrite in_union_eq. 
Admitted.

Lemma remove_finite : forall U {S : set A}, finite U -> finite (U \- S).
Proof.
  introv [S1 E1]. exists S1. 
Admitted.

Lemma update_finite : forall U k x, finite U -> finite (U \(k := x)).
Proof.
  introv [S1 E1]. exists (S1 \u \{k}).
Admitted.

Definition empty_impl : finmap := build_finmap finite_empty.
Definition single_bind_impl k x : finmap := build_finmap (single_bind_finite k x).
Definition index_impl M k : Prop := index (proj1_sig M) k.
Definition binds_impl M k x : Prop := binds (proj1_sig M) k x.
Definition incl_impl M1 M2 : Prop := forall k x, binds_impl M1 k x -> binds_impl M2 k x.
Definition read_option_impl M k : option B := proj1_sig M k. (* TODO abstract it!!! change TLC *)
Definition read_impl M k : B := proj1_sig M \(k).
Definition union_impl M1 M2 : finmap := build_finmap (union_finite (proj2_sig M1) (proj2_sig M2)).
Definition remove_impl M (S : finset A) : finmap.
Admitted.
Definition restrict_impl M (S : finset A) : finmap.
Admitted.
Definition update_impl M k x : finmap := build_finmap (update_finite k x (proj2_sig M)).
Definition fresh_impl : Minimal A -> PickGreater A -> finmap -> A.
Admitted.

Definition binds_double_impl : forall M M', (forall k x, binds_impl M k x <-> binds_impl M' k x) -> M = M'.
Admitted.

Definition listish (U : map A B) := 
  exists L, forall k x, binds U k x = Mem (k, x) L.

Lemma finite_listish : forall U, finite U -> listish U.
Proof.
Admitted.

Definition from_list_impl (L : list (A * B)) : finmap := 
  fold_right (fun p acc => let '(k, x) := p in update_impl acc k x) empty_impl L.

Definition to_list_impl M := proj1_sig (indefinite_description (finite_listish (proj2_sig M))).

Definition card_impl M := length (to_list_impl M).

Lemma read_option_binds_eq_impl : forall M k x, (read_option_impl M k = Some x) = binds_impl M k x.
Proof.
Admitted.

Lemma incl_binds_eq_impl : forall M1 M2, incl_impl M1 M2 = forall k x, binds_impl M1 k x -> binds_impl M2 k x.
Proof. unfold incl_impl. auto. Qed.
Parameter binds_empty_eq_impl : forall k x, binds_impl empty_impl k x = False.
Parameter binds_single_bind_eq_impl : forall k k' x x', 
    binds_impl (single_bind_impl k' x') k x = (k = k' /\ x = x').
Parameter binds_union_eq_impl : forall M1 M2 k x,
    binds_impl (union_impl M1 M2) k x = (binds_impl M1 k x \/ ~index_impl M1 k /\ binds_impl M2 k x).
Parameter binds_remove_eq_impl : forall M S k x,
    binds_impl (remove_impl M S) k x = (binds_impl M k x /\ k \notin S).
Parameter binds_restrict_eq_impl : forall M S k x,
    binds_impl (restrict_impl M S) k x = (binds_impl M k x /\ k \in S).

Lemma binds_update_eq_impl : forall M k k' x x', 
    binds_impl (update_impl M k' x') k x = (k = k' /\ x = x' \/ k <> k' /\ binds_impl M k x).
Proof.
    intros.
    rew_logic.
    apply iff_intro; intro H.
    skip.
Admitted.

Parameter index_binds_eq_impl : forall M k, index_impl M k = exists x, binds_impl M k x.
Parameter fresh_index_eq_impl : forall M c1 c2, index_impl M (fresh_impl c1 c2 M) = False.

Parameter from_list_binds_eq_impl : forall L k x, binds_impl (from_list_impl L) k x = Assoc k x L.
Parameter to_list_binds_eq_impl : forall M k x, Assoc k x (to_list_impl M) = binds_impl M k x.

End Definitions.
End FinmapImpl.

Section Instances.

Variables (A B : Type).
Context {LTA : Lt A}.
Context {IB : Inhab B}.
Context {ST : Lt_strict_total_order }.

Global Instance empty_inst : BagEmpty (finmap A B) :=
    { empty := @empty_impl _ _ }.

Global Instance single_bind_inst : Lt_strict_total_order -> BagSingleBind A B (finmap A B) :=
    { single_bind := @single_bind_impl _ _ }.

Global Instance index_inst : BagIndex (finmap A B) A :=
    { index := @index_impl _ _ }.

Global Instance binds_inst : BagBinds A B (finmap A B) :=
    { binds := @binds_impl _ _ }.

Global Instance incl_inst : BagIncl (finmap A B) :=
    { incl := @incl_impl _ _ }.

Global Instance read_inst : BagRead A B (finmap A B) :=
    { read := @read_impl _ _ _ }.

Global Instance read_option_inst : BagReadOption A B (finmap A B) :=
    { read_option := @read_option_impl _ _ }.

Global Instance union_inst : BagUnion (finmap A B) :=
    { union := @union_impl _ _ }.

Global Instance remove_inst : BagRemove (finmap A B) (finset A) :=
    { remove := @remove_impl _ _ }.

Global Instance restrict_inst : BagRestrict (finmap A B) (finset A) :=
    { restrict := @restrict_impl _ _ }.

Global Instance update_inst : BagUpdate A B (finmap A B) :=
    { update := @update_impl _ _ }.

Global Instance card_inst : BagCard (finmap A B) :=
    { card := @card_impl _ _ }.

Global Instance from_list_inst : BagFromList (A * B) (finmap A B) :=
    { from_list := @from_list_impl _ _ }.

Global Instance to_list_inst : BagToList (A * B) (finmap A B) :=
    { to_list := @to_list_impl _ _ }.

Global Instance fresh_inst : Minimal A -> PickGreater A -> BagFresh A (finmap A B) :=
    { fresh := @fresh_impl _ _ _ _ }.

Global Instance binds_double_inst : Binds_double :=
    { binds_double := @binds_double_impl _ _ }.

Global Instance incl_binds_eq_inst : Incl_binds_eq :=
    { incl_binds_eq := @incl_binds_eq_impl _ _ }.

Global Instance read_option_binds_eq_inst : Read_option_binds_eq :=
    { read_option_binds_eq := @read_option_binds_eq_impl _ _ }.

Global Instance binds_empty_eq_inst : Binds_empty_eq := 
    { binds_empty_eq := @binds_empty_eq_impl _ _ }.

Global Instance binds_single_bind_eq_inst : Binds_single_bind_eq := 
    { binds_single_bind_eq := @binds_single_bind_eq_impl _ _ }.

Global Instance binds_union_eq_inst : Binds_union_eq :=
    { binds_union_eq := @binds_union_eq_impl _ _ }.

Global Instance binds_remove_eq_inst : Binds_remove_eq :=
    { binds_remove_eq := @binds_remove_eq_impl _ _ }.

Global Instance binds_restrict_eq_inst : Binds_restrict_eq :=
    { binds_restrict_eq := @binds_restrict_eq_impl _ _ }.

Global Instance binds_update_eq_inst : Binds_update_eq :=
    { binds_update_eq := @binds_update_eq_impl _ _ }.

Global Instance index_binds_eq_inst : Index_binds_eq :=
    { index_binds_eq := @index_binds_eq_impl _ _ }.

Global Instance fresh_index_eq_inst : 
    forall (c1 : Minimal A) (c2 : PickGreater A), Fresh_index_eq (A := A) (T := finmap A B) :=
    { fresh_index_eq := fun x => @fresh_index_eq_impl _ _ x _ _ }.

Global Instance from_list_binds_eq_impl : From_list_binds_eq :=
    { from_list_binds_eq := @from_list_binds_eq_impl _ _ }.

Global Instance to_list_binds_eq_impl : To_list_binds_eq :=
    { to_list_binds_eq := @to_list_binds_eq_impl _ _ }.

End Instances.

Global Opaque empty_inst single_bind_inst in_inst binds_inst read_inst
    read_option_inst remove_inst update_inst card_inst fresh_inst.

(* Extraction. *)

Extraction Language Ocaml.

Extract Constant FinmapImpl.finmap "'A" "'B" => "('A, 'B) BatMap.t". 
Extract Constant FinmapImpl.from_list_impl => "fun l -> BatMap.of_enum (BatList.enum l)".
Extract Constant FinmapImpl.to_list_impl => "fun m -> BatMap.bindings m".
Extract Constant FinmapImpl.empty_impl => "BatMap.empty".
Extract Constant FinmapImpl.single_bind_impl => "fun k x -> BatMap.singleton k x".
Extract Constant FinmapImpl.read_impl => "fun m k -> BatMap.find k m".
Extract Constant FinmapImpl.read_option_impl => "fun m k -> try Some (BatMap.find k m) with Not_found -> None".
Extract Constant FinmapImpl.union_impl => "fun m1 m2 -> BatMap.union m2 m1".
Extract Constant FinmapImpl.remove_impl => "fun m s -> BatList.fold_right (BatMap.remove) (FinsetImpl.to_list_impl s) m". 
Extract Constant FinmapImpl.restrict_impl => "fun m s -> BatList.fold_left (fun cc i -> BatMap.add i (BatMap.find i m) cc) BatMap.empty (FinsetImpl.to_list_impl s)".
Extract Constant FinmapImpl.update_impl => "fun m k x -> BatMap.add k x m".
Extract Constant FinmapImpl.card_impl => "fun m -> BatMap.cardinal m".
Extract Constant FinmapImpl.fresh_impl => "fun mm pg m -> if BatMap.is_empty m then mm else pg (fst (BatMap.max_binding m))".
