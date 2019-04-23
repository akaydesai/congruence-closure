Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations. (* Why does Require complain about path? *)

Require Import Coq.Classes.EquivDec.

Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Require Import Coq.Lists.ListSet.
Require Import Coq.Bool.Bool. (* For reflect et al. *)

Inductive term : Set :=
  | var : nat -> term.
(*   | fn : nat -> term -> term. *)

Scheme Equality for term.
(* nat_beq is defined
term_beq is defined
term_eq_dec is defined  *)

(* a = b \/ a <> b. *)
Corollary term_eq_decidable : forall (a b:term), Decidable.decidable (a = b). 
Proof. intros. pose ( T := term_eq_dec a b). destruct T. left. assumption. right. assumption. Qed.

(* Let's obtain a decision procedure for term*term *)
Definition term_pair_beq (x y : term * term) : bool :=
  match x, y with
  | (x1, x2), (y1,y2) => if term_beq x1 y1 then term_beq x2 y2 else false
  end.

(* From VFA *)
Print reflect.

Lemma nat_beq_refl : forall x, nat_beq x x = true.
Proof.
  intros x. induction x. 
  - reflexivity.
  - simpl. apply IHx.
Qed.
Lemma term_beq_refl: forall a, term_beq a a  = true.
Proof.
  intros a. destruct a as [ a0 ]. simpl. apply nat_beq_refl.
Qed.

Print beq_nat. Print eqb.
(* Let's just show these two are the same, then we get lemmas for free. *)
Lemma nat_beq_is_eqb : forall x y, nat_beq x y = beq_nat x y.
Proof.
  intros x y. unfold nat_beq, beq_nat.
  destruct x, y; reflexivity.
Qed.

Lemma term_beq_reflect : forall x y, reflect (x = y) (term_beq x y).
Proof.
  intros x y. apply iff_reflect. split.
  - (* x = y -> term_beq x y = true *)
    intro x_eq_y. subst. apply (term_beq_refl).
  - destruct x as [x0 ], y as [y0]. simpl. intros.
    rewrite nat_beq_is_eqb in H. apply beq_nat_true in H. subst. reflexivity.
Qed.

Lemma term_pair_beq_reflect : forall x y, reflect (x = y) (term_pair_beq x y).
Proof.
  intros x y. Search reflect. apply iff_reflect. split.
  - intros x_eq_y. subst. destruct y as [y1 y2]. simpl. 
    repeat rewrite term_beq_refl. reflexivity.
  - intros x_beq_y. destruct x as [x1 x2], y as [y1 y2]. simpl in *.
    (* Need to reflect term first. *)
    destruct x1, y1, x2, y2. simpl in *. 
    repeat rewrite nat_beq_is_eqb in x_beq_y. rewrite (nat_beq_is_eqb n1 n2) in x_beq_y.
    case (n =? n0) eqn: case1, (n1 =? n2) eqn: case2; 
    try apply beq_nat_true in case1; try apply beq_nat_false in case2.
    + apply beq_nat_true in case2. subst. reflexivity.
    + subst. discriminate.
    + discriminate.
    + discriminate.
Qed.

Check term_pair_beq.
Locate "*". Search prod. 
Locate "=". Search (prod _ _). Check injective_projections. 
Search "prod_eqdec".
Check prod_eqdec. Check EqDec. Check Equivalence.
Check EqDec term eq. Locate "<>". Search (not (eq _ _)).

(* Dual of injective_projections *)
Lemma uneq_pair {A B : Type}: forall  (p1 p2 : A * B), 
  fst p1 <> fst p2 \/ snd p1 <> snd p2 -> p1 <> p2.
Proof.
  intros. unfold not in *. destruct H; intros; apply H; subst; reflexivity. Qed.
Lemma uneq_pair1 {A B : Type}: forall  (p1 p2 : A * B), 
  fst p1 <> fst p2 -> p1 <> p2.
Proof. intros. unfold not in *. intros. subst. apply H. reflexivity. Qed.
Lemma uneq_pair2 {A B : Type}: forall  (p1 p2 : A * B), 
  snd p1 <> snd p2 -> p1 <> p2.
Proof. intros. unfold not in *. intros. subst. apply H. reflexivity. Qed.

Print sumbool.
Definition term_pair_eq_dec (x y : term * term) : {x = y} + {x <> y} :=
  match x, y with
  | (x1, x2), (y1,y2) => 
    match term_eq_dec x1 y1, term_eq_dec x2 y2 with
    | left eqx1y1, left eqx2y2 => 
          left (injective_projections (x1,x2) (y1,y2) eqx1y1 eqx2y2)
    | right a , _ => right (uneq_pair1 (x1,x2) (y1,y2) a)
    | _ , right b => right (uneq_pair2 (x1,x2) (y1,y2) b)
    (* Fix this hack of a definition. *)
    end
  end.

Compute term_pair_eq_dec ((var 1),(var 2)) ((var 3),(var 4)).
Eval compute in term_pair_eq_dec ((var 1),(var 2)) ((var 3),(var 4)).
Compute term_pair_eq_dec ((var 1),(var 2)) ((var 1),(var 2)).

(* Alternate correctness condition; using ListSet. *)
Check set_In.
Inductive proof (l : set (term*term)) : term -> term -> Prop :=
  | proofAxm : forall s t, set_In (s, t) l -> proof l s t
  | proofRefl : forall t, proof l t t
  | proofSymm : forall s t, proof l s t -> proof l t s
  | proofTrans : forall s t u, set_In (s,t) l -> proof l t u -> proof l s u. 

Fixpoint subterms (t : term) : list term :=
  match t with
  | var n => [var n]
(*   | fn n t1 => (fn n t1) :: subterms t1 *)
  end.

Inductive Is_subterm (t:term) : term -> Prop :=
  | subAxm : Is_subterm t t.
(*   | subFn : forall n s, t = fn n s -> Is_subterm t s *)
(*   | subTrans : forall r s, Is_subterm t s -> Is_subterm r s -> Is_subterm t s. *)

(* Lemma subterm_fn_mono : forall n t s, Is_subterm t s -> Is_subterm (fn n t) s.
Proof.
  intros. 
(*   Check subFn. apply (subFn (fn n t) n). *)
  induction H.
  - apply (subFn (fn n t) n). reflexivity.
  - induction t as [ k | j t' IHt'].
    + inversion H.
    + inversion H. subst.
Admitted. *)

(* Theorem subterms_fn_sound : forall t s, In s (subterms t) -> Is_subterm t s.
Proof.
  intros. induction t as [ n | n t' IHt'].
  - simpl in *. destruct H.
    + subst. apply subAxm.
    + contradiction.
  - simpl in *. destruct H.
    + subst. apply subAxm.
    + apply IHt' in H. apply subterm_mono. assumption.
(*       apply (subFn (fn n t') n _). *)
Qed. *)

(*   intros. apply (Is_subterm_ind t).
  - apply subAxm.
  - intros. destruct t.
    + simpl in *. destruct H.
      * inversion H0.
      * contradiction.
    + inversion H0. subst. Check subFn. apply (subFn (fn n s0) n _). reflexivity.
  -  simpl in *. *)

Theorem subterms_sound_complete : forall t s, In s (subterms t) <-> Is_subterm t s.
Proof.
  split.
  - intros. destruct t. destruct H.
    + inversion H. apply subAxm.
    + contradiction.
  - intros. unfold subterms. destruct t as [tn]. simpl. destruct s as [sn].
    inversion H. subst. left. reflexivity.
Qed.

Fixpoint flatn (l : set (term *term)) : (list term) :=
  match l with
  | [] => []
  | (t1, t2)::l' => t1::t2::flatn l'
  end.

Theorem flatn_sound_complete : forall l t, 
   In t (flatn l) <-> (exists x, In (t, x) l \/ In (x, t) l).
Proof.
  split.
  - intros. induction l as [|hl l' IHl'].
    + simpl in *. contradiction.
    + simpl in H. destruct hl as [hl1 hl2]. simpl in H. destruct H.
      * subst. exists hl2. left. simpl. left. reflexivity.
      * { destruct H.
        - subst. exists hl1. right. simpl. left. reflexivity.
        - apply IHl' in H. destruct H. exists x. simpl. destruct H.
          + left. right. assumption.
          + right. right. assumption. }
  - intros. induction l as [|hl l' IHl'].
    + repeat destruct H.
    + destruct H as [x H]. simpl. destruct hl as [hl1 hl2].
      destruct H.
      * { destruct H.
        - inversion H. simpl. left. reflexivity.
        - simpl. right. right. apply IHl'. exists x. left. assumption. }
      * { simpl in *. destruct H.
        - inversion H. right. left. reflexivity.
        - right. right. apply IHl'. exists x. right. assumption. }
Qed.

(* Returns list of all subterms; may have dupes. *)
Fixpoint get_subterms (l : list term) : (list term) :=
  match l with
  | [] => []
  | t::l' => (subterms t) ++ get_subterms l'
  end.

Theorem get_subterms_sound_complete: forall l s, 
  In s (get_subterms l) <-> exists t, In t l /\ Is_subterm t s. 
  (* Problem of non uniq t in completeness proof. *)
Proof.
  split.
  - intros. induction l as [| hl l' IHl'].
    + simpl in H. contradiction.
    + simpl in H. destruct hl as [hn]. simpl in *. destruct H.
      * { exists s. split.
        - left. assumption.
        - constructor. }
      * { pose ( T := IHl' H).  destruct T as [x T]. exists x. split.
        - right. apply T.
        - apply T. }
  - induction l as [|hl l' IHl'].
    + simpl. intros. destruct H,H. contradiction.
    + intros. destruct H, H. Search (In _ _ -> exists _, _). simpl in H. destruct H.
      * simpl. apply in_or_app. subst. destruct x as [xn]. simpl in *.
        left. left. inversion H0. reflexivity.
      * { apply in_split in H. destruct H as [l1], H as [l2]. simpl in *.
        apply in_or_app. right. apply IHl'.
        exists x. split.
        - destruct l1 as [|hl1 l1'].
          + simpl in H. subst. simpl. left. reflexivity. 
          + subst l'. simpl. right. apply in_or_app. right. 
            simpl. left. reflexivity.
        - assumption. }
Qed.
  
(*   - intros. induction l as [| hl l' IHl'].
    + repeat destruct H.
    + simpl in *. Search ( In _ _ \/ In _ _).
      apply (in_or_app (subterms hl) (get_subterms l') s).
      destruct hl as [hln]. simpl in *. destruct H as [t H].
      left. destruct H. inversion H0. subst. destruct H.
      * left. assumption.
      * destruct s.

  - intros. induction l as [| hl l' IHl'].
    + repeat destruct H.
    + simpl in *. apply in_or_app. destruct hl as [hn]. simpl.
      left. destruct H, H. inversion H0. subst. destruct H.
      * left. assumption.
      * destruct s as [sn].
    
    + simpl in *. destruct hl as [hln]. simpl in *.
      left. destruct H. destruct H. destruct s as [sn], x as [xn].
      destruct H.
      * inversion H0. subst. assumption.
      * inversion H0. subst. (* Dammit! *)
    
    + simpl in *. destruct hl as [hln]. simpl in *.
      right. apply IHl'. clear IHl'.
      destruct H as [t H]. destruct H. exists t. split.
      * { destruct H.
        -  (* Not true. Damn! *)
         }
      * apply H. 
Abort. *)

(* Adding and removing elements from sets. *)
Check set_add (list_eq_dec term_eq_dec) [(var 2)] nil.
Definition setterm_eq_dec := list_eq_dec term_eq_dec.
Definition set_setterm_add := set_add setterm_eq_dec.
Definition set_term_add := set_add term_eq_dec.
Compute set_term_add (var 2) nil.
Compute set_setterm_add [(var 5)] [[(var 1);(var 2)];[(var 3)];[(var 4)]].
(* ---------- ---------- ---------- *)

Check nodup. Check map.
(* Create initial unionfind set. *)
Definition create_ufs (l : set (term*term)) : (set (set term)) :=
  map (fun t => t::nil) (nodup term_eq_dec (get_subterms (flatn l))).

Compute create_ufs [(var 1, var 2); (var 1, var 3); (var 3,var 4)].
(* Why no type error due to set vs list discrepancy? Coz Definition is at term level. *)

(* ---- MAIN INVARIANTS ---- *)
Print set_In. Check term_eq_dec.
(* Invariant for ufs, states that all elements of a class are equal wrt l. *)
Definition EqInvar (l: set (term * term)) (ufs: set (set term)) := 
  forall (c:set term), set_In c ufs -> 
    forall (a b: term), set_In a c /\ set_In b c -> 
      proof l a b.
Print EqInvar.
(* Disjoint classes invariant for ufs. Required for uniqueness of representative. *)
Definition DisjntInvar (ufs: set (set term)) := 
  forall (c1 c2 : set term), set_In c1 ufs /\ set_In c2 ufs ->
    ~ (exists x, set_In x c1 /\ set_In x c2).
(* ------------ ------------ *)
(* Search "eq_dec".
Fixpoint has_succ (x : nat) (l : list term) : option term :=
  match l with
  | [] => None
  | h::l'=> match term_eq_dec (var (S x)) h with
            | left _ _ => Some h
            | right _ _ => has_succ x l'
            end
  end.
(* This works ok, then why doesn't uf_find? *)
Compute has_succ 3 [(var 2); (var 1); (var 4)].

Check set_In_dec term_eq_dec (var 3) (cons (var 3) nil).
Check set_In_dec. Print option. Print sumbool. About set_In_dec.
(* Approach 1 for find *)
Fixpoint uf_find (x : term) (ufs : set (set term)) : option (set term) :=
  match ufs with
  | [] => None
  | uh::ufs' => match (set_In_dec term_eq_dec x uh) with (* set_In_dec is opaque. *)
                | left _ _ => Some uh 
                | right _ _ => uf_find x ufs'
                end
  end.
Compute uf_find (var 3) nil.
Compute uf_find (var 3) (cons nil nil). (* Why not normal? *) *)

Check set_mem term_eq_dec.
(* Approach 1 for find *)
Fixpoint uf_find (x : term) (ufs : set (set term)) : option (set term) :=
  match ufs with
  | [] => None
  | uh::ufs' => if (set_mem term_eq_dec x uh) then Some uh else uf_find x ufs'
  end.

Compute uf_find (var 3) (cons ((cons (var 3) nil)) nil).
Compute uf_find (var 3) (create_ufs [(var 1, var 2); (var 1, var 3); (var 3,var 4)]).

(* Approach 2 for find - returning proofs. *)
(* Fixpoint uf_search (x:term) (ufs : set (set term)) : 
  forall (c : set term), {set_In x c} + {~ set_In x c} :=
    match ufs with
    | [] => right (set_In_dec term_eq_dec x [])
    | uh::ufs' => 
      match set_In_dec term_eq_dec x uh with
      | left xInuh => left xInuh
      end
    end. *)

Check set_add.
Compute set_setterm_add (set_union term_eq_dec [(var 5)] [(var 3)]) (set_remove setterm_eq_dec [(var 3)] [[(var 1);(var 2)];[(var 3)];[(var 4)]]).
Compute set_remove setterm_eq_dec [(var 3)] (set_remove setterm_eq_dec [(var 3)] [[(var 1);(var 2)];[(var 3)];[(var 4)]]). (* Removing elem not in set. *)
(* Merge classes containing x and y. *) 
(* Dep types to assert x & y oocur in some class? *) (* merge needs "proof l a b" *)
Definition uf_merge (ufs : set (set term)) (x y :term) : set (set term) :=
  let Qx := uf_find x ufs in (* Qx : query x *)
  let Qy := uf_find y ufs in
  match Qx, Qy with
  | Some Sx, Some Sy => 
        set_setterm_add (set_union term_eq_dec Sx Sy) (set_remove setterm_eq_dec Sy (set_remove setterm_eq_dec Sx ufs)) 
  | _, _ => ufs
  end.

Compute uf_merge [[(var 1);(var 2)];[(var 3)];[(var 4)]] (var 3) (var 0).
Compute uf_merge [[(var 1);(var 2)];[(var 3)];[(var 4)]] (var 3) (var 1).

Fixpoint do_cc (work : set (term*term)) (ufs : set (set term)) :=
  match work with
  | nil => ufs
  | (t1, t2)::work' => do_cc work' (uf_merge ufs t1 t2)
  end.

Compute do_cc [(var 1, var 2); (var 1, var 3); (var 3,var 4)] (create_ufs [(var 1, var 2); (var 1, var 3); (var 3,var 4)]).

Print setterm_eq_dec.
Definition cc_algo (work : set (term*term)) (t1 t2 : term) : bool :=
  let ufs := create_ufs work in (* Add query terms so uf_find need not return option. *)
  let res := do_cc work ufs in
  let Qt1 := uf_find t1 res in
  let Qt2 := uf_find t2 res in
  match Qt1, Qt2 with
  | Some St1, Some St2 => 
    match setterm_eq_dec St1 St2 with
    | left _ => true
    | _ => false
    end
  | _, _ => false
  end.
Compute cc_algo [(var 1, var 2); (var 1, var 3); (var 3,var 4)] (var 2) (var 4).

(* Lemma EqInvar_emp : forall a l, ~ EqInvar (a::l) [].  ??? *)

Lemma uf_find_emp : forall a, uf_find a [] = None.
(* Generalize to non-occurence later. *)
Proof. intros. reflexivity. Qed.

Lemma uf_merge_emp : forall a b, uf_merge [] a b = [].
Proof. intros. unfold uf_merge. rewrite uf_find_emp. reflexivity. Qed.

Lemma do_cc_emp : forall l, do_cc l [] = [].
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. destruct a. rewrite uf_merge_emp. assumption.
Qed.

(* Theorem uf_merge_inv : forall a b l ufs, set_In (a,b) l  /\ EqInvar l ufs -> EqInvar l (uf_merge ufs a b).
Proof.
  intros. unfold EqInvar in *. intros. destruct H, H1.
(*   assert(exists Ca, set_In a Ca /\ set_In Ca ufs). admit. *)
(*   assert(exists Cb, set_In b Cb /\ set_In Cb ufs). admit. *)
(*   destruct H4 as [Ca], H5 as [Cb]. pose (U := set_union term_eq_dec Ca Cb). *)
  unfold uf_merge in H0. case (uf_find a ufs) eqn:case1, (uf_find b ufs) eqn:case2. 
Abort. *)

Theorem do_cc_inv : 
  forall (l: set (term * term)) (ufs: set (set term)), 
    EqInvar l ufs -> EqInvar l (do_cc l ufs).
Proof.
  intros. induction ufs as [|uh ufs' IHufs'].
  - rewrite do_cc_emp. assumption.
  - induction l as [| hl l' IHl'].
    + simpl in *. assumption.
    + (* Show prop of EqInvar WRT ufs. ie. From "EqInVar (hl::l') (uh::ufs')" follows: *)
    assert (EqInvar (hl::l') ufs'). admit.
    (* Now, how do you write "do_cc l (uh::ufs')" into "do_cc l ufs'" *)
    simpl in *. destruct hl as [hl1 hl2]. (* Need case on uh = find(hl1 or hl2) *)
    unfold uf_merge.
    case (uf_find hl1 (uh::ufs')) eqn: case1, (uf_find hl2 (uh::ufs')) eqn: case2.
      * unfold set_setterm_add.
        (* Damn *) 
    



  intros. induction l as [|hl l' IHl'], ufs as [|uh ufl']; try (simpl; assumption).
  - simpl. destruct hl as [hl1 hl2]. assert (uf_merge [] hl1 hl2 = []). admit.
    rewrite H0. (* Can't write Eqinvar l in terms of l', induct on ufs. *)
  -
  

  intros. 
  induction l as [|hl l' IHl'].
(*     destruct l as [| hl l']. *)
  - unfold do_cc. assumption.
  - simpl in *. destruct hl as [hl1 hl2]. (* We have 'proof l hl1 hl2' *)
    assert (proof ((hl1,hl2)::l') hl1 hl2). admit.
    unfold EqInvar in *. intros. apply (H c). 
    + 
    + assumption.
