(* Author: Akshay
 *)
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
Check set_In_dec term_eq_dec.
Corollary set_In_decidable : 
  forall (a : term) (s : set term), 
    Decidable.decidable (set_In a s). 
Proof. intros. pose ( T := set_In_dec term_eq_dec a s). destruct T. left. assumption. right. assumption. Qed.

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
Check reflect. Print reflect. 
About term_eq_dec. (* is transparent *)
About set_In_dec. (* is opaque. *)
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
    (* Fix this hack of a definition? *)
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
  | proofTrans : forall s t u, proof l s t -> proof l t u -> proof l s u.
(*   | proofCong : forall (n : nat) s t, proof l s t -> proof l (fn n s) (fn n t). *)

Lemma proof_monotonic : forall h l a b, proof l a b -> proof (h::l) a b.
Proof.
  intros h l a b Hprf. induction Hprf.
  - apply proofAxm. simpl. right. assumption.
  - apply proofRefl.
  - apply proofSymm. assumption.
  - apply (proofTrans (h::l) s t u); assumption.
Qed.

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

(* Theorem create_ufs_sound_complete : forall l t, *)

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
  forall (c1 c2 : set term) (x : term), 
    set_In c1 ufs /\ set_In c2 ufs ->
      set_In x c1 /\ set_In x c2 -> c1 = c2.
(* Third invariant is NoDup ufs. *)
Definition ContainInvar (l: set (term*term)) (ufs: set (set term)) :=
  forall t1 t2, In (t1, t2) l -> 
    exists ct1 ct2,  (In t1 ct1 /\ In ct1 ufs) /\ (In t2 ct2 /\ In ct2 ufs).
(* ------------ ------------ *)

Check set_mem term_eq_dec.
(* Approach 1 for find *)
Fixpoint uf_find (x : term) (ufs : set (set term)) : option (set term) :=
  match ufs with
  | [] => None
  | uh::ufs' => if (set_mem term_eq_dec x uh) then Some uh else uf_find x ufs'
  end.

Compute uf_find (var 3) (cons ((cons (var 3) nil)) nil).
Compute uf_find (var 3) (create_ufs [(var 1, var 2); (var 1, var 3); (var 3,var 4)]).

Lemma DisjntInvar_tail : forall a l, DisjntInvar (a::l) -> DisjntInvar l.
Proof.
  intros a l H1. unfold DisjntInvar in *. unfold set_In in *.
  intros c1 c2 x H2 H3. apply (H1 c1 c2 x).
  - destruct H2, H3. simpl. split; [ right | right ]; assumption.
  - assumption.
Qed.

Theorem uf_find_some_sound_complete : forall a s ufs,
  DisjntInvar ufs ->
    uf_find a ufs = Some s <-> set_In s ufs /\ set_In a s.
Proof.
  intros a s ufs Hdisj. split.
  (* One direction does not need uniqueness/disjntinvar. *)
  - induction ufs as [|uh ufs' IHufs']. 
    + intros. inversion H.
    + intros H1. simpl in *. case (set_mem term_eq_dec a uh) eqn:case1.
      * { inversion H1. split.
        - left. reflexivity.
        - subst. Search set_mem. apply set_mem_correct1 in case1. assumption. }
      * { split.
        - right. apply IHufs' in H1. 
          + destruct H1. assumption.
          + apply DisjntInvar_tail in Hdisj. assumption.
        - apply IHufs'; try (apply DisjntInvar_tail in Hdisj); assumption. }
  - intros H1. induction ufs as [|uh ufs' IHufs'].
    + destruct H1. contradiction.
    + simpl. case (set_mem term_eq_dec a uh) eqn:case1.
      * { simpl in *. destruct H1 as [[H1 | H2] H3].
        - subst. reflexivity.
        - apply set_mem_correct1 in case1. 
          (* Use DisjntInvar to show uh = s *) (* Would be nice to have NoDup as invariant?? *)
          assert ( T : uh = s).
          {
            unfold DisjntInvar in Hdisj. pose ( H := Hdisj uh s a).
            apply H.
            - simpl. split;[ left; reflexivity | right;assumption].
            - split; assumption.
          } subst. reflexivity.
         }
      * { apply IHufs'.
        - apply DisjntInvar_tail in Hdisj. assumption.
        - destruct H1. split.
          + apply set_mem_complete1 in case1. unfold not in case1. simpl in H, case1.
            destruct H.
            * subst. contradiction.
            * assumption.
          + assumption. }
Qed.

Theorem uf_find_none_sound_complete : forall a ufs,
  uf_find a ufs = None <-> forall s, ~(set_In s ufs /\ set_In a s).
Proof.
  intros a ufs. split.
  - unfold not. intros H1 s H2. induction ufs as [|uh ufs' IHufs'].
    + destruct H2. contradiction.
    + simpl in *. case (set_mem term_eq_dec a uh) eqn:case1.
      * inversion H1.
      * { apply IHufs'.
        - assumption.
        - destruct H2. split.
          + destruct H.
            * subst. apply set_mem_complete1 in case1. contradiction.
            * assumption.
          + assumption. }
- intros H. unfold not in H. induction ufs as [|uh ufs' IHufs'].
  + reflexivity.
  + simpl. case (set_mem term_eq_dec a uh) eqn:case1.
    * exfalso. apply set_mem_correct1 in case1. apply (H uh).
      split; [ simpl; left; reflexivity | assumption ].
    * { apply IHufs'. intros s H1. simpl set_In in *.
        apply (H s).  destruct H1. split; try (right); assumption. }
Qed.

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
(* Dep types to assert x & y occur in some class? *) (* merge needs "proof l a b" *)
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

(* Theorem uf_merge_inv : forall l ufs a b, set_In (a,b) l  /\ EqInvar l ufs -> EqInvar l (uf_merge ufs a b).
Proof.
  intros. unfold EqInvar in *. intros. destruct H, H1.
(*   assert(exists Ca, set_In a Ca /\ set_In Ca ufs). admit. *)
(*   assert(exists Cb, set_In b Cb /\ set_In Cb ufs). admit. *)
(*   destruct H4 as [Ca], H5 as [Cb]. pose (U := set_union term_eq_dec Ca Cb). *)
  unfold uf_merge in H0. case (uf_find a ufs) eqn:case1, (uf_find b ufs) eqn:case2. 
Abort. *)

(* Theorem uf_merge_EqInvar : forall l ufs a b,
  EqInvar l ufs -> set_In (a,b) l -> EqInvar l (uf_merge ufs a b).
Proof.
  intros l ufs a b H1 H2. unfold EqInvar in *. intros c H3 x y H4.
  unfold uf_merge in H3. 
  case (uf_find a ufs) eqn:case1, (uf_find b ufs) eqn:case2;
  try (apply (H1 c); assumption).
  assert (HA : set_In a s). admit. assert (HB : set_In b s0). admit.
  (* Show that removing things from ufs maintains invariant. *)
  (* Then show adding union maintains invariant. *)
  remember (set_setterm_add (set_union term_eq_dec s s0)
          (set_remove setterm_eq_dec s0 (set_remove setterm_eq_dec s ufs))) as newUfs.
  assert (T : EqInvar l newUfs).
  {
    admit.
  }
  unfold EqInvar in T. apply (T c). assumption.
Abort. *)

About set_remove. (*Always use About instead of Check for lib stuff, gives lots of useful info; like which args are implicit and whether definition is transparent/opaque. *)
Lemma set_remove_notin_same : forall (A:Type) (a:A) (s:set A) Aeq, 
  ~ set_In a s -> set_remove Aeq a s = s.
Proof.
  intros A a s Aeq Hnotin. induction s as [| hs s' IHs'].
  - simpl. unfold empty_set. reflexivity.
  - unfold not in *. unfold set_In in *. simpl in *. case (Aeq a hs) eqn:case1.
    + exfalso. apply Hnotin. subst. left. reflexivity.
    + apply f_equal. (* f_equal removes constructor from both sides. *)
      apply IHs'. intros. apply Hnotin. right. assumption.
Qed.

Lemma EqInvar_tail : forall l hu u, EqInvar l (hu::u) -> EqInvar l u.
Proof.
  intros l hu u H1. unfold EqInvar in *. intros c H2 a b H3. 
  apply (H1 c);try (simpl; right); assumption.
Qed.

Lemma EqInvar_splits : forall l l1 l2, 
  EqInvar l (l1++l2) <-> EqInvar l l1 /\ EqInvar l l2.
Proof.
  intros l l1 l2. split.
  { intros H. unfold EqInvar in H. unfold set_In in H. 
    Search ( In _ _ <-> In _ _ \/ In _ _ ).
    split; unfold EqInvar; intros c H1 a b H2; apply (H c); try apply in_app_iff;
    [ left | assumption | right | assumption ]; try assumption.
  }
  { intros [H1 H2]. unfold EqInvar. intros c H3 a b H4. unfold set_In in *.
    unfold EqInvar in *. Search (In _ ( _ ++ _ )). apply in_app_iff in H3.
    destruct H3; [ apply (H1 c) | apply (H2 c) ]; assumption.
  }
Qed.

Lemma NoDup_tail : forall {A:Type} (h:A) l, NoDup (h::l) -> NoDup l.
Proof.
  intros. destruct (NoDup_cons_iff h l) as [H' _].
  apply H' in H. destruct H. assumption.
Qed.

Lemma set_remove_split : forall (A:Type) (a:A) l1 l2 Aeq, 
  NoDup (l1 ++ a::l2) -> set_remove Aeq a (l1 ++ a::l2) = l1 ++ l2.
Proof.
  intros A a l1 l2 Aeq Hnodup. induction l1 as [|hl1 l1' IHl1'].
  - simpl. case (Aeq a a) eqn:case1; try reflexivity. contradiction.
  -  simpl. case (Aeq a hl1) eqn:case1.
    + exfalso. (* Contradiction in Hnodup *) simpl in Hnodup.
      rewrite <- e in Hnodup. Search (NoDup _ -> _ ). Search "NoDup_remove".
      pose (T := NoDup_remove (a::l1') l2 a).
      apply T in Hnodup. destruct Hnodup as [_ Hnotin].
      Search ((_::_++_)). apply Hnotin. simpl. left. reflexivity.
    + apply f_equal. apply IHl1'. simpl in Hnodup. Search (NoDup ( _ :: _)).
      destruct (NoDup_cons_iff hl1 (l1' ++ a::l2)) as [T _]. 
      apply T in Hnodup. destruct Hnodup. assumption.
Qed.

Lemma set_remove_notin : forall (A:Type) (a b:A) (s:set A) Aeq,
  NoDup s -> ~ set_In a s -> a <> b -> ~ set_In a (set_remove Aeq b s).
Proof. (* Could've used set_remove_notin_same to prove this. *)
  intros A a b s Aeq Hnodup Hnotin Hineq. unfold not in *. intros Hn.
  induction s as [|hs s' IHs'].
  - simpl in *. contradiction.
  - apply IHs'. unfold set_In in *. simpl in *.
    + apply (NoDup_tail hs s'). assumption.
    + intros H. apply Hnotin. right. assumption.
    + clear IHs'. unfold set_In in *. Search (set_remove _ _ (_::_)).
      Search set_remove. About set_remove_iff.
      destruct (set_remove_iff Aeq a b Hnodup) as [T _]. apply T in Hn.
      destruct Hn as [Hn _]. contradiction.
Qed.

Lemma setterm_ineq_refl : forall (a b: set term), a <> b <-> b <> a.
Proof.
  intros. split; intros; unfold not in *; intros; symmetry in H0; contradiction.
Qed.

Check set_In_dec setterm_eq_dec. 
(* Show DisjntInvar is preserved. Rename to set_remove_invariant. *)
Lemma set_remove_invariant : forall l (c:set term) (s: set (set term)),
  NoDup s /\ EqInvar l s /\ DisjntInvar s -> 
    NoDup (set_remove setterm_eq_dec c s) /\ 
      EqInvar l (set_remove setterm_eq_dec c s) /\
        DisjntInvar (set_remove setterm_eq_dec c s).
Proof.
  intros l c s [Hnodup [HEq HDisj]]. split; try split.
  - clear HEq. (* Derive Nodup new from Hnodup *)
    induction s as [|hs s' IHs'].
    * simpl. unfold empty_set. constructor.
    * { simpl. case (setterm_eq_dec c hs) eqn:case1.
      - Search (NoDup (_ :: _)). destruct (NoDup_cons_iff hs s') as [T _].
        apply T in Hnodup. destruct Hnodup. assumption.
      - Search (NoDup (_ :: _)). 
(*         destruct (NoDup_cons_iff c s') as [Hnd1 Hnd2]. *)
        destruct (NoDup_cons_iff hs s') as [Hnd1 _]. assert (Hnodup' := Hnodup).
        apply Hnd1 in Hnodup'. destruct Hnodup' as [Hnd'1 Hnd]. apply IHs' in Hnd.
        
        Search (NoDup (_::_)). 
        destruct (NoDup_cons_iff hs (set_remove setterm_eq_dec c s')) as [_ T].
        apply T. split; try assumption.
        + (* Show that "hs not in s" -> "hs not in set_remove whatever s" *)
          Check set_remove_notin (set term) hs c s'.
          apply (NoDup_tail hs s') in Hnodup.
          apply (set_remove_notin (set term) hs c s'); try assumption.
          (* FML *) 
          apply setterm_ineq_refl. assumption.
        + apply DisjntInvar_tail in HDisj. assumption.
      }
    - case (set_In_dec setterm_eq_dec c s).
      + intros Hin. unfold set_In in *. Search ( In _ _ -> exists _, _).
        assert (Hin1 := Hin). apply in_split in Hin1. destruct Hin1 as [l1 [l2 H]].
        assert (R : set_remove setterm_eq_dec c s = l1 ++ l2 ).
        { (* Wouldn't this need NoDup? Or is it enough to additionally assert 
          that "~set_In c l1"? Let's see...guess it does. *)
         rewrite H in *. apply (set_remove_split (set term) c l1 l2); 
         try reflexivity; assumption.
        }
        setoid_rewrite R.
        rewrite H in HEq. apply EqInvar_splits in HEq. destruct HEq as [H1 H2].
        apply EqInvar_tail in H2. destruct (EqInvar_splits l l1 l2) as [_ lemma].
        apply lemma. split; assumption.
      + (* Show list is unchanged *)
        intros Hnotin. Search set_remove.
        apply (set_remove_notin_same (set term) _ _ setterm_eq_dec) in Hnotin.
        try rewrite Hnotin. (* doesn't work! WTF!? *)
        (* Forgot that Eqinvar is a predicate with quantifs *)
        setoid_rewrite Hnotin. assumption.
  - unfold DisjntInvar in *. intros c1 c2 x H1 H2.
    apply (HDisj c1 c2 x).
    + case (setterm_eq_dec c1 c) eqn:case1, (setterm_eq_dec c2 c) eqn:case2;
      (* Solve 1st 2 cases. *) (* Search set_remove. About set_remove_2. *)
      try ( subst; destruct H1 as [H1 _];
     apply (set_remove_2 setterm_eq_dec Hnodup) in H1; contradiction H1;
     reflexivity ).
      * subst. destruct H1 as [_ H1]. Search set_remove. About set_remove_2.
         apply (set_remove_2 setterm_eq_dec Hnodup) in H1. contradiction H1.
         reflexivity.
      * clear case1 case2. unfold set_In in *. Search set_remove. 
        destruct H1 as [H1l H1r]. split; 
        [ apply (set_remove_1 setterm_eq_dec c1 c s) | 
          apply (set_remove_1 setterm_eq_dec c2 c s) ]; assumption.
    + assumption.
Qed.

Lemma set_remove_removes_terms : forall ufs (crem: set term) t,
  NoDup ufs -> DisjntInvar ufs -> In t crem ->
    forall c, ~( In t c /\ In c (set_remove setterm_eq_dec crem ufs)).
Proof.
  intros ufs crem t Hnodup HDisj Hin c. unfold not. intros H.
  destruct H as [H1 H2].
  (* Show c <> crem *) Search set_remove. About set_remove_2.
  apply (set_remove_2 setterm_eq_dec) in H2.
  (* This lemma not required. *)
Abort.

Lemma set_union_make_class : forall l (ufs :set (set term)) a b ca cb union,
  NoDup ufs /\ EqInvar l ufs /\ DisjntInvar ufs ->
    In ca ufs /\ In a ca -> 
      In cb ufs /\ In b cb ->
        proof l a b ->
          union = set_union term_eq_dec ca cb->
            forall x y, In x union /\ In y union -> proof l x y.
Proof.
  intros l ufs a b ca cb union [Hnodup [HEq Hdisj]] Hca Hcb Hprf H x y Hin.
  Search set_union. destruct Hin as [Hxin Hyin]. About set_union_iff.
  destruct (set_union_iff term_eq_dec x ca cb) as [Tx _].
  rewrite H in *. apply Tx in Hxin.
  destruct (set_union_iff term_eq_dec y ca cb) as [Ty _]. apply Ty in Hyin.
  clear Tx Ty.
  destruct Hxin as [Hxin | Hxin], Hyin as [Hyin | Hyin]; unfold set_In in *.
  - unfold EqInvar in HEq. apply (HEq ca); [ destruct Hca | split ]; assumption.
  - assert (Tab : proof l x a /\ proof l y b).
    { destruct Hca as [HcaUfs Hcaa], Hcb as [HcbUfs Hcbb].
      split; [ apply (HEq ca) | apply (HEq cb)]; unfold set_In; try split; assumption.
    }
    assert (T : proof l a y).
    { destruct Tab as [_ Tb]. apply (proofTrans l a b y); try assumption;
      apply proofSymm; assumption.
    }
    apply (proofTrans l x a y); destruct Tab; assumption.
  - assert (Tab : proof l y a /\ proof l x b).
    { destruct Hca, Hcb. split; [apply (HEq ca) | apply (HEq cb)];
      unfold set_In; try split; assumption.
    }
    destruct Tab as [Ta Tb]. apply proofSymm in Ta.
    assert ( T : proof l x a).
    { apply proofSymm in Hprf. apply (proofTrans l x b a); assumption.
    }
    apply (proofTrans l x a y); assumption.
  - unfold EqInvar in HEq. apply (HEq cb); [ destruct Hcb | split ]; assumption.
Qed.

Lemma set_add_Eq_Disjnt : forall l (union: set term) ufs,
  EqInvar l ufs -> DisjntInvar ufs -> 
      (forall x y, In x union /\ In y union -> proof l x y) -> (* union is an Eq Class *)
        (forall a ca, ~(In a union /\ In a ca /\ In ca ufs)) ->
          EqInvar l (set_add setterm_eq_dec union ufs) /\ 
            DisjntInvar (set_add setterm_eq_dec union ufs).
Proof.
  intros l union ufs HEq HDisj Hunion H.
  split; [unfold EqInvar | unfold DisjntInvar]; unfold set_In.
  - intros c Hinc a' b' Hinab. About set_add_iff.
    apply set_add_iff in Hinc. destruct Hinc.
    + subst. apply Hunion. assumption.
    + apply (HEq c); assumption.
  - intros c1 c2 x Hinc Hinx. unfold DisjntInvar in HDisj. unfold set_In in *.
    destruct Hinc as [Hincl Hincr].
    apply set_add_iff in Hincl; apply set_add_iff in Hincr. destruct Hincl, Hincr.
    + subst. reflexivity.
    + apply (HDisj c1 c2 x); try assumption. split; try assumption.
      subst. exfalso. (* goal is clearly false. *) 
      apply (H x c2). destruct Hinx; split; try split; assumption.
    + apply (HDisj c1 c2 x); try assumption. split; try assumption.
      subst. exfalso. apply (H x c1). destruct Hinx; split; try split; assumption.
    + apply (HDisj c1 c2 x); try assumption. split; assumption.
Qed.

Theorem uf_merge_invariant : forall a b l ufs newUfs, 
  set_In (a,b) l  -> NoDup ufs -> EqInvar l ufs -> DisjntInvar ufs ->
    newUfs = uf_merge ufs a b -> 
      NoDup newUfs /\ EqInvar l newUfs /\ DisjntInvar newUfs.
Proof.
  intros a b l ufs newUfs Hprf Hnodup HEq HDisj H4.
  unfold uf_merge in H4.
  case (uf_find a ufs) eqn:case1, (uf_find b ufs) eqn:case2;
  try (subst; exact (conj Hnodup (conj HEq HDisj))).
  (* Solves 3 subgoals where "newUfs = ufs" *)
  - assert (HA : set_In s ufs /\ set_In a s).
    { pose (T := uf_find_some_sound_complete a s ufs).
      apply T in HDisj. destruct HDisj as [HDisj _]. apply HDisj in case1.
      assumption. }
    assert (HB : set_In s0 ufs /\ set_In b s0).
    { pose (T := uf_find_some_sound_complete b s0 ufs).
      apply T in HDisj. destruct HDisj as [HDisj _]. apply HDisj in case2.
      assumption. }
    clear case1 case2. rename s into ca, s0 into cb.
      (* Show that removing things from ufs maintains invariant. *)
    (* Then show adding union maintains invariant. *)
    remember (set_remove setterm_eq_dec ca ufs) as I1.
    remember (set_remove setterm_eq_dec cb I1) as I2.
    assert (T1 : NoDup I1 /\ EqInvar l I1 /\ DisjntInvar I1).
    { rewrite HeqI1. split; try split;
      apply (set_remove_invariant l ca ufs (conj Hnodup (conj HEq HDisj))). }
    assert (T2 : NoDup I2 /\ EqInvar l I2 /\ DisjntInvar I2).
    { rewrite HeqI2. Check set_remove_invariant l cb I1.
      apply (set_remove_invariant l cb I1 T1). }
    unfold set_setterm_add in *. unfold set_In in *.
    remember (set_union term_eq_dec ca cb) as union.
    assert (forall x' y', In x' union /\ In y' union -> proof l x' y').
    { apply proofAxm in Hprf. Check set_union_make_class.
      apply (set_union_make_class l ufs a b ca cb union (conj Hnodup (conj HEq HDisj)) HA HB Hprf Hequnion).
    }
    
    assert (HnotinI2 : forall z c, ~(In z union /\ In z c /\ In c I2)).
    { (* First show same for I1? Not true. *)
      unfold not. intros z c [Hunion [HclassL HclassR]]. rewrite Hequnion in Hunion. 
      apply set_union_iff in Hunion. destruct Hunion as [HunL | HunR].
      - Search set_remove. rewrite HeqI2 in HclassR. About set_remove_1.
        apply (set_remove_1 setterm_eq_dec c cb I1) in HclassR. 
        rewrite HeqI1 in HclassR.
        (* Let's show ca = c *) 
        assert (A1: ca = c).
        { apply (set_remove_1 setterm_eq_dec c ca ufs) in HclassR.
          apply (HDisj ca c z); split; try destruct HA; assumption. }
        (* Now derive contradiction to A1 *)
        About set_remove_2. 
        apply (set_remove_2 setterm_eq_dec) in HclassR; try assumption.
        symmetry in A1. contradiction.
      - rewrite HeqI2 in HclassR.
        assert (A2: c = cb).
        { apply (set_remove_1 setterm_eq_dec c cb I1) in HclassR.
          rewrite HeqI1 in HclassR.
          apply (set_remove_1 setterm_eq_dec c ca ufs) in HclassR.
          apply (HDisj c cb z); split; try destruct HB; assumption. }
        (* Show c <> cb *)
        About set_remove_2. destruct T1 as [T1nodup T1rest].
        apply (set_remove_2 setterm_eq_dec T1nodup) in HclassR.
        contradiction.
    }
    
    split.
    + (* Show NoDup is preserved by all set operations. *)
      rewrite H4. Search set_add. apply (set_add_nodup setterm_eq_dec).
      destruct T2 as [T2nodup T2rest]; assumption.
    + rewrite H4. destruct T2 as [T2nodup [T2Eq T2Disj]].
      apply (set_add_Eq_Disjnt l union I2 T2Eq T2Disj H HnotinI2).
Qed.

(* This is actually do_tc, as it only does transitive closure for now *)
Fixpoint do_cc (l : set (term*term)) (ufs : set (set term)) :=
  match l with
  | nil => ufs
  | (t1, t2)::l' => do_cc l' (uf_merge ufs t1 t2)
  end.

Compute do_cc [(var 1, var 2); (var 1, var 3); (var 3,var 4)] (create_ufs [(var 1, var 2); (var 1, var 3); (var 3,var 4)]).

(* Lemma EqInvar_emp : forall a l, ~ EqInvar (a::l) [].  ??? *)

Lemma uf_merge_emp : forall a b, uf_merge [] a b = [].
Proof. intros. unfold uf_merge. simpl. reflexivity. Defined.

Lemma do_cc_emp : forall l, do_cc l [] = [].
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. destruct a. rewrite uf_merge_emp. assumption.
Defined.

Lemma EqInvar_monotonic: forall x y l ufs, EqInvar l ufs -> EqInvar ((x,y)::l) ufs.
Proof.
  intros. unfold EqInvar in *. intros.
  assert(T: proof l a b).  (* Dependency on definition of proof!! *)
  { pose (H c H0 a b H1). assumption. }
  apply proof_monotonic. assumption.
Qed.

Lemma EqInvar_noclass_equiv: forall x y l ufs,
  uf_find x ufs = None \/ uf_find y ufs = None ->
    EqInvar ((x,y)::l) ufs <-> EqInvar l ufs.
Proof.
  intros x y l ufs Hnotin. split.
  - intros HEq. Search uf_find. 
    unfold EqInvar; unfold set_In in *. 
    intros c Hinc a b [Hina Hinb]. 
(*     unfold EqInvar in HEq; unfold set_In in HEq. *)
    assert(H: proof ((x, y) :: l) a b). 
    { unfold EqInvar in HEq. apply (HEq c); [assumption | split; assumption]. }
    induction H. (* Dependency on definition of proof!! *)
    + unfold set_In in H; simpl in H. destruct H.
      * symmetry in H. inversion H. subst. exfalso. 
        destruct Hnotin as [Hnotinx | Hnotiny].
        { destruct (uf_find_none_sound_complete x ufs) as [Tx _].
          pose (Hx := Tx Hnotinx). apply (Hx c). split; assumption. }
        { destruct (uf_find_none_sound_complete y ufs) as [Ty _].
          pose (Hy := Ty Hnotiny). apply (Hy c). split; assumption. }
      * apply proofAxm; assumption.
    + apply proofRefl.
    + apply proofSymm. apply IHproof; assumption.
    + destruct Hnotin as [Hnotinx | Hnotiny]. 
      * { destruct (uf_find_none_sound_complete x ufs) as [Tx _]. unfold set_In in *.
        assert (HP: proof ((x, y) :: l) s u). 
(*         { unfold EqInvar in HEq. apply (HEq c); [assumption | split; assumption]. } *)
        { About proofTrans. apply (proofTrans ((x,y)::l) s t u); assumption. }
        (* Need 'proof l u c' or goal directly. Show 'uf_find x ufs = None -> EqInvar (x,y)::l ufs'? *)
          admit.
        }
      * admit.
  - apply EqInvar_monotonic.
Admitted.

Theorem do_cc_invariant : forall l ufs newUfs, 
  NoDup ufs /\ EqInvar l ufs /\ DisjntInvar ufs ->
    newUfs = do_cc l ufs -> 
      NoDup newUfs /\ EqInvar l newUfs /\ DisjntInvar newUfs.
Proof.
  intros l ufs newUfs. induction l as [| hl l' IHl'].
  - intros [Hnodup [HEq HDisj]] Hnew. simpl in *. subst. split; try split; assumption.
  - intros [Hnodup [HEq HDisj]] Hnew. simpl in Hnew. 
    destruct hl as [hl1 hl2]. 
    (* Inductive hyp only useful(?) if hl1 and hl2 are in same class, 
       else newUfs = ufs; and we need inductive properties of EqInvar. *)
    unfold uf_merge in Hnew. 
    case (uf_find hl1 ufs) eqn:case1, (uf_find hl2 ufs) eqn:case2;
    try rename s into chl1, s0 into chl2.
    + admit.
    (* Need EqInvar_noclass_equiv for the other 3 cases. *)
    (* Missing out on the fact that during do_cc, uf_find will never return none.
        Add this to thm statement and we can dispose off the 3 cases. *)
    + admit.
    + admit.
    + Print EqInvar.
Admitted.

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

Lemma create_ufs_no_emp: forall l, ~ set_In (create_ufs l) [].
Proof.
 unfold not. intros l Hin. simpl in Hin. assumption.
Qed.

Lemma emp_no_proof: forall a b, a <> b -> ~(proof [] a b).
Proof.
  unfold not. intros a b H Hprf. 
  induction Hprf; simpl in *;try assumption.
  - apply H; reflexivity. 
  - apply IHHprf. intros. subst. apply H. reflexivity.
  - apply IHHprf1. intros. subst. apply IHHprf2. intros. subst. apply H. reflexivity.
Qed.

Lemma create_ufs_invariant: forall l,
  NoDup (create_ufs l) /\ EqInvar l (create_ufs l) /\ DisjntInvar (create_ufs l).
Proof. Admitted.

Theorem cc_algo_sound_complete: forall l t1 t2,
 cc_algo l t1 t2 = true <-> proof l t1 t2.
Proof.
  intros. split.
(*   1:{ intros Ht. unfold cc_algo in Ht. remember (create_ufs l) as iufs.
  induction iufs as [|ih iufs' IHiu].
    - induction l as [|h l' IHl'].
      + simpl in *. apply diff_false_true in Ht; exfalso; assumption.
      + admit.
    -
      
  1:{
  intros Hcc. unfold cc_algo in Hcc. remember (create_ufs l) as iufs.
  remember (uf_find t1 (do_cc l iufs)) as T1. remember (uf_find t2 (do_cc l iufs)) as T2.
  destruct T1 as [r1|]; destruct T2 as [r2|]; try (apply diff_false_true in Hcc; exfalso; assumption).
  - Search "setterm_eq_dec". admit.
  
  (* Alt 1 *)
    induction r1,r2; try (apply diff_false_true in Hcc; exfalso; assumption).
    + simpl in *. clear Hcc. admit. (* See note in orig *)
    + admit.
  
  (* Orig *)
    case r1 eqn:Er1, r2 eqn: Er2; simpl in *; try (apply diff_false_true in Hcc; exfalso; assumption).
    + clear Hcc. (* contradict HeqT1 or HeqT2.
     Since, create_ufs does not add [] to ufs; do_cc preserves that. *)
      admit.
    + rewrite <- Er1 in *. rewrite <- Er2 in *.
  } *)

  2:{ induction l as [| h l' IHl'].
    - intros. (*Show forall a b: ~ H *) destruct H.
      + simpl in H. exfalso. assumption.
      + unfold cc_algo. simpl. 
    - intros Hprf. induction Hprf.
      + unfold set_In in H. simpl in H. destruct H as [Hl| Hr].
        * { subst. unfold cc_algo. remember (create_ufs ((s,t)::l')) as iufs. 
          remember (do_cc ((s,t)::l') iufs) as newUfs.
          assert(T: NoDup newUfs /\ EqInvar ((s,t)::l') newUfs /\ DisjntInvar newUfs). admit.
          case (uf_find s newUfs) as [rs|] eqn:cases, (uf_find t newUfs) as [rt|] eqn:caset.
          - admit.
          - apply (uf_find_some_sound_complete s rs newUfs) in cases;
            destruct T as [TDup [TEq TDisj]]; try assumption.
            (* Need completeness of do_cc. Stated how exactly? *)
            (* Need proof l' s t -> do_cc ((s,t)::l') *)
      
      
  
  
  2:{ intros Hprf. induction Hprf.
    - unfold set_In in *. 
      induction l as [|h l' IHl']; try contradiction.
      unfold cc_algo. remember (create_ufs (h::l')) as iufs. 
      remember (do_cc (h::l') iufs) as newUfs.
      assert(T: NoDup newUfs /\ EqInvar (h::l') newUfs /\ DisjntInvar newUfs). admit.
      simpl In in H. destruct H as [Hl | Hr].
      + case (uf_find s newUfs) as [rs|] eqn:cases, (uf_find t newUfs) as [rt|] eqn:caset.
        * admit.
        * exfalso. rewrite Hl in *. 
(*           assert(HEq: proof ((s,t)::l') s t). 
          { apply proofAxm. simpl. left. reflexivity. } *)
          destruct T as [TDup [TEq TDisj]].
          (* Derive contradiction from TEq and case eqn correctness. Wait..how???*)
          Search "uf_find_some_sound_complete".
          apply (uf_find_some_sound_complete s rs newUfs) in cases; try assumption.
          Search "uf_find_none_sound_complete".
          pose (P := uf_find_none_sound_complete t newUfs). destruct P as [P' _].
          pose (P := P' caset).
          unfold EqInvar in TEq. 

Admitted.