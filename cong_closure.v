Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Require Import Coq.Program.Wf.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Inductive term : Set :=
| var : nat -> term.
(* | fn  : nat -> term -> term. *)

(* Check fn 1 (fn 1 (var 2)). *)

Inductive form : Set :=
| eq : term -> term -> form.

(* The correctness condition *)
Inductive prf (l : list (term * term)) : term -> term -> Prop  :=
  | paxm : forall s t, In (s, t) l -> prf l s t
  | pref : forall t, prf l t t
  | psym : forall s t, prf l s t -> prf l t s
  | ptrs : forall s t u, prf l s t -> prf l t u -> prf l s u.


Check paxm [(var 2, var 3)] (var 2) (var 3).

Check psym [] (var 2) ( var 2) (pref [] (var 2) ).

Check prf.

(* computes all the subterms of a given term. *)
(* Fixpoint subterms (t : term) : list term :=
  match t with
  | var n => [var n]
  | fn n t1 => (fn n t1) :: subterms t1
  end. *)
Definition subterms (t:term) := 
  match t with
    | var n => [var n]
  end.

Print Nat.eq_dec.

(* give list of tuples of term and its parent *)
Check beq_nat. (* Importes from EqNat *)

(* Scheme Equality for term. (* screw these defs. *) *)
(* Check term_beq. *)
(* Check term_eq_dec. *)
(* Print term_eq_dec. *)

(* Define own term equality and nodup boolean version. *)
(* Reset term_beq. (* Use IDE navigation?? *) *)
Definition term_beq (a b : term) := 
  match a, b with
  | var n1, var n2 => beq_nat n1 n2
  end.

Check term_beq.
Compute term_beq (var 3) (var 4).
Check nodup.
Check in_dec.

(* Define own nodup which works with (term->term->bool) *)
Fixpoint skip {A:Type}  (f : A -> A -> bool) (e : A) (l : list A) : list A :=
  match l with
  | [] => []
  | x::xs => if f e x then skip f e xs else x :: skip f e xs
  end.

Compute length [].
Lemma skip_nonincr : forall (A:Type) (f:A->A->bool) (e:A) (l:list A) , length (skip f e l) <= length l.
Proof.
  intros. induction l as [ | h l' IHl].
  + reflexivity.
  + simpl. case (f e h) eqn:val.
    2:{
      simpl. Search (_ <= _ -> S _ <= S _).
      apply le_n_S, IHl. 
      }
    1:{
      simpl. Print le. apply le_S. trivial.
      }
Qed.
(* Program Fixpoint nodupb {A:Type} (f: A -> A -> bool) (l :list A) {wf show skip is nonincreasing} : list A :=
  match l with
  | [] => []
  | x::xs => x :: nodupb f (skip f x xs)
  end. *)
Print In.

(* Fixpoint rem_el (f: A -> A -> bool) (a : A) (l : list A) := *)

Fixpoint check {A:Type} (f : A -> A -> bool) (x : A)  (acc : list A) :=
  match acc with
  | [] => false
  | y::ys => if (f x y) then true else check f x ys
  end.

Fixpoint nodup_new {A:Type} (f: A -> A -> bool) (l : list A) (acc : list A) : list A :=
 match l with
 |  [] => acc
 |  x::xs => if (check f x acc) then nodup_new f xs acc else nodup_new f xs (x::acc)
 end.


Search "nodup".

Theorem nodup_nodup: forall (l tail: list term) (a x: term),
    nodup_new (term_beq) l [] = a :: tail -> ~ In  a tail.
Proof.
  intros.
  induction l.
  + simpl in H. inversion H.
  + simpl in H. 
    
                                                       

(* Example check : term_eq_dec (var 3) (var 3). ??? *)
(* Proof.
Admitted. *)

(* Eval compute in term_eq_dec (var 2) (fn 1 (var 3)). *)
(* Eval compute in term_beq (var 2) (var 3). *)
(* Eval compute in if (term_beq (var 2) (var 2)) then 1 else 0. *)

Notation "x -=- y" := (term_beq x y)
                        (at level 60).

(* Scheme Equality for term*term. *)
Definition term_pairs_eqb (u v : term * term) :=
  match (u, v) with
  | ((a, b), (c, d)) => andb  (term_beq a c) (term_beq b d)
  end.

Compute skip term_pairs_eqb (var 3, var 4) [(var 3, var 5); (var 3, var 4); (var 1, var 3)].

(* Compute nodupb term_pairs_eqb [(var 3, var 5); (var 3, var 4); (var 1, var 3); (var 3, var 4)]. *)

Search "nodup".

Fixpoint uf_find (l : list (term*term)) (t : term) :=
  match l with
  | [] => t (*  *)
  | (x, y) :: ls => if term_beq x t then y
                    else
                      uf_find ls t
  end.


(* Fixpoint uf_find1 (l : list (term*term)) (t : term) := *)
(*   match l with *)
(*   | [] => var (1000) *)
(*   | (t, y) :: ls => y *)
(*   | _ :: ls            =>  uf_find ls t *)
(*   end. *)


Fixpoint change_rep (l : list (term * term)) (a b : term) :=
  if term_beq a b then l else
    match l with
    | [] => []
    | (x, n) :: xs => if term_beq n a then (x, b) :: change_rep xs a b
                      else
                        (x, n) :: change_rep xs a b
    end.


Definition uf_merge (l : list (term*term)) (u v : term) :=
  let a := uf_find l u in
  let b := uf_find l v in
  change_rep l a b.


Fixpoint do_cc (work ufl : list (term*term)) (bound : nat) :=
  match bound with
  | 0 => ufl
  | _ => match work with
         | [] => ufl
         | (t1, t2) :: ws => ufl end
  end.

Fixpoint do_cc1 (work ufl : list (term*term)) :=
  match work with
  | [] => ufl
  | (t1, t2) :: ws => do_cc1 ws (uf_merge ufl t1 t2)
  end.

Definition wfl' l ufl := forall c d, term_beq (uf_find ufl c) (uf_find ufl
                                                                       d) =
                                     true -> prf l c d.

Theorem main_one' : forall l ufl, (wfl' l ufl) -> wfl' l (do_cc1 l ufl).
Proof.
  intros.
  induction l.
  simpl.
  assumption.

  destruct a.
  simpl.

  unfold wfl' in H, IHl. unfold wfl'. intros.
  case (uf_find ufl c -=- uf_find ufl d) eqn: lets_try.
  apply H in lets_try. assumption.
  Admitted.

  

Definition wfl l ufl := forall c d, uf_find ufl c = d -> prf l c d.

Theorem main_one : forall l ufl, (wfl l ufl) -> wfl l (do_cc1 l ufl).
Proof.
  intros.
  (* unfold wfl. *)
  (* unfold wfl in H. *)
  (* intros. *)
  (* inversion in H0. *)
  (* inversion. *)
  
  (* induction l. *)
  unfold wfl in *.
  simpl.
 Admitted.

(*   (* unfold wfl. *) *)
(*   (* unfold wfl in H, IHl. *) *)
(*   destruct a. *)
(*   simpl. *)
(*   unfold wfl. unfold wfl in H, IHl. *)
(*   intros. *)
(*   pose (new1 := ((H t) (uf_find ufl t))). *)
(*   assert (uf_find ufl t = uf_find ufl t). *)
(*   reflexivity. *)
(*   pose (shit := (new1 H1)). *)

(*   pose (new2 := ((H t0) (uf_find ufl t0))). *)
(*   assert (uf_find ufl t0 = uf_find ufl t0). *)
(*   reflexivity. *)
(*   pose (shit1 := (new2 H2)). *)

  
(*   (* unfold do_cc1 in H0. *) *)
(*   (* case (uf_find ufl c) eqn: bagbose. *) *)
(*   (* case (d) eqn: mad. *) *)
(*   (* (* unfold wfl in H. *) *) *)
(*   (* unfold wfl. *) *)
(*   (* intros. *) *)
(*   (* unfold wfl in IHl. *) *)
(*   (* unfold uf_merge in H0. *) *)
(*   (* case (uf_find ufl c = d) eqn: something. *) *)
(*   (* unfold wfl. *) *)
  
(*   (* pose (nt := uf_find ufl t1). *) *)
(*   (* Variable xy : uf_find ufl t1. *) *)
(*   (* unfold change_rep. *) *)
  
(*   (* unfold uf_merge. *) *)
(*   (* unfold do_cc1. *) *)
(* admit.   *)

Fixpoint create_uf' (l : list (term*term)) :=
  match l with
  | [] => [] 
  | (t1, t2)::ls => (subterms t1 ++ subterms t2) ++ create_uf' ls
  end.

Print nodup_new.

Definition create_uf l := let res := nodup_new term_beq (create_uf' l) []
                          in map (fun x => (x, x)) res.

Fixpoint cc1_algo (work : list (term*term)) (t1 t2 : term) : bool :=
  (* let ufl := create_uf ((t1, t2)::work) in *)
  let ufl := create_uf (work) in
  let res := do_cc1 work ufl in
  let a  := uf_find res t1 in
  let b  := uf_find res t2 in
  term_beq a b.

Eval compute in cc1_algo [(var 1, var 2); (var 1, var 3); (var 3,var 4)] (var 2) (var 4).

Eval compute in cc1_algo [(var 1, var 2); (var 1, var 3); (var 3,var 4); (var 5, var 6)] (var 3) (var 6).

Search "nat_beq".
Check nodup.

Compute uf_find [(var 3, var 3)] (var 3).

(* Theorem cc1_sound l a b: cc1_algo l a b = true -> prf l a b. *)
(* Proof. *)
(*   intros correct. induction l as [ | hl l' Hl]. *)
(*   + simpl in correct. remember (create_uf [(a, b)]) as ufl. *)

(*     unfold create_uf in Hequfl. simpl in Hequfl. rewrite app_nil_r in Hequfl. *)
(*     destruct a as [ na ]; destruct b as [ nb ]. simpl subterms in Hequfl. *)
(*     simpl app in Hequfl. simpl nodup_new in Hequfl. case (nb =? na) eqn:mast. *)
(*     - simpl in Hequfl. Search (_=?_). *)
(*       apply beq_nat_true in mast. rewrite mast. *)
(*       apply pref. *)
(*     - simpl in Hequfl. Search (_=?_).  *)
(* (*     apply beq_nat_false in mast. Locate "<>". *) *)
(*      rewrite Hequfl in correct. simpl in correct. *)
(* (*      pose (T := beq_nat_false nb na mast). unfold not in T. *) *)
(*      pose ( Q := Nat.eqb_sym na nb). *)
(*      rewrite Q in correct. rewrite <- (beq_nat_refl nb) in correct.  *)
(*      rewrite <- (beq_nat_refl na) in correct. rewrite mast in correct. *)
(*      simpl term_beq in correct. rewrite Q in correct. rewrite mast in correct. *)
(*      discriminate. *)
(*       + case (cc1_algo l' a b) eqn: bose. *)
(*         admit. *)
        
        
        
(* Admitted. *)


Theorem term_beq_refl: forall a, term_beq a a  = true.
Proof.
  intros.
  case (a) eqn: fuck.
  unfold "-=-".
  Locate "=?". Search eqb _ _.
  simpl. apply Nat.eqb_refl.
Qed.

  
Theorem uf_find_refl: forall l a,  uf_find l a -=- uf_find l a = true.
Proof.
  intros.
  apply term_beq_refl.
Qed.

Theorem term_beq_sym: forall  a b,  term_beq a b = true ->
                                    term_beq b a = true.
Proof.
  intros.
  case a eqn: fuck.
  case b eqn: fuck1.
  simpl in H.
  simpl. Search (eqb _ _ = eqb _ _).

  rewrite Nat.eqb_sym. assumption.
Qed.

                

Theorem uf_find_sym: forall l a b, uf_find l a -=- uf_find l b = true
                                   ->  uf_find l b -=- uf_find l a = true.
Proof.
  intros.
  case a eqn: fuck.
  case b eqn: fuck1.
  case l eqn: fuck2.
  apply term_beq_sym. assumption.

  apply term_beq_sym. assumption.
Qed.

Theorem term_beq_trans: forall a b c,  term_beq a b = true ->
                                       term_beq b c = true ->
                                       term_beq a c = true.
Proof.
  intros.
  case a eqn: H1.
  case b eqn: H2.
  case c eqn: H3.
  simpl in *. apply beq_nat_true in H. rewrite H.
  assumption.
 (* Search Nat.eqb. *)
 (*
 apply Nat.beq_nat_eq *)
Qed.

Theorem uf_find_trans: forall l a b c, uf_find l a -=- uf_find l b
                                       = true ->
                                       uf_find l b -=- uf_find l c
                                       = true ->
                                       uf_find l a -=- uf_find l c
                                       = true.
Proof.
  intros.
  case (a) eqn: fuck.
  case (b) eqn: fuck1.
  case (c) eqn: fuck2.
  case (l) eqn: fuck3.
  apply (term_beq_trans (var n) (var n0) (var n1)).
  simpl in *. assumption.
  simpl in *. assumption.
  apply (term_beq_trans (uf_find (p :: l0) (var n))
                        (uf_find (p :: l0) (var n0))
                        (uf_find (p :: l0) (var n1))). assumption.
  assumption.
Qed.


Theorem term_eqb_eq: forall a b, a -=- b = true ->
                                 a = b.
Proof.
  intros.
  case a eqn: fuck.
  case b eqn: fuck1.
  simpl in H. apply Nat.eqb_eq in H. rewrite H. reflexivity.
Qed.
  
  
Theorem uf_implies_in_list: forall l x a, uf_find l x -=- a = true
                                          -> x -=- a = false                                                   -> In (x, a) l.
Proof.
  intros.
  induction l.
  - simpl in H. rewrite H in H0. discriminate.
  - case a0 eqn: fuck.
    simpl in H.
    case (t -=- x) eqn: fuck1.
    simpl. apply term_eqb_eq in fuck1. apply term_eqb_eq in H.
    + rewrite fuck1, H in *. left. reflexivity.
    + right. apply IHl. assumption.
Qed.

Theorem change_rep_eq: forall l x a b, In (x, a) l ->
                                       uf_find l x -=- a = true ->
                                       uf_find (change_rep l a b) x
                                               -=-  b = true.
Proof.
  intros.
  induction l. simpl in H. contradiction. simpl in H.
  (*inversion H. admit.*) destruct H.
  rewrite H. simpl. case (a -=- b) eqn: a_not_b.
  simpl. rewrite (term_beq_refl x). assumption.
  rewrite (term_beq_refl a). simpl. rewrite (term_beq_refl x).
  apply term_beq_refl.

  case a0 eqn: Anaught. simpl. case (a -=- b) eqn: ANB.
  simpl. case (t -=- x) eqn: fuck. simpl in H0.
  rewrite fuck in H0. apply (term_beq_trans t0 a b).
  assumption. assumption.

  simpl in H0. rewrite fuck in H0. apply (term_beq_trans (uf_find l x) a b). assumption. assumption.

  case (t0 -=- a) eqn: fuck. case (t -=- x) eqn: fuck1.
  simpl. rewrite fuck1. apply term_beq_refl.

  simpl. rewrite fuck1. simpl in H0. rewrite fuck1 in H0.
  apply (IHl H H0).

  simpl. case (t -=- x) eqn: fuck1. simpl in H0. rewrite fuck1 in H0.
  rewrite H0 in fuck. discriminate.

  simpl in H0. rewrite fuck1 in H0. apply (IHl H H0).
Qed.


(* Theorem uf_merge_eq': forall l x y a b, In (x, a) l -> *)
(*                                         In (y, a) l -> *)
(*                                         uf_find l x -=- a = true -> *)
(*                                         uf_find (uf_merge l a b) y *)
(*                                                 -=- b = true. *)
(* Proof. *)
(*   intros. *)
(*   induction l. *)
(*   + simpl in H. contradiction. *)
(*   + simpl in H, H0. *)
(*     inversion H. *)
(*     inversion H0. admit.  *)

Definition ufl_wf (l : list (term*term)) := forall x y, In (x, y) l ->
                                                        In (y, y) l.

Definition ufl_wf' (l : list (term*term)) := forall x y, uf_find l x -=- y = true ->
                                                        uf_find l y -=- y = true.

Theorem in_monotonic : forall (l: list (term*term))
                              (x: term) (a: term)
                              (a0: term*term),
    In (x, a) l -> In (x, a) (a0 :: l).
Proof.
  intros.
  simpl.
  right. assumption.
Qed.


Theorem uf_merge_eq': forall l x a b, ufl_wf' l ->
                                      In (x, a) l ->
                                      uf_find l x -=- a = true ->
                                      uf_find (uf_merge l a b) x -=-
                                            uf_find l b
                                      = true.
Proof.
  intros.
  induction l.
  + simpl in H0. contradiction.
  + simpl in H0. destruct H0. unfold uf_merge.
  - rewrite H0. simpl. case (x -=- a) eqn: fuck.
    case (x -=- b) eqn: fuck1. pose (fuck2 := term_beq_refl a).
    rewrite fuck2. simpl. pose (fuck3 := term_beq_refl x).
    rewrite fuck3. assumption.

    case (a -=- uf_find l b) eqn: fuck2.
    simpl. pose (fuck3 := term_beq_refl x). rewrite fuck3.
    assumption.
    *  pose (fuck3 := term_beq_refl a).
       rewrite fuck3. simpl.


    pose (fuck4 := term_beq_refl x). rewrite fuck4.
    apply term_beq_refl.

    * admit.
    
  - unfold uf_merge. apply change_rep_eq.
    pose (fuck5 := (in_monotonic l x a a0 H0)).
    unfold ufl_wf' in H. pose (fuck6 := (H x a H1)).
    apply term_eqb_eq in fuck6. rewrite fuck6.
    assumption.

     unfold ufl_wf' in H. pose (fuck6 := (H x a H1)).
     apply term_eqb_eq in fuck6. rewrite fuck6.
     assumption.
Admitted.     



(* Theorem uf_merge_eq: forall l x a b, In (x, a) l -> *)
(*                                      In (y, b) l -> *)
(*                                      uf_find l x -=- a = true -> *)
(*                                      uf_find (uf_merge l a b) x -=- *)
(*                                              b *)
(*                                      = true. *)
(* Proof. *)
(*   intros. *)
(*   induction l. *)
(*   + simpl in H. contradiction. *)
(*   + simpl in H. destruct H. unfold uf_merge. *)
(*   case l eqn: H1. *)
(*   case x eqn: H2. *)
(*   case a eqn: H3. *)
(*   case b eqn: H4. *)
(*   simpl in H. rewrite H in *. (*simpl.*) *)
(*   - admit. *)
(*   - admit. *)
(*   - unfold uf_merge. *)
(*     apply change_rep_eq with (l := (a0 :: l) *)
(*                                    (x := x) *)
(*                                    (a := (uf_find (a0 :: l) a)) *)
(*                                    (b := (uf_find (a0 :: l) b))). *)

(*     Abort. *)
  (* unfold uf_merge. *)
  (* simpl. simpl in H. apply beq_nat_true in H. *)
  (* rewrite H. case (n0 =? n1) eqn: doit. admit. simpl in H. simpl. admit. Admitted. *)
                                       

Theorem cc1_mon: forall work x y a b, cc1_algo work a b = true ->
                                      cc1_algo ((x, y) :: work) a b = true.
Proof.
  intros.
  
  induction work.
  
  {simpl. simpl in H. apply term_eqb_eq in H.
   rewrite H. 
   unfold cc1_algo. apply uf_find_refl. }

  { destruct a0. simpl. case x eqn: fuck1.
    case y eqn: fuck2. unfold create_uf. simpl.
    case (n0 =? n) eqn: fuck3. simpl. admit. admit.}
  
  
Admitted.


Theorem cc1_head: forall work a b, cc1_algo ((a, b) :: work) a b = true.
Proof.
  intros.
  simpl.
  case (a) eqn: fuck1.
  case (b) eqn: fuck2. simpl.
  
  
  
Admitted.

Theorem do_cc1_mon: forall work l x y,
    uf_find l x -=- uf_find l y = true ->
    uf_find (do_cc1 work l) x -=-
         uf_find (do_cc1 work l) y
    = true.
Proof.
  intros.
  induction work.
  - simpl. assumption.

  - destruct a. simpl. 
Abort.

Theorem do_cc1_inv: forall work l x y,
    uf_find l x -=- uf_find l y = true ->
    uf_find (do_cc1 work l) x -=- uf_find (do_cc1 work l) y = true.
Proof.
  intros.
  induction work.
  { simpl. assumption. }
  { destruct a. simpl. induction l.
    + simpl. destruct t, t0. unfold uf_merge.
      simpl. case (n =? n0). assumption. assumption.

    + 
  simpl in H. admit.
Abort.

Theorem do_cc1_rewrite: forall work a l,
    do_cc1 (a :: work) l = do_cc1 [a] (do_cc1 work l).
Proof.
  intros. destruct a.
  induction l.
  simpl. unfold uf_merge. simpl. case (t -=- t0).
  

Theorem do_cc1_mon_aux: forall work l x y
  t t0,
    uf_find (do_cc1 work l) x -=-
            uf_find (do_cc1 work l) y
    = true ->

    uf_find (do_cc1 work (uf_merge l t t0))
            x -=- uf_find (do_cc1 work (uf_merge l t t0)) y = true.
Proof.
  intros.
  induction l as [ | a l'].
  { unfold uf_merge. simpl.
    case (t -=- t0). assumption.
    assumption. }

  { destruct a. unfold uf_merge. 
    simpl.  unfold uf_merge. simpl.
  
                                                        
                                  

Theorem cc1_In: forall work a b, In (a, b) work ->
                                 cc1_algo work a b = true.
Proof.
  intros.
  (* unfold cc1_algo. *)
  case (a) eqn: fuck.
  case (b) eqn: fuck1.
  induction work as [ | a0 work']. simpl in H. contradiction.
  case (a0) eqn: fuck3.

  simpl in H. destruct H.
  { rewrite H. apply cc1_head. }
  { apply cc1_mon. apply IHwork'. assumption. }  
Qed.


Theorem cc1_refl: forall work a, cc1_algo work a a = true.
Proof.
  intros.
  case a eqn: fuck.
  case work eqn: fuck2.
  simpl.
  apply Nat.eqb_refl.
  (* apply uf_find_refl. *)

  simpl. apply uf_find_refl.
Qed.


Theorem cc1_sym: forall work a b, cc1_algo work a b = true ->
                                  cc1_algo work b a = true.
Proof.
  intros.
  unfold cc1_algo in *.
  case (a) eqn: fuck.
  case (b) eqn: fuck1.
  case (work) eqn: fuck2.
  apply uf_find_sym. assumption.
  apply uf_find_sym. assumption.
Qed.


Theorem cc1_trans: forall work a b c, cc1_algo work a b = true ->
                                      cc1_algo work b c = true ->
                                      cc1_algo work a c = true.
Proof.
  intros.
  unfold cc1_algo in *.
  case (a) eqn: fuck.
  case (b) eqn: fuck1.
  case (c) eqn: fuck2.
  case (work) eqn: fuck3.
  
  apply (uf_find_trans
           (do_cc1 [] (create_uf [])) (var n)
           (var n0) (var n1)). assumption. assumption.


  apply (uf_find_trans
           (do_cc1 (p :: l) (create_uf (p :: l))) (var n)
           (var n0) (var n1)).
  assumption. assumption.
Qed.


Theorem cc1_complete work a b: prf work a b -> cc1_algo work a b = true.
Proof.
(*   intros proof. inversion proof. *)
(*   + admit. (* In the list case*) *)
(*   + admit. (* case of reflexivity *) *)
(*   +  *)
(*   + *)
  (* Admitted. *)

  intros. induction H.
  + apply cc1_In. assumption. (* case: in the list *)
  + apply cc1_refl. (* case: refl *)
  + apply cc1_sym. assumption. (* case: sym of cc algo *)
  + apply (cc1_trans work s t u). (* case: trans of cc algo *)
    assumption.
    assumption.
Qed.

Fixpoint create_uf' (l : list (term*term)) :=
  match l with
  | [] => [] 
  | (t1, t2)::ls => (subterms t1 ++ subterms t2) ++ create_uf' ls
  end.

Check nodup_new.

Definition create_uf l := let res := nodup_new term_eq_dec  (create_uf' l)
                          in map (fun x => (x, x)) res.

Check fold_left.

Definition create_parents l :=
  let lis := fold_left (fun x y => x ++ y) (map parent_list1 l) []
  in map (fun x => (x, get_parents1 x lis)) l.
                          

Definition cc_algo (l : list (term*term)) (a b : term) :=
  (* do the merging *)
  let res := 1 in
  let t1  := uf_find l a in
  let t2  := uf_find l b in
  term_beq t1 t2.
