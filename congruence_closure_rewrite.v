(* Author: Akshay
 *)
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations. (* Why does Require complain about path? *)

Require Import Coq.Classes.EquivDec.

Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Require Import Coq.Bool.Bool. 

(* term is Type instead of Set so we can use sigma *)
Inductive term : Set :=
  | var : nat -> term
  | fn : nat -> term -> term.

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
  intros a. induction a.
  - simpl; apply nat_beq_refl.
  - simpl. Locate "&&". unfold andb. rewrite IHa, nat_beq_refl. reflexivity.
Qed.

Print beq_nat. Print eqb.
(* Let's just show these two are the same, then we get lemmas for free. *)
Lemma nat_beq_is_beq_nat : forall x y, nat_beq x y = beq_nat x y.
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
  - generalize x as a, y as b.
    induction a as [vx | n vx], b as [vy | m vy].
    + intros. unfold term_beq in H. rewrite nat_beq_is_beq_nat in H. 
      apply beq_nat_true in H. subst. reflexivity.
    + intros. unfold term_beq in H. inversion H.
    + intros. unfold term_beq in H. inversion H.
    + intros. unfold term_beq in H. Search (_ && _ = true -> _).
      apply andb_prop in H. destruct H as [L R]. rewrite nat_beq_is_beq_nat in L.
      apply beq_nat_true in L. subst. apply f_equal. apply IHvx.
      destruct vx, vy; try trivial.
Qed.

Lemma term_pair_beq_reflect : forall x y, reflect (x = y) (term_pair_beq x y).
Proof.
  intros x y. Search reflect. apply iff_reflect. split.
  - intros x_eq_y. subst. destruct y as [y1 y2]. simpl. 
    repeat rewrite term_beq_refl. reflexivity.
  - intros x_beq_y. destruct x as [x1 x2], y as [y1 y2]. simpl in *.
    (* Need to reflect term first. *)
    destruct x1, y1, x2, y2; simpl in *;
    repeat rewrite nat_beq_is_beq_nat in x_beq_y;
    try rewrite (nat_beq_is_beq_nat n1 n2) in x_beq_y.
    case (n =? n0) eqn: case1, (n1 =? n2) eqn: case2; 
    try apply beq_nat_true in case1; try apply beq_nat_false in case2.
    + apply beq_nat_true in case2. subst. reflexivity.
    + subst. discriminate.
    + discriminate.
    + discriminate.
    + case (n =? n0) eqn:case1. discriminate. discriminate.
    + case (n =? n0) eqn:case1. discriminate. discriminate.
    + admit.
Admitted. (* Not needed. *)

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

Inductive proof (l : list (term*term)) : term -> term -> Prop :=
  | proofAxm : forall s t, In (s, t) l -> proof l s t
  | proofRefl : forall t, proof l t t
  | proofSymm : forall s t, proof l s t -> proof l t s
  | proofTrans : forall s t u, proof l s t -> proof l t u -> proof l s u
  | proofCong : forall (n : nat) s t, proof l s t -> proof l (fn n s) (fn n t).

Lemma proof_monotonic_cons : forall h l a b, proof l a b -> proof (h::l) a b.
Proof.
  intros h l a b Hprf. induction Hprf.
  - apply proofAxm. simpl. right. assumption.
  - apply proofRefl.
  - apply proofSymm. assumption.
  - apply (proofTrans (h::l) s t u); assumption.
  - apply proofCong. assumption.
Qed.

(* Generalization of in_cons *)
Lemma In_mono: forall A (l k: list A) (x: A), In x l -> In x (k++l).
Proof.
  intros. induction k as [| h k' IHk'].
  - simpl. assumption.
  - simpl. right; assumption.
Qed.

(* Maybe gen to proof l a b \/ proof k a b -> proof (l++k) a b *)
Lemma proof_monotonic : forall k l a b, proof l a b -> proof (k++l) a b.
Proof.
  intros k l. induction k as [|hk k' IHk'].
  - intros; simpl; assumption.
  - intros.  induction H.  
    + apply (In_mono (term*term) l k' (s,t)) in H. apply proofAxm in H. simpl.
      apply proof_monotonic_cons. assumption.
    + apply proofRefl.
    + apply proofSymm. apply IHproof.
    + apply (proofTrans _ s t u); [apply IHproof1 | apply IHproof2].
    + apply proofCong. assumption.
Qed.

Inductive Subterm : term -> term -> Prop :=
  | subRefl : forall t, Subterm t t
  | subFn : forall n s, Subterm s (fn n s)
  | subTrans : forall s t u, Subterm s t -> Subterm t u -> Subterm s u.

(* Lets modify definition of occurs and define mapRep only for elements that Occur in eql. *)
Definition Occurs (eql: list (term*term)) (t: term) := 
  exists x, (In (t,x) eql \/ In (x,t) eql) /\ Subterm t x.

(* We assume the existence of appropriate representation by assuming a correct merge operation. *)
Definition Decidable_Eq (T:Type) := forall a b: T, Decidable.decidable (a = b).

(* Type of the map of representatives, where R is the type of the representative(which ofcourse, needs to be decidable).
We need term -> R , where R is decidable. *)
Definition mapRep eql (R:{T: Type | Decidable_Eq T }) := 
  {r:term | Occurs eql r } -> (proj1_sig R).

(* Decision procedure type, used in do_tc. *)
Definition DecProc (R:{T: Type | Decidable_Eq T }) := 
  forall (x y: (proj1_sig R)), {x = y} + {x <> y}.

(* Well-formed Representative Map *)
Definition WFM (eql: list (term*term)) (R:{T: Type | Decidable_Eq T}) : 
  mapRep eql R -> Prop := 
    fun ufm =>
        (forall t1 t2, ufm t1 = ufm t2 -> proof eql (proj1_sig t1) (proj1_sig t2)).

Check exist.
Check sigT.

Lemma WFM_preserved : forall h l R m, WFM (h::l) R m -> exists m', WFM l R m'.
(* intros. pose(forall t, if In l t then m t else False). *)
Admitted.

(* The actual merge operation.
(R in merge had to be explicit o/w type cannot be inferred in proof of do_tc) *)
(* TODO: Check correctness conditions for parents. *)
Definition merge R eql 
(a b: {t: term | Occurs eql t}) (Hpf: proof eql (proj1_sig a) (proj1_sig b))
  (ufm: { m: mapRep eql R | WFM eql R m }) :
      ({ m: mapRep eql R | WFM eql R m /\ 
        (forall x, (proj1_sig ufm) x = (proj1_sig ufm) a -> 
            (forall y, Subterm (proj1_sig x) (proj1_sig y) -> 
                          m y = (proj1_sig ufm) b)) /\ 
        (forall x, (proj1_sig ufm) x <> (proj1_sig ufm) a ->
            (forall y, Subterm (proj1_sig x) (proj1_sig y) -> 
                          (proj1_sig ufm) y = m y)) } ).
Admitted.

(* No stupid suffix business, use one list and induct over it. *)

Fixpoint do_cc {R} (decProc: DecProc R) (eql: list (term*term)) :
  {m: mapRep eql R | WFM eql R m} -> 
    {m: mapRep eql R | WFM eql R m /\ 
      forall a b, proof eql (proj1_sig a) (proj1_sig b) -> m a = m b}.
Proof.
intros omap. induction eql as [| [x y] eql' imap].
-  assert (B1: forall r, ~Occurs [] r).
  {
    unfold not. intros. unfold Occurs in H. destruct H as [ x [[A | B] _]].
    inversion A. inversion B.
  }
(* Show type is uninhabited because no type corresp. even the second conjunct is habited. *)
  destruct omap as [m mProp]. unfold WFM in mProp. exists m. split.
  + unfold WFM. intros. exfalso. destruct t1 as [t1 t1prf]. 
    unfold not in B1. apply (B1 t1). assumption.
  + intros. exfalso. destruct a as [a aPrf].
    unfold not in B1. apply (B1 a). assumption.
(* Well, we showed both. Ok! *)
- destruct omap as [omap omapH]. exists omap. split.
  + assumption.
  + (* Use merge to build goal. *)
    intros. assert(T1 := omapH).
    apply WFM_preserved in T1. destruct T1 as [m' m'WF].
    pose(I1 := exist (WFM eql' R) m'). apply I1 in m'WF. apply imap in m'WF.
    clear imap do_cc I1. rename m' into m. rename m'WF into mWF.
    (* Lost information that m is omap, WFM_preserved is too weak. *)
  

Admitted.
