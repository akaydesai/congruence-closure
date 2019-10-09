Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations. (* Why does Require complain about path? *)

Require Import Coq.Classes.EquivDec.

Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Require Import Coq.Bool.Bool. 

Inductive term : Set :=
  | var : nat -> term.

(* Let's get term decidability for free. *)
Scheme Equality for term.
(* nat_beq is defined
term_beq is defined
term_eq_dec is defined  *)

(* a = b \/ a <> b. *)
Corollary term_eq_decidable : forall (a b:term), Decidable.decidable (a = b). 
Proof. intros. pose ( T := term_eq_dec a b). destruct T. left. assumption. right. assumption. Qed.

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

Inductive proof (l : list (term*term)) : term -> term -> Prop :=
  | proofAxm : forall s t, In (s, t) l -> proof l s t
  | proofRefl : forall t, proof l t t
  | proofSymm : forall s t, proof l s t -> proof l t s
  | proofTrans : forall s t u, proof l s t -> proof l t u -> proof l s u.

Lemma proof_monotonic_cons : forall h l a b, proof l a b -> proof (h::l) a b.
Proof.
  intros h l a b Hprf. induction Hprf.
  - apply proofAxm. simpl. right. assumption.
  - apply proofRefl.
  - apply proofSymm. assumption.
  - apply (proofTrans (h::l) s t u); assumption.
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
Qed.

Definition Occurs (eql: list (term*term)) (t: term) := 
  exists x, In (t,x) eql \/ In (x,t) eql.

Check Occurs [].
Example test: (Occurs [(var 1, var 2)] (var 2)).
Proof. unfold Occurs. exists (var 1). simpl. right. left; reflexivity. Qed.

(* We assume the existence of appropriate representation by assuming a correct merge operation. *)
Definition Decidable_Eq (T:Type) := forall a b: T, Decidable.decidable (a = b).

(* Type of the map of representatives, where R is the type of the representative(which ofcourse, needs to be decidable).
We need term -> R , where R is decidable. *)
Definition mapRep (R:{T: Type | Decidable_Eq T }) := term -> (proj1_sig R).

(* Decision procedure type, used in do_tc. *)
Definition DecEqT (R:{T: Type | Decidable_Eq T }) := 
  forall (x y: (proj1_sig R)), {x = y} + {x <> y}.

(* Well-formed Representative Map *)
Definition WFM (eql: list (term*term)) (R:{T: Type | Decidable_Eq T}) : 
  mapRep R -> Prop := 
    fun ufm =>
        (forall t1 t2, ufm t1 = ufm t2 -> proof eql t1 t2).

(* The actual merge operation.
(R in merge had to be explicit o/w type cannot be inferred in proof of do_tc) *)
Definition merge R eql 
(a b: term) (Hpf: proof eql a b)
  (ufm: { m: mapRep R | WFM eql R m }) :
      ({ m: mapRep R | WFM eql R m /\ 
        (forall x, (proj1_sig ufm) x = (proj1_sig ufm) a -> 
                    m x = (proj1_sig ufm) b) /\ 
          (forall x, (proj1_sig ufm) x <> (proj1_sig ufm) a ->
                    (proj1_sig ufm) x = m x) } ).
Admitted.

Lemma aux1 : forall l x y, Occurs ((x,y)::l) x /\ Occurs ((x,y)::l) y.
Proof.
  intros. unfold Occurs. split.
  - exists y. simpl. repeat left. reflexivity.
  - exists x. simpl. right. left. reflexivity.
Defined.

(* a is suffix of b *)
Definition suffix {A} (a b: list A) := exists c, b = c ++ a.

Lemma suffix_monoton : forall A (a:A) (l1 l2: list A), 
  suffix (a::l1) l2 -> suffix l1 l2.
Proof.
  intros. destruct H. unfold suffix. exists (x++[a]). Locate "++". Search app.
  rewrite <- app_assoc. simpl. assumption.
Qed.

Lemma emp_no_proof: forall a b, a <> b -> ~(proof [] a b).
Proof.
  unfold not. intros a b H Hprf. 
  induction Hprf; simpl in *;try assumption.
  - apply H; reflexivity. 
  - apply IHHprf. intros. subst. apply H. reflexivity.
  - apply IHHprf1. intros. subst. apply IHHprf2. intros. subst. apply H. reflexivity.
Qed.

Lemma emp_proof_eq: forall a b, proof [] a b -> a = b.
Proof.
  intros. induction H.
  - simpl in H; contradiction.
  - reflexivity.
  - symmetry; assumption.
  - subst. reflexivity.
Qed.

Lemma occurs_mono: forall l l' x, suffix l' l -> Occurs l' x -> Occurs l x.
Proof.
  intros. unfold suffix in H. destruct H as [el H]. rewrite H. unfold Occurs in H0.
  destruct H0 as [y H0]. 
  unfold Occurs. exists y. destruct el as [| h el'].
  - simpl. assumption.
  - simpl. destruct H0; [left| right]; right; apply In_mono; assumption.
Qed.

Check sig (Occurs []).
Check exist (Occurs []).

(* R is the decidable representative type, decProc the corresponding decision procedure.
eql is the original list of equalities. l is a suffix of eql (we induct on eql).
This convoluted definition with two lists is not needed for transitive closure, but was used because we thought it would be easier to change this later to work for the congruence case. *)
Fixpoint do_tc {R} (decProc: DecEqT R) (eql: list (term*term)) 
  (l: {k: list (term*term) | suffix k eql}) :
    {m: mapRep R | WFM eql R m} -> 
      {m: mapRep R | WFM eql R m /\ forall a b, proof (proj1_sig l) a b -> m a = m b}.
Proof.
intros. destruct l as [l Hpf]. 
  (* X as [x W] is the input map to the original do_tc call. *)
simpl in *. destruct X as [x W]. induction l as [ | (hl1, hl2) l' IHl'].
- simpl. exists x. split; try assumption.
  intros r k H. destruct H.
  + simpl in H. contradiction.
  + reflexivity.
  + apply emp_proof_eq in H. subst. reflexivity.
  + apply emp_proof_eq in H. apply emp_proof_eq in H0. subst. reflexivity.
- clear do_tc. assert(HPf := Hpf). apply suffix_monoton in Hpf.
  rename Hpf into Hpf'. assert(Hres := Hpf').
  (* Hres is the result of recursive call to do_tc, m' is the corresponding MapRep. *)
  apply IHl' in Hres. clear IHl'.
  assert(HResN := Hres).
  destruct Hres as [m' [Hm'WFM Hm'tc]].
  (* Now use merge to build goal. That's why we did destruct Hres. So we can call merge.
  Show that m' and result of merge differ only in the case where the equiv class of a is concerned. *)
  assert(H1 : Occurs ((hl1,hl2)::l') hl1).
  { unfold Occurs. exists hl2. simpl. repeat left; reflexivity. }
  assert(H2 : Occurs ((hl1,hl2)::l') hl2).
  { unfold Occurs. exists hl1. simpl. right. left; reflexivity. }
  (* Use Occurs monotonic, to prove asserts. *)
  assert(h1' : Occurs eql hl1). 
  { apply (occurs_mono eql ((hl1,hl2)::l')); assumption. } clear H1.
  assert(h2' : Occurs eql hl2).
  { apply (occurs_mono eql ((hl1,hl2)::l')); assumption. } clear H2.
  Check exist. pose(E1 := exist (Occurs eql)). 
  assert(H1:=h1'). assert(H2:=h2').
  apply E1 in h1'. apply E1 in h2'. clear E1.
  assert(A1 : proof eql hl1 hl2). 
  {
    unfold suffix in HPf. destruct HPf as [y HPf]. rewrite HPf.
    assert(A: proof ((hl1,hl2)::l') hl1 hl2). 
    { apply proofAxm. simpl. left; reflexivity. }
    (* Prove by showing generalized monotonicity of proof(++ instead of ::) *)
    (* This might've not been necessary if we were only using one list: eql *)
    apply proof_monotonic. assumption.
  }
  pose(E2 := exist (WFM eql R) m').
  pose (C := merge R eql hl1 hl2 A1 (E2 Hm'WFM)).
  (* C, the result of merge, is our witness. *)
   destruct C as [M [HMpf [HM1 HM2]]].
  assert(recov: m' = (proj1_sig (E2 Hm'WFM))). { simpl. reflexivity. }
  assert(recovG: forall q, m' q = proj1_sig (E2 Hm'WFM) q).
  { intros. simpl. reflexivity. }
  setoid_rewrite <- recovG in HM1. (* This does all *)
  setoid_rewrite <- recovG in HM2. clear recov recovG.
  rename HM1 into mergProp1. rename HM2 into mergProp2.

  (* Use the fact that classes don't split. *)
  assert(HMrecPf : forall a b : term, proof l' a b -> M a = M b).
  (* Maybe we don't need this assertion. *)
  { 
    intros. induction H.
    - apply proofAxm in H. apply Hm'tc in H.
      (* Case analysis, based on antecedents of mergeprops. *)
      pose(P := decProc (m' t) (m' hl1)). destruct P as [P|P].
      + pose(Tmerg1 := mergProp1 t). pose(Tmerg2 := mergProp1 s).
         rewrite P in H. apply Tmerg1 in P. apply Tmerg2 in H.
         rewrite H, P. reflexivity.
      + pose(Tmerg1 := mergProp2 t). pose(Tmerg2 := mergProp2 s).
        assert(Pn := P). rewrite <- H in P. apply Tmerg2 in P.
        apply Tmerg1 in Pn. rewrite <- P, <- Pn. assumption.
    - reflexivity.
    - symmetry; assumption.
    - rewrite IHproof2 in IHproof1. assumption.
  }
  (* We need to use HMrecPf, A1 to derive Goal by induction on proof(refer whiteboard) *)
  assert(Hfinal : forall a b, proof ((hl1, hl2)::l') a b -> M a = M b).
  {
    intros. induction H.
    - simpl in H. destruct H.
      + inversion H. rewrite <- H3; rewrite <- H4. clear H; clear H3; clear H4.
        (* Case analysis, based on antecedents of mergProps. *)
        pose(P := decProc (m' hl2) (m' hl1)). 
        assert(Pn : m' hl1 = m' hl1). { reflexivity. } apply (mergProp1 hl1) in Pn.
        destruct P as [P|P].
        * apply (mergProp1 hl2) in P. 
          rewrite <- Pn in P. symmetry; assumption.
        * apply (mergProp2 hl2) in P. rewrite <- Pn in P. assumption.
      + (* Use Hm'tc and corr *)
        apply proofAxm in H. pose (HMrecPf s t). apply e; assumption.
    - reflexivity.
    - symmetry; assumption.
    - rewrite IHproof2 in IHproof1. assumption.
  }
 exists M. split; assumption.
Defined.

(* While the above definition of merge is sufficient to prove transitive closure, 
it's not strong enough to actually implement merge itself.
So we provide an augmented merge' below which ought be implementable; but it isn't fully thought out. We might need to switch to partial maps, amongst other things to make it work. *)

Definition mapClass (R:{T: Type | Decidable_Eq T}) := (proj1_sig R) -> list term.

(* Well formed reverse map, aka class map *)
Definition WFC (eql: list (term*term)) (R:{T: Type | Decidable_Eq T}) :
  mapClass R -> Prop :=
    fun cm => forall x y r, In x (cm r) /\ In y (cm r) -> proof eql x y.

Definition merge' R eql
(a b: term) (Hpf: proof eql a b)
  (maps:{m : ({mr: mapRep R | WFM eql R mr } * {mc: mapClass R | WFC eql R mc}) | 
  forall t r, (proj1_sig (fst m)) t = r <-> In t ((proj1_sig (snd m)) r) })
  :
  {m : ({mr: mapRep R | WFM eql R mr } * {mc: mapClass R | WFC eql R mc}) | 
  forall t r, 
    (proj1_sig (fst m)) t = r <-> In t ((proj1_sig (snd m)) r) /\ 
  forall t, 
    (proj1_sig (fst (proj1_sig maps))) t = (proj1_sig (fst (proj1_sig maps))) a -> 
      (proj1_sig (fst m)) t = (proj1_sig (fst (proj1_sig maps))) b /\
  forall t, 
    (proj1_sig (fst (proj1_sig maps))) t <> (proj1_sig (fst (proj1_sig maps))) a -> 
      (proj1_sig (fst m)) t = (proj1_sig (fst (proj1_sig maps))) t }.
Admitted.
