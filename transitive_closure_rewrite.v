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
  | var : nat -> term.

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

(* Definition ufm (l:list term) (R: Type) (t:{ x:term | In x l }) : term := var 0. *)
(* Why cant member of subtype(t) be used instead of term?
 We use option instead of this definition so that we need not add query terms to ufm.
 *)
 
Locate "==".

Definition Occurs (eql: list (term*term)) (t: term) := 
  exists x, In (t,x) eql \/ In (x,t) eql.

(* Inductive Occurs (eql: list (term*term)) (t: term) := 
  | left : (exists x, In (t,x) eql) -> Occurs eql t
  | right : (exists x, In (x,t) eql -> Occurs eql t. *)

Check Occurs [].
Example test: (Occurs [(var 1, var 2)] (var 2)).
Proof. unfold Occurs. exists (var 1). simpl. right. left; reflexivity. Qed.

Definition Decidable_Eq (T:Type) := forall a b: T, Decidable.decidable (a = b).

(* We need term -> R , where R is decidable. *)
Definition mapRep (R:{T: Type | Decidable_Eq T }) := 
(*   term -> {T: Type | forall a b: T, Decidable.decidable (a = b)}. *)
  term -> (proj1_sig R).

Definition mapClass (R:{T: Type | Decidable_Eq T}) := (proj1_sig R) -> list term.

Definition DecEqT (R:{T: Type | Decidable_Eq T }) := 
  forall (x y: (proj1_sig R)), {x = y} + {x <> y}.

(* Well-formed Rep Map *)
Definition WFM (eql: list (term*term)) (R:{T: Type | Decidable_Eq T}) : 
  mapRep R -> Prop := 
    fun ufm =>
(*      (forall t, exists r, ufm t = Some r <-> Occurs eql t) /\  *)
(*         (forall t, ufm t = None <-> ~ Occurs eql t) /\ *)
        (forall t1 t2, ufm t1 = ufm t2 -> proof eql t1 t2).

(* Well formed reverse map, aka class map *)
Definition WFC (eql: list (term*term)) (R:{T: Type | Decidable_Eq T}) :
  mapClass R -> Prop :=
    fun cm => forall x y r, In x (cm r) /\ In y (cm r) -> proof eql x y.

Lemma proof_implies_occurence: forall l a b, 
  l <> [] /\ proof l a b -> Occurs l a /\ Occurs l b.
Proof.
  intros l a b [Hemp ]. induction l as [ | h l' IHl'].
  - induction H.
    + inversion H.
    + (* proof [] t t -/> Occurs, hence Hemp constraint *)
      contradiction.
    + destruct IHproof; unfold Occurs in *. split;
      [ destruct H0 as [x [Ha | Hb]] | destruct H0 as [x [Ha | Hb]] ];
      try inversion Ha; try inversion Hb.
    + exfalso. destruct IHproof1. unfold Occurs in H1. destruct H1 as [x []];
      simpl in H1; contradiction.
  - induction H.
  
Admitted. (* Not used *)

(* Dummy merge for now *)
(* Definition merge {R} eql : 
  { eq : term*term | proof eql (fst eq) (snd eq) } -> 
(*     Occurs (fst eq) eql /\ Occurs (snd eq) eql } ->  *)
      ({ m: mapRep R | WFM eql R m }) -> ({ m: mapRep R | WFM eql R m }). 
(*       :=  
      (* Add correctness to return type? How? 
         This will cause type problems in do_tc, since we don't have subtyping. *)
        fun eq m => m. *) *)

(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype. *)
Locate "<:".
(* Check subType. *)

(* Here we go, can't type a b. No subtyping, lets use projections. *)
(* Maybe we don't need Occurs for merge *)
(* Cross-check this definition with the correctness condition on whiteboard. *)
Definition merge R eql 
(* R had to be explicit o/w type cannot be inferred in proof of do_tc *)
(a b: term) (Hpf: proof eql a b)
  (ufm: { m: mapRep R | WFM eql R m }) :
      ({ m: mapRep R | WFM eql R m /\ 
        (forall x, (proj1_sig ufm) x = (proj1_sig ufm) a -> 
                    m x = (proj1_sig ufm) b) /\ 
                    (* Stronger: RHS above = (proj1_sig ufm) b, but this is implied by next conjunct, so let's explicity say it anyways instead of m (proj1_sig b) *)
          (forall x, (proj1_sig ufm) x <> (proj1_sig ufm) a ->
                    (proj1_sig ufm) x = m x) } ).
Admitted.
(* But now we need to recover map of type { m:mapRep R | WFM } for use by do_tc. 
   How?
   Take proj2 to get proofs and recover fst proof and build back sig type over mapRep.
   FML! *)

Locate "*". Print prod. 
(* merge should be implementable with this augmented type. Might need to use partial maps.
  Simplify all complicated types using lets? *)
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

Lemma aux1 : forall l x y, Occurs ((x,y)::l) x /\ Occurs ((x,y)::l) y.
Proof.
  intros. unfold Occurs. split.
  - exists y. simpl. repeat left. reflexivity.
  - exists x. simpl. right. left. reflexivity.
Defined.

(* Restrict to nonempty eql?, otherwise problems due to "forall t, proof [] t t"*)
(* Proving completeness is also an issue due to "forall t, proof [] t t", 
   Is there any way to solve this that does not involve adding query terms to do_cc?
   How about a 3-valued option type? Nah! Why complicate further! 
   Modify Occurs to include query terms? *)
(* Need to assert that l is a part of eql? Suffix maybe, incl is weaker. *)
Search "sub".

(* a is suffix of b *)
Definition suffix {A} (a b: list A) := exists c, b = c ++ a.

Lemma suffix_antimon : forall A (a:A) (l1 l2: list A), 
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
(*   assert(A: forall h x, Occurs l' x -> Occurs(h::l') x). admit. *)
  unfold Occurs. exists y. destruct el as [| h el'].
  - simpl. assumption.
  - simpl. destruct H0; [left| right]; right; apply In_mono; assumption.
Qed.

Check sig (Occurs []).
Check exist (Occurs []).
(* Search list. *)
(* Check sig term. *) 
(* Alternate design, use two lists, one as accumulator of processed eqs; but this doesn't extend to cong closure; where we find fixpoint of ufm(Check with Manna). *)

(* Remove Occurs from merge, How do you do that without needing to add query terms?
   Well, lets ignore query terms for now and only show soundness and completeness for do_tc. *)
(* Inducting on eql without keeping a copy should be sufficient for tc, since WFM is valid due to monotonicity of proof. *)
Fixpoint do_tc {R} (decProc: DecEqT R) (eql: list (term*term)) 
  (l: {k: list (term*term) | suffix k eql}) :
    {m: mapRep R | WFM eql R m} -> 
      {m: mapRep R | WFM eql R m /\ forall a b, proof (proj1_sig l) a b -> m a = m b}.
Proof.
intros. destruct l as [l Hpf]. 
  (* X as [x W] is the input map to the original do_tc call. *)
simpl in *. destruct X as [x W]. induction l as [ | (hl1, hl2) l' IHl'].
- simpl. assert (F : forall (a b:term), False -> x a = x b). 
  { intros. exfalso. assumption. } exists x. split; try assumption.
  intros r k H. destruct H.
  + simpl in H. contradiction.
  + reflexivity.
  + apply emp_proof_eq in H. subst. reflexivity.
  + apply emp_proof_eq in H. apply emp_proof_eq in H0. subst. reflexivity.
- clear do_tc. assert(HPf := Hpf). apply suffix_antimon in Hpf.
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
  (* Had to make param R of merge explicit *)
  (* C, the result of merge, is our witness. *)
   destruct C as [M [HMpf [HM1 HM2]]].
  (* But, in constructing M, we have lost the information that it was created by modifying m'. Hence Hm'tc is useless, since we can't recover m' from HM1 and HM2.
  When creating the sig type, we also need m' to be the witness for the subtype.
  But this would require m' to belong to two types, which needs subtyping.
  If we could recover... *)
(*   unfold E2 in H. unfold E2 in HM1. *)
  assert(recov: m' = (proj1_sig (E2 Hm'WFM))). { simpl. reflexivity. }
  try setoid_rewrite <- recov in HM1. (* Why won't this work? *)
  (* Let's try removing the forall x, *)
  assert(HM1n := HM1 hl2). try rewrite <- recov in HM1n. (* Wtf *)
(*   unfold WFM in Hm'WFM. rewrite <- recov in HM1n. *) (* Nope! *)
  assert(recovG: forall q, m' q = proj1_sig (E2 Hm'WFM) q).
  { intros. simpl. reflexivity. }
(*   setoid_rewrite <- (recovG hl2) in HM1. (* Phew!! *) clear HM1n. *)
  setoid_rewrite <- recovG in HM1. (* This does all *) clear HM1n.
  setoid_rewrite <- recovG in HM2. clear recov recovG.
  rename HM1 into mergProp1. rename HM2 into mergProp2.

  (* ...then we can show. Maybe use the fact that classes don't split. *)
  assert(HMrecPf : forall a b : term, proof l' a b -> M a = M b).
  (* Maybe we don't need this assertion. *)
  { 
    intros. induction H.
    - apply proofAxm in H. apply Hm'tc in H.
      (* Make this goal a lemma, keeps coming up everywhere. *)
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
        (* Case analysis, based on antecedents of mergProps. 
          Requires equality for R to be decidable. *)
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
