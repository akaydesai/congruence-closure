Require Import Coq.Lists.List.

Require Import Coq.Classes.EquivDec.


Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


(* Definition xlist := [1;1;1;1]. *)

(* Check ([1; 2; 3; 4]). *)

(* Check (var1 [1; 2; 3]). *)



  
(* Inductive terms : Set := *)
(* | var : string -> terms *)
(* | app : string -> terms list -> terms. *)

Inductive term : Set :=
| var : nat -> term
| fn  : nat -> term -> term.

Check fn 1 (fn 1 (var 2)).

Inductive form : Set :=
| eq : term -> term -> form.

Notation "x -=- y" := (eq x y)
                        (at level 60).

Check (fn 1 (var 2)) -=- (var 2).

(* Check exists  *)

(* Inductive prf (l : list (term * term)) : term -> Prop := *)
(*   prfrefl (a : term) : (prf l a). *)


(* Inductive prf (l : list (term * term)) (a : term) : term -> Prop := *)
(*   prfrefl : prf l a a *)
(*   prfsym  : prf l a b -> prf l b a.  *)


(* The correctness condition *)

Inductive prf (l : list (term * term)) : term -> term -> Prop  :=
(* | paxm  :  *)  
| pref : forall t, prf l t t
| psym : forall s t, prf l s t -> prf l t s
| ptrs : forall s t u, prf l s t -> prf l t u -> prf l s u
| pcong : forall (n : nat) s t, prf l s t -> prf l (fn n s) (fn n t).


Check psym [] (var 2) ( var 2) (pref [] (var 2) ).

Check prf.  



(* computes all the subterms of a given term. *)

Fixpoint subterms (t : term) : list term :=
  match t with
  | var n => [var n]
  | fn n t1 => (fn n t1) :: subterms t1
  end.

(* give list of tuples of term and its parent *)

Fixpoint parent_list (t : term) :=
  match t with
  | var _ => []
  | fn n t => (t, fn n t) :: parent_list t
  end.

Eval compute in parent_list (fn 1 (var 2)).

Scheme Equality for term.

Check term_eq_dec.

Eval compute in term_eq_dec (var 2) (fn 1 (var 3)).

Eval compute in term_beq (var 2) (var 3).

Eval compute in if (term_beq (var 2) (var 2)) then 1 else 0.


(* Ignore this *)

Definition f (t : term) (arg : term*term) :=
  match arg with
  | (x, _) => term_beq t x
  end.
  

(* gets the parents of a particular term from parent_list *)

Definition get_parents (t : term) (l : list (term*term)) :=
  map (fun x => match x with | (_, n) => n end) (filter (f t) l).

Eval compute in get_parents (var 2) (parent_list (fn 1 (var 2)) ++ parent_list (fn 3 (var 2))).


Check remove.

Check List.remove.

Check last.

Eval compute in remove term_eq_dec (var 2) [var 2; var 3; var 4].

Definition removeT l := remove term_eq_dec (var 2) l.


(* Scheme Equality for term*term. *)

Definition term_pairs_eqb (u v : term * term) :=
  match (u, v) with
  | ((a, b), (c, d)) => andb  (term_beq a c) (term_beq b d)
  end.


(* equality for... *)
(* Definition term_pairs_eq_dec (u v : term * term) := *)
(*   match (u, v) with *)
(*   | ((a, b), (c, d)) => (term_eq_dec a c) /\ (term_eq_dec b d) *)
(*   end. *)

Definition removeTP a l := remove term_pairs_eq a l.

(* Setting up the UF datastructure. Will need further modification *)

(* Fixpoint uf_find (l : list (term*term)) (t : term) := *)
(*   match l with *)
(*   | [] => var 1000 *)
(*   | (x, y)::ls => if term_beq x t then (if term_beq x y then x else uf_find l y) else *)
(*                     uf_find ls t *)
(*   end. *)


(* Fixpoint uf_merge (l : list (term*term)) (u v : term) := *)
(*   let a := uf_find l u in *)
(*   let b := uf_find l v in *)
(*   if term_beq a b then l else remove *)


                    
(* Ignore this *)
(* Fixpoint get_parents (t : term) (l : list (term*nat)) := *)
(*   match l with *)
(*   | [] => [] *)
(*   | (x,n) :: xs => match t with *)
(*                    | x => n :: get_parents t xs *)
(*                    | _ => get_parents t xs *)
(*                    end *)
                   
(*   end. *)








