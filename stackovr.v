Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.ListSet.
Require Import Coq.Bool.Bool.

Inductive term : Set :=
  | var : nat -> term
  | fn : nat -> term -> term.

Scheme Equality for term.

Fixpoint uf_find (x : term) (ufs : set (set term)) : option (set term) :=
  match ufs with
  | [] => None
  | uh::ufs' => match (set_In_dec term_eq_dec x uh) with
                | left _ _ => Some uh 
                | right _ _ => uf_find x ufs'
                end
  end.
Compute uf_find (var 3) nil.
(* Why isn't this fully reduced? *)
Compute uf_find (var 3) (cons nil nil).

(* But this works *)
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