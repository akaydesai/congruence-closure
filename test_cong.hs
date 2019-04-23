module Test_cong where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 _ iHl ->
    let {s = h a0 a} in case s of {
                         Left -> Left;
                         Right -> iHl}) l

list_eq_dec :: (a1 -> a1 -> Sumbool) -> (List a1) -> (List a1) -> Sumbool
list_eq_dec eq_dec l l' =
  list_rect (\x -> case x of {
                    Nil -> Left;
                    Cons _ _ -> Right}) (\a _ x x0 ->
    case x0 of {
     Nil -> Right;
     Cons a0 l1 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (x l1))
        (\_ -> Right) (eq_dec a a0)}) l l'

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

nodup :: (a1 -> a1 -> Sumbool) -> (List a1) -> List a1
nodup decA l =
  case l of {
   Nil -> Nil;
   Cons x xs ->
    case in_dec decA x xs of {
     Left -> nodup decA xs;
     Right -> Cons x (nodup decA xs)}}

type Set a = List a

empty_set :: Set a1
empty_set =
  Nil

set_add :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Set a1
set_add aeq_dec a x =
  case x of {
   Nil -> Cons a Nil;
   Cons a1 x1 ->
    case aeq_dec a a1 of {
     Left -> Cons a1 x1;
     Right -> Cons a1 (set_add aeq_dec a x1)}}

set_remove :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Set a1
set_remove aeq_dec a x =
  case x of {
   Nil -> empty_set;
   Cons a1 x1 ->
    case aeq_dec a a1 of {
     Left -> x1;
     Right -> Cons a1 (set_remove aeq_dec a x1)}}

set_union :: (a1 -> a1 -> Sumbool) -> (Set a1) -> (Set a1) -> Set a1
set_union aeq_dec x y =
  case y of {
   Nil -> x;
   Cons a1 y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)}

set_In_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Sumbool
set_In_dec aeq_dec a x =
  list_rec Right (\a0 _ ha0 ->
    case aeq_dec a a0 of {
     Left -> eq_rec_r a0 Left a;
     Right -> sumbool_rec (\_ -> Left) (\_ -> Right) ha0}) x

type Term = Nat
  -- singleton inductive, whose constructor was var
  
nat_beq :: Nat -> Nat -> Bool
nat_beq x y =
  case x of {
   O -> case y of {
         O -> True;
         S _ -> False};
   S x0 -> case y of {
            O -> False;
            S x1 -> nat_beq x0 x1}}

term_beq :: Term -> Term -> Bool
term_beq =
  nat_beq

term_eq_dec :: Term -> Term -> Sumbool
term_eq_dec x y =
  let {b = term_beq x y} in case b of {
                             True -> Left;
                             False -> Right}

subterms :: Term -> List Term
subterms t =
  Cons t Nil

get_subterms :: (Set (Prod Term Term)) -> List Term
get_subterms l =
  case l of {
   Nil -> Nil;
   Cons p l' ->
    case p of {
     Pair t1 t2 -> app (subterms t1) (app (subterms t2) (get_subterms l'))}}

setterm_eq_dec :: (List Term) -> (List Term) -> Sumbool
setterm_eq_dec =
  list_eq_dec term_eq_dec

set_setterm_add :: (List Term) -> (Set (List Term)) -> Set (List Term)
set_setterm_add =
  set_add setterm_eq_dec

create_ufs :: (Set (Prod Term Term)) -> Set (Set Term)
create_ufs l =
  map (\t -> Cons t Nil) (nodup term_eq_dec (get_subterms l))

uf_find :: Term -> (Set (Set Term)) -> Option (Set Term)
uf_find x ufs =
  case ufs of {
   Nil -> None;
   Cons uh ufs' ->
    case set_In_dec term_eq_dec x uh of {
     Left -> Some uh;
     Right -> uf_find x ufs'}}

uf_merge :: (Set (Set Term)) -> Term -> Term -> Set (Set Term)
uf_merge ufs x y =
  let {qx = uf_find x ufs} in
  let {qy = uf_find y ufs} in
  case qx of {
   Some sx ->
    case qy of {
     Some sy ->
      set_setterm_add (set_union term_eq_dec sx sy)
        (set_remove setterm_eq_dec sy (set_remove setterm_eq_dec sx ufs));
     None -> ufs};
   None -> ufs}

do_cc :: (Set (Prod Term Term)) -> (Set (Set Term)) -> Set (Set Term)
do_cc work ufs =
  case work of {
   Nil -> ufs;
   Cons p work' ->
    case p of {
     Pair t1 t2 -> do_cc work' (uf_merge ufs t1 t2)}}

cc_algo :: (Set (Prod Term Term)) -> Term -> Term -> Bool
cc_algo work t1 t2 =
  let {ufs = create_ufs work} in
  let {res = do_cc work ufs} in
  let {qt1 = uf_find t1 res} in
  let {qt2 = uf_find t2 res} in
  case qt1 of {
   Some st1 ->
    case qt2 of {
     Some st2 ->
      case setterm_eq_dec st1 st2 of {
       Left -> True;
       Right -> False};
     None -> False};
   None -> False}

