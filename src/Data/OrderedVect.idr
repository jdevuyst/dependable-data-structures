module Data.OrderedVect

import Rekenaar

import Decidable.Order

%default total
%language ElabReflection

mutual
  public export
  data OrderedVect : Nat -> (constraint : Ordered ty to) -> Type where
    Nil : .{auto constraint : Ordered ty to}
        -> OrderedVect Z constraint
    (::) : .{constraint : Ordered ty to}
        -> (x : ty)
        -> (v : OrderedVect n constraint)
        -> .{auto prf : Fits x v}
        -> OrderedVect (S n) constraint

  public export
  Fits : {constraint : Ordered ty to} -> ty -> OrderedVect n constraint -> Type
  Fits _ Nil = ()
  Fits n (m :: _) = to n m

%name OrderedVect xs,ys,zs

export
head : .{constraint : Ordered ty to} -> OrderedVect (S _) constraint -> ty
head (x :: _) = x

fitsTrans : (Fits {constraint} x ys) -> Fits {constraint} (head ys) zs -> Fits {constraint} x zs
fitsTrans {zs = []} _ _ = ()
fitsTrans {x} {ys = y' :: _} {zs = z' :: _} rel1 rel2 = transitive x y' z' rel1 rel2

mutual
  merge' : .{constraint : Ordered ty to}
        -> {n : Nat}
        -> (v1 : OrderedVect (S n) constraint)
        -> {m : Nat}
        -> (v2 : OrderedVect (S m) constraint)
        -> (ret : OrderedVect ((S n) + (S m)) constraint ** Either (Fits (head v1) ret) (Fits (head v2) ret))
  merge' [] _ impossible
  merge' _ [] impossible
  merge' {to} [x] [y] = case order {to} x y of
                        Left prf => ([x, y] ** Left (reflexive x))
                        Right prf => ([y, x] ** Right (reflexive y))
  merge' {m} [x] (y :: ys) = rewrite the (S m = m + 1) (%runElab natPlusRefl) in
                             case assert_total $ merge' (y :: ys) [x] of
                             (ref ** Left prf) => (ref ** Right prf)
                             (ref ** Right prf) => (ref ** Left prf)
  merge' {n = S cntX} (x :: xs) [y]
    = case order {to} x y of
      Left prf => case mergeHelper xs [y] x of
                  (zs ** fitsPrf) => (zs ** Left fitsPrf)
      Right prf => rewrite the (cntX + 1 = S cntX) (%runElab natPlusRefl) in
                   ((y :: x :: xs) ** Right (reflexive y))
  merge' ((::) {n = S cntX} x (x' :: xs'))
        ((::) {n = S cntY} y (y' :: ys'))
    = case order {to} x y of
      Left prf => case mergeHelper (x' :: xs') (y :: y' :: ys') x of
                  (zs ** fitsPrf) => (zs ** Left fitsPrf)
      Right prf => case mergeHelper (y' :: ys') (x :: x' :: xs') y of
                   (zs ** fitsPrf) => rewrite the (cntX + S (S cntY) = cntY + S (S cntX)) (%runElab natPlusRefl) in
                                      (zs ** Right fitsPrf)
  mergeHelper : .{constraint : Ordered ty to}
             -> {n : Nat}
             -> (xs : OrderedVect (S n) constraint)
             -> {m : Nat}
             -> (ys : OrderedVect (S m) constraint)
             -> (x : ty)
             -> .{auto prfXs : Fits x xs}
             -> .{auto prfYs : Fits x ys}
             -> (ret : OrderedVect (S $ (S n) + (S m)) constraint ** Fits x ret)
  mergeHelper xs ys x {prfXs} {prfYs}
    = case assert_total $ merge' xs ys of
      (zs ** Left fitsPrf) => let _ = fitsTrans prfXs fitsPrf in
                              (x :: zs ** reflexive x)
      (zs ** Right fitsPrf) => let _ = fitsTrans prfYs fitsPrf in
                               (x :: zs ** reflexive x)

export
merge : {constraint : Ordered ty to}
     -> (n : Nat)
     -> OrderedVect n constraint
     -> (m : Nat)
     -> OrderedVect m constraint
     -> OrderedVect (n + m) constraint
merge Z     [] Z     [] = Nil
merge n     v1 Z     [] = rewrite the (n + 0 = n) (%runElab natPlusRefl) in v1
merge Z     [] _     v2 = v2
merge (S _) v1 (S _) v2 = fst $ merge' v1 v2

export
tail : OrderedVect (S n) constraint -> OrderedVect n constraint
tail (_ :: v) = v

export
orderedVectToList : .{constraint : Ordered ty _} -> OrderedVect n constraint -> List ty
orderedVectToList [] = []
orderedVectToList {n = S _} (x :: xs) = x :: (orderedVectToList xs)
