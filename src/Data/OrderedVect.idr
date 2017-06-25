module Data.OrderedVect

import Decidable.Order

%default total

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
  export
  head : .{constraint : Ordered ty to} -> OrderedVect (S _) constraint -> ty
  head (x :: _) = x
  public export
  data Fits : {constraint : Ordered ty to}
           -> ty
           -> OrderedVect n constraint
           -> Type where
    FitsNil : .{constraint : Ordered ty to}
           -> .(x : ty)
           -> .(v : OrderedVect Z constraint)
           -> Fits x v
    FitsNext : .{constraint : Ordered ty to}
            -> .(x : ty)
            -> .(v : OrderedVect (S _) constraint)
            -> .{auto prf : to x (head v)}
            -> Fits x v

%name OrderedVect xs,ys,zs

fitsTrans : {constraint : Ordered ty to} -> (to x y) -> (Fits {constraint} y v) -> Fits {constraint} x v
fitsTrans rel (FitsNil y v) = FitsNil x v
fitsTrans {x} rel (FitsNext {prf} y v) = let prf = transitive x y (head v) rel prf in
                                         FitsNext {prf} x v

fitsTrans' : (Fits {constraint} x v1) -> Fits {constraint} (head v1) v2 -> Fits {constraint} x v2
fitsTrans' (FitsNext {prf = prf} x v) fits2 = fitsTrans prf fits2

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
                        Left prf => ([x, y] ** Left (FitsNext {prf = reflexive x} x [x, y]))
                        Right prf => let ret = (::) {prf = FitsNext y [x]} y [x] in
                                     (ret ** Right (FitsNext {prf = reflexive y} y ret))
  merge' {m} [x] (y :: ys) = rewrite sym $ plusZeroRightNeutral m in
                             rewrite plusSuccRightSucc m Z in
                             case assert_total $ merge' (y :: ys) [x] of
                             (ref ** Left prf) => (ref ** Right prf)
                             (ref ** Right prf) => (ref ** Left prf)
  merge' {n = S cntX} ((::) {prf = fits_x_xs} x xs) [y]
    = case order {to} x y of
      Left prf => case mergeHelper xs [y] x fits_x_xs prf of
                  (zs ** fitsPrf) => (zs ** Left fitsPrf)
      Right prf => let ret = (::) {prf = FitsNext y (x :: xs)} y (x :: xs) in
                   rewrite sym $ plusSuccRightSucc cntX Z in
                   rewrite plusZeroRightNeutral cntX in
                   (ret ** Right (FitsNext {prf = reflexive y} y ret))
  merge' ((::) {n = S cntX} {prf = fits_x_xs'} x (x' :: xs'))
        ((::) {n = S cntY} {prf = fits_y_ys'} y (y' :: ys'))
    = case order {to} x y of
      Left prf => case mergeHelper (x' :: xs') (y :: y' :: ys') x fits_x_xs' prf of
                  (zs ** fitsPrf) => (zs ** Left fitsPrf)
      Right prf => case mergeHelper (y' :: ys') (x :: x' :: xs') y fits_y_ys' prf of
                   (zs ** fitsPrf) => rewrite plusCommutative cntX (S $ S $ cntY) in
                                      rewrite plusSuccRightSucc (S $ S cntY) cntX in
                                      rewrite plusSuccRightSucc (S cntY) (S cntX) in
                                      (zs ** Right fitsPrf)
  mergeHelper : .{constraint : Ordered ty to}
             -> {n : Nat}
             -> (xs : OrderedVect (S n) constraint)
             -> {m : Nat}
             -> (ys : OrderedVect (S m) constraint)
             -> (x : ty)
             -> .(Fits x xs)
             -> .(to x (head ys))
             -> (ret : OrderedVect (S $ (S n) + (S m)) constraint ** Fits x ret)
  mergeHelper xs ys x prfXs prfYs
    = case assert_total $ merge' xs ys of
      (zs ** Left fitsPrf) => let prf = fitsTrans' prfXs fitsPrf
                                  ret = x :: zs in
                               (ret ** FitsNext x {prf = reflexive x} ret)
      (zs ** Right fitsPrf) => let prf = fitsTrans prfYs fitsPrf
                                   ret = x :: zs in
                               (ret ** FitsNext x {prf = reflexive x} ret)

export
merge : {constraint : Ordered ty to}
     -> (n : Nat)
     -> OrderedVect n constraint
     -> (m : Nat)
     -> OrderedVect m constraint
     -> OrderedVect (n + m) constraint
merge Z     [] Z     [] = Nil
merge n     v1 Z     [] = rewrite plusZeroRightNeutral n in v1
merge Z     [] _     v2 = v2
merge (S _) v1 (S _) v2 = case merge' v1 v2 of
                          (ret ** _) => ret

export
tail : OrderedVect (S n) constraint -> OrderedVect n constraint
tail (_ :: v) = v

export
orderedVectToList : .{constraint : Ordered ty _} -> OrderedVect n constraint -> List ty
orderedVectToList [] = []
orderedVectToList {n = S _} (x :: xs) = x :: (orderedVectToList xs)