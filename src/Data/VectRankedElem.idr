module VectRankedElem

import Data.Vect
import Decidable.Order

%default total

public export
data RankedElem : ty -> Vect _ ty -> (idx : Nat) -> Type where
  Here : {v : Vect (S _) ty} -> RankedElem (head v) v Z
  There : RankedElem a xs idx -> RankedElem a (x::xs) (S idx)

export
indexSmallerThanSize : {v : Vect size ty} -> {idx : Nat} -> RankedElem x v idx -> LT idx size
indexSmallerThanSize {size = Z} _ impossible
indexSmallerThanSize {size = S len} Here = shift Z len zeroAlwaysSmaller
indexSmallerThanSize {size = S len} {v = (x::xs)} {idx = S n} (There elem)
  = shift (S n) len $ indexSmallerThanSize elem

export
Uninhabited (RankedElem _ [] _) where
  uninhabited _ impossible

export
cons_ : (x : ty) -> (v : Vect size ty)
     -> (ret : Vect (S size) ty
         ** ({a : ty} -> {n : Nat} -> RankedElem a v n -> RankedElem a ret (S n),
             RankedElem x ret Z))
cons_ x [] = ([x] ** (absurd, Here))
cons_ x (y::ys) = (x::y::ys ** (f, Here))
                  where f : {a : ty} -> {n : Nat} -> RankedElem a (y::ys) n -> RankedElem a (x::y::ys) (S n)
                        f elem = There elem

export
cons : ty -> Vect size ty -> Vect (S size) ty
cons x v = fst $ cons_ x v

export
concat_ : {size1, size2 : Nat}
       -> (v1 : Vect size1 ty) -> (v2 : Vect size2 ty)
       -> (ret : Vect (size1 + size2) ty
           ** ({a : ty} -> {n : Nat} -> RankedElem a v1 n -> RankedElem a ret n,
               {a : ty} -> {n : Nat} -> RankedElem a v2 n -> RankedElem a ret (size1 + n)))
concat_ [] ys = (ys ** (absurd, id))
concat_ {size1} xs [] = rewrite plusZeroRightNeutral size1 in
                        (xs ** (id, absurd))
concat_ (x::xs) (y::ys) = let (ret ** (f, g)) = xs `concat_` (y::ys) in
                          (x :: ret ** (ff f, gg g))
                          where ff : {ret : Vect (size1 + size2) ty}
                                  -> ({a : ty} -> {n : Nat} -> RankedElem a xs n -> RankedElem a ret n)
                                  -> {a : ty} -> {n : Nat} -> (RankedElem a (x::xs) n -> RankedElem a (x::ret) n)
                                ff f Here = Here
                                ff f (There elem) = There $ f elem
                                gg : {ret : Vect (size1 + size2) ty}
                                  -> ({a : ty} -> {n : Nat} -> RankedElem a (y::ys) n -> RankedElem a ret (size1 + n))
                                  -> {a : ty} -> {n : Nat} -> (RankedElem a (y::ys) n -> RankedElem a (x::ret) (S $ size1 + n))
                                gg g elem = There $ g elem

export
concat : {size1, size2 : Nat} -> Vect size1 ty -> Vect size2 ty -> Vect (size1 + size2) ty
concat v1 v2 = fst $ concat_ v1 v2

export
rev_ : {size : Nat} -> (orig : Vect size ty)
    -> (ret : Vect size ty ** {a : ty} -> {n : Nat} -> RankedElem a orig n -> RankedElem a ret (size `minus` (S n)))
rev_ [] = ([] ** absurd)
rev_ ((::) {len} x xs) = rewrite plusCommutative 1 len in
                         let (sx ** h) = rev_ xs
                             (ret ** (f, g)) = sx `concat_` [x] in
                         (ret ** fgh f g h)
                         where fgh : ({a : ty} -> {n : Nat} -> RankedElem a sx n -> RankedElem a ret n)
                                  -> ({a : ty} -> {n : Nat} -> RankedElem a [x] n -> RankedElem a ret (len + n))
                                  -> ({a : ty} -> {n : Nat} -> RankedElem a xs n -> RankedElem a sx (len `minus` (S n)))
                                  -> {a : ty} -> {n : Nat} -> RankedElem a (x::xs) n -> RankedElem a ret (len `minus` n)
                               fgh f g h Here = rewrite minusZeroRight len in
                                                rewrite sym $ plusZeroRightNeutral len in
                                                g Here
                               fgh f g h (There elem) = f $ h elem

export
rev : {size : Nat} -> Vect size ty -> Vect size ty
rev v = fst $ rev_ v