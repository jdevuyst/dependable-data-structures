module Data.MergeList

import Decidable.Order
import Data.OrderedVect

%default total

export
data MergeList : (rank : Nat) -> (cnt : Nat) -> (constraint : Ordered ty to) -> Type where
  Nil : MergeList _ Z _
  Skip : (next : MergeList (n + n) cnt constraint)
      -> MergeList n cnt constraint
  (::) : OrderedVect n constraint
      -> .{cnt : Nat}
      -> (next : MergeList (n + n) cnt constraint)
      -> MergeList n (n + cnt) constraint

%name MergeList xs,ys,zs

insertVect : {constraint : Ordered ty to}
          -> {n : Nat}
          -> {cnt : Nat}
          -> MergeList n cnt constraint
          -> OrderedVect n constraint
          -> MergeList n (cnt + n) constraint
insertVect {n} {constraint} {cnt=Z} Nil v
  = rewrite rewriteType in v :: Nil
      where rewriteType : MergeList n n constraint = MergeList n (n + 0) constraint
            rewriteType = rewrite sym $ plusZeroRightNeutral n in Refl
insertVect {n} {cnt} (Skip next) v = rewrite plusCommutative cnt n in
                                     v :: next
insertVect {n} ((::) v next {cnt}) v'
  = rewrite sym $ plusCommutative cnt n in
    rewrite sym $ plusAssociative cnt n n in
    Skip $ insertVect next (merge n v n v')

export
empty : .{auto constraint : Ordered ty to} -> MergeList 1 0 constraint
empty = []

export
insert : .{constraint : Ordered ty to}
      -> {cnt : Nat}
      -> MergeList 1 cnt constraint
      -> ty
      -> MergeList 1 (cnt + 1) constraint
insert l x = insertVect l [x]

export
mergeListToOrderedVect : .{constraint : Ordered ty _}
                      -> (n : Nat)
                      -> (cnt : Nat)
                      -> MergeList n cnt constraint
                      -> OrderedVect cnt constraint
mergeListToOrderedVect _ _ Nil = []
mergeListToOrderedVect n cnt (Skip next) = mergeListToOrderedVect (n + n) cnt next
mergeListToOrderedVect n (n + nextCnt) (v :: next)
  = merge n v nextCnt $ mergeListToOrderedVect (n + n) nextCnt next

namespace CountedMergeList
  public export
  CountedMergeList : (n : Nat) -> (constraint: Ordered to rel) -> Type
  CountedMergeList n constraint = (cnt : Nat ** Lazy $ MergeList n cnt constraint)

  export
  empty : CountedMergeList 1 constraint
  empty = (Z ** empty)

  export
  insert : .{constraint : Ordered ty to} -> CountedMergeList 1 constraint -> ty -> CountedMergeList 1 constraint
  insert (cnt ** xs) x = (cnt + 1 ** insert xs x)