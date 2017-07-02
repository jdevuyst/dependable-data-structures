module Data.LazyPairingHeap

import Decidable.Order

%default total

mutual
  public export
  data LazyPairingHeap : Nat -> Ordered ty to -> Type where
    Empty : .{auto constraint : Ordered ty to} -> LazyPairingHeap Z constraint
    Tree : .{constraint : Ordered ty to}
        -> (x : ty)
        -> {leftCnt : Nat}
        -> (l : LazyPairingHeap leftCnt constraint)
        -> .{leftFits : Fits x l}
        -> {rightCnt : Nat}
        -> (r : Lazy $ LazyPairingHeap rightCnt constraint)
        -> .{rightFits : Fits x r}
        -> LazyPairingHeap (S (leftCnt + rightCnt)) constraint

  export
  findMin : {constraint : Ordered ty _} -> LazyPairingHeap (S _) constraint -> ty
  findMin (Tree x l r) = x

  export
  data Fits : {constraint : Ordered ty _} -> ty -> LazyPairingHeap _ constraint -> Type where
    FitsEmpty : {constraint : Ordered ty _}
             -> (x : ty)
             -> (h : LazyPairingHeap Z constraint)
             -> Fits x h
    FitsTree : {constraint : Ordered ty to}
            -> (x : ty)
            -> (h : LazyPairingHeap (S _) constraint)
            -> {ltePrf : to x (findMin h)}
            -> Fits x h

fitsSubst : {h1 : LazyPairingHeap (S _) constraint}
         -> {h2 : LazyPairingHeap (S _) constraint}
         -> Fits x h1
         -> findMin h2 = findMin h1
         -> Fits x h2
fitsSubst {h2} (FitsTree {ltePrf} x h1) eqPrf
  = FitsTree {ltePrf = rewrite eqPrf in ltePrf} x h2

mutual
  link : .{constraint : Ordered ty to}
      -> .{cnt1 : Nat} -> (h1 : LazyPairingHeap (S cnt1) constraint)
      -> .{cnt2 : Nat} -> (h2 : LazyPairingHeap (S cnt2) constraint)
      -> .{ltePrf : to (findMin h1) (findMin h2)}
      -> (ret : LazyPairingHeap ((S cnt1) + (S cnt2)) constraint ** findMin ret = findMin h1)
  link {cnt1} {cnt2} {ltePrf} h1@(Tree {leftFits = _} {rightFits} x Empty r) h2
    = rewrite plusCommutative cnt1 (S cnt2) in
      let leftFits = FitsTree {ltePrf} (findMin h1) h2
          ret = Tree {leftFits} {rightFits} (findMin h1) h2 r in
          (ret ** Refl)
  link {constraint} {ltePrf} h1 {cnt2} h2 with (h1)
    | Tree {leftFits} {rightFits} {leftCnt} {rightCnt} x l r
      = rewrite sym $ plusAssociative leftCnt rightCnt (S cnt2) in
        rewrite plusCommutative rightCnt (S cnt2) in
        rewrite plusAssociative leftCnt (S cnt2) rightCnt in
        rewrite plusCommutative leftCnt (S cnt2) in
        rewrite sym $ xFindMin in
        let (merged ** fitsPrf) = merge' {lbound = findMin h1}
                                         {fits1 = FitsTree {ltePrf = rewrite xFindMin in ltePrf} (findMin h1) h2}
                                         h2
                                         {fits2 = rewrite xFindMin in leftFits}
                                         l
            (merged' ** fitsPrf') = merge' {lbound = findMin h1}
                                           {fits1 = fitsPrf}
                                           merged
                                           {fits2 = rewrite xFindMin in rightFits}
                                           r
            ret = Tree {leftFits = FitsEmpty (findMin h1) Empty}
                       {rightFits = fitsPrf'}
                       (findMin h1) Empty merged' in
        (ret ** Refl)
        where xFindMin : findMin h1 = x
              xFindMin = really_believe_me ()

  merge' : .{constraint : Ordered ty to}
        -> {cnt1 : Nat} -> (h1 : LazyPairingHeap cnt1 constraint)
        -> {cnt2 : Nat} -> (h2 : LazyPairingHeap cnt2 constraint)
        -> .{lbound : ty} -> .{fits1 : Fits lbound h1} -> .{fits2 : Fits lbound h2}
        -> (ret : LazyPairingHeap (cnt1 + cnt2) constraint ** Fits lbound ret)
  merge' {fits2} Empty h = (h ** fits2)
  merge' {cnt1} {fits1} h Empty = rewrite plusZeroRightNeutral cnt1 in (h ** fits1)
  merge' {to} {fits1} {fits2} {cnt1 = S n} {cnt2 = S m} h1 h2 with (order {to} (findMin h1) (findMin h2))
    | Left ltePrf = let (ret ** eqPrf) = assert_total $ link {ltePrf} h1 h2 in
                    (ret ** fitsSubst fits1 eqPrf)
    | Right ltePrf = rewrite plusCommutative n (S m) in
                     rewrite plusSuccRightSucc m n in
                     let (ret ** eqPrf) = assert_total $ link {ltePrf} h2 h1 in
                     (ret ** fitsSubst fits2 eqPrf)

export
merge : .{constraint : Ordered ty to}
     -> {cnt1 : Nat} -> LazyPairingHeap cnt1 constraint
     -> {cnt2 : Nat} -> LazyPairingHeap cnt2 constraint
     -> LazyPairingHeap (cnt1 + cnt2) constraint
merge Empty h = h
merge {cnt1} h Empty = rewrite plusZeroRightNeutral cnt1 in h
merge {constraint} {ty} {to} {cnt1 = S n} {cnt2 = S m} h1 h2
  = let (lbound ** (fits1, fits2)) = proofs in
        fst $ merge' {lbound} {fits1} {fits2} h1 h2
    where proofs : (lbound : ty ** (Fits lbound h1, Fits lbound h2))
          proofs with (order {to} (findMin h1) (findMin h2))
            | Left ltePrf = let x = findMin h1 in
                            (x ** (FitsTree {ltePrf = reflexive x} x h1,
                                   FitsTree {ltePrf} x h2))
            | Right ltePrf = let x = findMin h2 in
                             (x ** (FitsTree {ltePrf} x h1,
                                    FitsTree {ltePrf = reflexive x} x h2))

export
deleteMin : .{constraint : Ordered ty to} -> LazyPairingHeap (S cnt) constraint -> LazyPairingHeap cnt constraint
deleteMin (Tree _ l r) = merge l r

singleton : {ty : Type} -> {constraint : Ordered ty to} -> ty -> LazyPairingHeap 1 constraint
singleton x = Tree {leftFits = FitsEmpty x Empty} {rightFits = FitsEmpty x Empty}
                   x Empty Empty

export
insert : .{constraint : Ordered ty to} -> {cnt : Nat} -> LazyPairingHeap cnt constraint -> ty -> LazyPairingHeap (S cnt) constraint
insert {cnt} h x = rewrite sym $ plusZeroRightNeutral cnt in
                   rewrite plusSuccRightSucc cnt Z in
                   merge h (singleton x)

namespace CountedPairingHeap
  public export
  CountedPairingHeap : (constraint : Ordered ty to) -> Type
  CountedPairingHeap constraint = (cnt : Nat ** LazyPairingHeap cnt constraint)

  export
  empty : CountedPairingHeap _
  empty = (Z ** Empty)

  export
  findMin : .{constraint : Ordered ty to} -> CountedPairingHeap constraint -> Maybe ty
  findMin (Z ** _) = Nothing
  findMin (S _ ** (Tree x _ _)) = Just x

  export
  deleteMin : CountedPairingHeap constraint -> CountedPairingHeap constraint
  deleteMin (Z ** h) = (Z ** h)
  deleteMin (S cnt ** h) = (cnt ** deleteMin h)

  export
  insert : .{constraint : Ordered ty to} -> CountedPairingHeap constraint -> ty -> CountedPairingHeap constraint
  insert (cnt ** h) x = ((S cnt) ** insert h x)