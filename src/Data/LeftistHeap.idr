module Data.LeftistHeap

import Decidable.Order

%default total

mutual
  export
  data Heap : .(constraint : Ordered a rel) -> .(count : Nat) -> Type where
       Empty : Heap _ Z
       Node : (n : Nat)
           -> (value : a)
           -> {countLeft : Nat}
           -> (left : Heap constraint countLeft)
           -> {countRight : Nat}
           -> (right : Heap constraint countRight)
           -> .{auto fitsLeft : Fits value left}
           -> .{auto fitsRight : Fits value right}
           -> .{auto leftistPrf : LTE (rank right) (rank left)}
           -> .{auto rankPrf : n = S $ rank right}
           -> Heap constraint (S $ countLeft + countRight)

  Fits : {constraint : Ordered a rel} -> a -> Heap constraint cnt -> Type
  Fits {cnt = Z} _ _ = ()
  Fits {cnt = S _} x h = rel x (findMin h)

  rank : Heap _ _ -> Nat
  rank Empty = Z
  rank (Node _ _ _ right) = S $ rank right

  export
  findMin : .{constraint : Ordered a _} -> Heap constraint (S _) -> a
  findMin (Node _ value _ _) = value

export
empty : Heap _ Z
empty = Empty

makeFit : .{constraint : Ordered a rel}
       -> .(fitsValue : a)
       -> (value : a)
       -> {count1 : Nat}
       -> {count2 : Nat}
       -> (h1 : Heap constraint count1)
       -> (h2 : Heap constraint count2)
       -> .{auto fits1 : Fits value h1}
       -> .{auto fits2 : Fits value h2}
       -> .{auto relPrf : rel fitsValue value}
       -> Subset (Heap constraint (S $ count1 + count2)) (Fits fitsValue)
makeFit {count1} {count2} {relPrf} fitsValue value h1 h2 with (order {to = LTE} (rank h1) (rank h2))
  | (Left _) = rewrite plusCommutative count1 count2 in
               Element (Node _ value h2 h1) relPrf
  | (Right _) = Element (Node _ value h1 h2) relPrf

covering
mergeHelper : .{constraint : Ordered a rel}
           -> .{value : a}
           -> {count1 : Nat}
           -> {count2 : Nat}
           -> (h1 : Heap constraint count1)
           -> (h2 : Heap constraint count2)
           -> .{auto fits1 : Fits value h1}
           -> .{auto fits2 : Fits value h2}
           -> Subset (Heap constraint (count1 + count2)) (Fits value)
mergeHelper Empty Empty = Element Empty ()
mergeHelper {fits1} h@(Node {countLeft} {countRight} n _ _ _) Empty = rewrite plusZeroRightNeutral (countLeft + countRight) in Element h fits1
mergeHelper {fits2} Empty h@(Node {countLeft} {countRight} n _ _ _) = Element h fits2
mergeHelper {value} {rel}
            (Node {countLeft = countLeft1} {countRight = countRight1} _ value1 left1 right1)
            (Node {countLeft = countLeft2} {countRight = countRight2} _ value2 left2 right2)
  = case order {to = rel} value1 value2 of
    Left orderPrf => rewrite sym $ plusAssociative countLeft1 countRight1 (S $ countLeft2 + countRight2) in
                     let (Element mergedHeap fitsMergedHeap) = mergeHelper {value = value1} right1 (Node _ value2 left2 right2) in
                     makeFit value value1 left1 mergedHeap
    Right orderPrf => rewrite sym $ plusSuccRightSucc (countLeft1 + countRight1) (countLeft2 + countRight2) in
                      rewrite plusCommutative countLeft2 countRight2 in
                      rewrite plusAssociative (countLeft1 + countRight1) countRight2 countLeft2 in
                      let (Element mergedHeap fitsMergedHeap) = mergeHelper {value = value2} (Node _ value1 left1 right1) right2 in
                      makeFit value value2 mergedHeap left2

export
merge : .{constraint : Ordered a rel}
     -> {count1 : Nat} -> {count2 : Nat}
     -> (h1 : Heap constraint count1) -> (h2 : Heap constraint count2)
     -> Heap constraint (count1 + count2)
merge Empty Empty = Empty
merge {count1} h Empty = rewrite plusZeroRightNeutral count1 in h
merge Empty h = h
merge h1@(Node _ _ _ _) h2@(Node _ _ _ _)
  = assert_total $ case order {to = rel} (findMin h1) (findMin h2) of
    Left orderPrf => case mergeHelper {value = (findMin h1)} h1 h2 {fits1 = reflexive (findMin h1)} of
                     Element h _ => h
    Right orderPrf => case mergeHelper {value = (findMin h2)} h1 h2 {fits2 = reflexive (findMin h2)} of
                      Element h _ => h

export
insert : .{constraint : Ordered a _} -> .{n : Nat} -> a -> Heap constraint n -> Heap constraint (S n)
insert value heap = merge (Node 1 value Empty Empty) heap

export
deleteMin : .{constraint : Ordered a _} -> {n : Nat} -> Heap constraint (S n) -> Heap constraint n
deleteMin (Node _ _ left right) = merge left right

namespace OrderedLeftistHeap
  export
  data CountedHeap : .(constraint : Ordered a rel) -> Type where
       MkCountedHeap : (n : Nat) -> (Heap constraint n) -> CountedHeap constraint

  export
  empty : CountedHeap _
  empty = MkCountedHeap Z empty

  export
  count : CountedHeap _ -> Nat
  count (MkCountedHeap n _) = n

  export
  findMin : .{constraint : Ordered ty _} -> CountedHeap constraint -> Maybe ty
  findMin (MkCountedHeap Z _) = Nothing
  findMin (MkCountedHeap (S _) h) = Just $ findMin h

  export
  merge : .{constraint : Ordered _ _} -> CountedHeap constraint -> CountedHeap constraint -> CountedHeap constraint
  merge (MkCountedHeap count1 h1) (MkCountedHeap count2 h2) = MkCountedHeap (count1 + count2) (merge h1 h2)

  export
  insert : .{constraint : Ordered ty _} -> ty -> CountedHeap constraint -> CountedHeap constraint
  insert a (MkCountedHeap n h) = MkCountedHeap (S n) (insert a h)

  export
  deleteMin : .{constraint : Ordered ty _} -> CountedHeap constraint -> CountedHeap constraint
  deleteMin orig@(MkCountedHeap Z h) = orig
  deleteMin (MkCountedHeap (S n) h) = MkCountedHeap n (deleteMin h)
