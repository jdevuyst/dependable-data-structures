module Data.CountedLeftistHeap

import Data.LeftistHeap
import Decidable.Order

%default total

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