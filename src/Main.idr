module Main

-- contrib
import Decidable.Order

-- Fast really_believe_me implementation of Ordered for Int
import Decidable.IntOrder

-- data structures
import Data.LeftistHeap
import Data.OrderedVect
import Data.MergeList
import Data.LazyPairingHeap
import Data.PhysicistsQueue

%default total

-- taken from the Type-Driven Development book
randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
               (seed' `shiftR` 2) :: randoms seed'

namespace CountedOrderedVect
  toVect : {constraint : Ordered Int LTE} -> (cnt : Nat ** Lazy $ MergeList 1 cnt constraint) -> (cnt ** OrderedVect cnt constraint)
  toVect (cnt ** xs) = (cnt ** mergeListToOrderedVect 1 cnt xs)
  head : {constraint : Ordered Int LTE} -> (cnt ** OrderedVect cnt constraint) -> Maybe Int
  head (Z ** Nil) = Nothing
  head (_ ** x::xs) = Just x
  tail : {constraint : Ordered Int LTE} -> (cnt ** OrderedVect cnt constraint) -> (cnt ** OrderedVect cnt constraint)
  tail (Z ** Nil) = (Z ** [])
  tail (S cnt ** x::xs) = (cnt ** xs)

-- Showcase basic operations on the various data structures in this module
-- and verify that proofs are erased as expected:
-- idris --warnreach -p contrib Main.idr -o main && time ./main
main : IO ()
main = do putStrLn "Start"
          let l = take 10000 $ randoms 42
          let leftistHeap = foldl (flip insert) emptyHeap l
          let mergeList = foldl CountedMergeList.insert emptyMergeList l
          let pairingHeap = foldl CountedPairingHeap.insert emptyPairingHeap l
          putStr "Results: "
          putStrLn $ show $ findMin $ deleteMin leftistHeap
          putStrLn $ show $ count $ leftistHeap
          putStrLn $ show $ CountedOrderedVect.head $ tail $ toVect mergeList
          putStrLn $ show $ CountedPairingHeap.findMin $ deleteMin pairingHeap
          putStrLn $ show $ PhysicistsQueue.head $ tail queue
          putStrLn "End"
          pure ()
  where
    emptyHeap : {auto constraint : Ordered Int LTE} -> CountedHeap constraint
    emptyHeap = empty
    emptyMergeList : {auto constraint : Ordered Int LTE} -> CountedMergeList 1 constraint
    emptyMergeList = empty
    emptyPairingHeap : {auto constraint : Ordered Int LTE} -> CountedPairingHeap constraint
    emptyPairingHeap = CountedPairingHeap.empty
    queue : PhysicistsQueue 4 Int
    queue = snoc (snoc (snoc (snoc empty 1) 2) 3) 4