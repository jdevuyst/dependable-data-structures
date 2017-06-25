module Main

import Data.CountedLeftistHeap
import Data.OrderedVect
import Data.MergeList
import Decidable.Order

%default total

-- taken from the Type-Driven Development book
randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
               (seed' `shiftR` 2) :: randoms seed'

-- `cast` crashes on negative and on large numbers
-- large numbers slow down `Decidable.Order.order`
partial
int2nat : Int -> Nat
int2nat i = cast $ abs $ mod i 100000

main : IO ()
main = do putStrLn "Start"
          let l = take 100 $ map (assert_total int2nat) $ randoms 42
          let leftistHeap = foldl (flip insert) emptyHeap l
          let mergeList = foldl CountedMergeList.insert emptyMergeList l
          putStr "Results: "
          putStrLn $ show $ findMin leftistHeap
          putStrLn $ show $ count $ leftistHeap
          putStrLn $ show $ head $ toVect mergeList
          putStrLn "End"
          pure ()
  where
    emptyHeap : {auto constraint : Ordered Nat LTE} -> CountedHeap constraint
    emptyHeap = empty
    emptyMergeList : {auto constraint : Ordered Nat LTE} -> CountedMergeList 1 constraint
    emptyMergeList = empty
    toVect : {constraint : Ordered Nat LTE} -> (cnt : Nat ** Lazy $ MergeList 1 cnt constraint) -> (cnt ** OrderedVect cnt constraint)
    toVect (cnt ** xs) = (cnt ** mergeListToOrderedVect 1 cnt xs)
    head : {constraint : Ordered Nat LTE} -> (cnt ** OrderedVect cnt constraint) -> Maybe Nat
    head (Z ** Nil) = Nothing
    head (_ ** x::xs) = Just x
