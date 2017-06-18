module Main

import Data.CountedLeftistHeap
import Data.OrderedVect
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
          let l = take 10000 $ map (assert_total int2nat) $ randoms 42
          let h = foldl (flip insert) emptyModel l
          let merged = merge 2 orderedVect 2 orderedVect
          putStr "Results: "
          putStrLn $ show $ findMin h
          putStrLn $ show $ count $ h
          putStrLn $ show $ head $ tail $ tail merged
          putStrLn "End"
          pure ()
  where
    emptyModel : {auto constraint : Ordered Nat LTE} -> (CountedHeap constraint)
    emptyModel = empty
    orderedVect : {auto constraint : Ordered Nat LTE} -> (OrderedVect 2 constraint)
    orderedVect = (::) {to=LTE} {prf = FitsNext 0 [1]} 0 ((::) {to=LTE} {prf=FitsNil 1 Nil} 1 Nil)