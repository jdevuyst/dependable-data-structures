module Main

import Data.CountedLeftistHeap
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
          putStr "Result: "
          putStrLn $ show $ findMin h
          putStr "Count: "
          putStrLn $ show $ count $ h
          putStrLn "End"
          pure ()
  where
    emptyModel : {auto constraint : Ordered Nat LTE} -> (CountedHeap constraint)
    emptyModel = empty