module Main

import Decidable.Order
import Data.LeftistHeap

%default total

insert' : {constraint : Ordered a rel} -> (n : Nat ** Heap constraint n) -> a -> (m : Nat ** Heap constraint m)
insert' (n ** h) el = (S n ** insert el h)

emptyModel : {auto constraint : Ordered Nat LTE} -> (n : Nat ** Heap constraint n)
emptyModel = (Z ** empty)

min : {auto constraint : Ordered Nat LTE} -> (m : Nat ** Heap constraint m) -> Nat
min (Z ** _) = Z
min ((S _) ** h) = findMin h

-- taken from the Type-Driven Development book
randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
               (seed' `shiftR` 2) :: randoms seed'

-- `cast` crashes on negative and on large numbers
-- large numbers slow down `Decidable.Orderorder`
partial
int2nat : Int -> Nat
int2nat i = cast $ abs $ mod i 100000

main : IO ()
main = do let l = take 10000 $ map (assert_total int2nat) $ randoms 42
          putStrLn "Start"
          let h = foldl insert' emptyModel l
          putStr "Result: "
          putStrLn $ show $ min h
          -- putStr "Count: "
          -- putStrLn $ show $ count $ snd $ h
          putStrLn "End"
          pure ()