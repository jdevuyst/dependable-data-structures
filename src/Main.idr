module Main

import Decidable.Order
import Data.LeftistHeap

canHasModel : {auto constraint : Ordered Nat LTE} -> Heap constraint 1
canHasModel = deleteMin $ insert 2 $ insert 1 empty

main : IO ()
main = do let h = canHasModel
          putStrLn $ show $ findMin h
          pure ()