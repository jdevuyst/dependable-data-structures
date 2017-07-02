module Data.PhysicistsQueue

import Data.Vect
import Decidable.Order

%default total

export
data PhysicistsQueue : (size : Nat) -> (ty : Type) -> Type where
  Queue : {n : Nat}
       -> (f : Vect n ty)
       -> {m : Nat}
       -> (r : Vect m ty)
       -> {auto invariant : LTE m n}
       -> PhysicistsQueue (n + m) ty

export
empty : PhysicistsQueue Z _
empty = Queue [] []

queue : {n : Nat}
     -> (f : Vect n ty)
     -> {m : Nat}
     -> (r : Vect m ty)
     -> PhysicistsQueue (n + m) ty
queue {n} f {m} r with (order {to = LTE} n m)
  | Left ltePrf = rewrite sym $ plusZeroRightNeutral (n + m) in
                  Queue (f ++ reverse r) []
  | Right invariant = Queue f r

export
snoc : PhysicistsQueue size ty -> ty -> PhysicistsQueue (S size) ty
snoc (Queue {n} f {m} r) x = rewrite plusSuccRightSucc n m in
                             queue f (x :: r)

export
head : PhysicistsQueue (S _) ty -> ty
head (Queue (x :: _) _) = x

export
tail : PhysicistsQueue (S size) ty -> PhysicistsQueue size ty
tail (Queue {n = S _} (_ :: f) {m} r) = queue f r