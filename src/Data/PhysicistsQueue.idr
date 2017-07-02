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
       -> .{auto invariant : LTE m n}
       -> PhysicistsQueue (n + m) ty

export
empty : PhysicistsQueue Z _
empty = Queue [] []

make : {n : Nat}
    -> (f : Vect n ty)
    -> {m : Nat}
    -> (r : Vect m ty)
    -> PhysicistsQueue (n + m) ty
make {n} f {m} r with (order {to = LTE} m n)
  | Left invariant = Queue f r
  | Right ltePrf = rewrite sym $ plusZeroRightNeutral (n + m) in
                   Queue (f ++ reverse r) []

export
snoc : PhysicistsQueue size ty -> ty -> PhysicistsQueue (S size) ty
snoc (Queue {n} f {m} r) x = rewrite plusSuccRightSucc n m in
                             make f (x :: r)

export
head : PhysicistsQueue (S _) ty -> ty
head (Queue (x :: _) _) = x

export
tail : PhysicistsQueue (S size) ty -> PhysicistsQueue size ty
tail (Queue {n = S _} (_ :: f) {m} r) = make f r

data Elem : type -> PhysicistsQueue _ type -> (distance : Nat) -> Type where
  Here : Elem (head queue) queue Z
  There : Elem x (tail queue) distance
       -> Elem x queue (S distance)

tailShifts : Elem x queue (S distance) -> Elem x (tail queue) distance
tailShifts {queue = _} (There elem) = elem