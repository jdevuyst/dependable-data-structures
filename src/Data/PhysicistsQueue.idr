module Data.PhysicistsQueue

import Data.Vect
import Data.VectRankedElem
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

queues : {ty : Type} -> PhysicistsQueue _ ty -> ((size1 : Nat ** Vect size1 ty),
                                                 (size2 : Nat ** Vect size2 ty))
queues (Queue {n} f {m} r) = ((n ** f), (m ** r))

export
data RankedElem : ty -> PhysicistsQueue size ty -> (idx : Nat) -> Type where
  FrontElem : {q : PhysicistsQueue size ty}
           -> {idx : Nat}
           -> RankedElem x (snd $ fst $ queues q) idx
           -> RankedElem x q idx
  BackElem : {q : PhysicistsQueue size ty}
          -> {idx : Nat}
          -> RankedElem x (snd $ snd $ queues q) idx
          -> RankedElem x q (size `minus` S idx)

export
empty : PhysicistsQueue Z _
empty = Queue [] []

lteAddRightLemma : LTE r c -> LTE r (l + c)
lteAddRightLemma {l} {r} {c} smaller
  = lteTransitive smaller cLTElc
    where cLTElc : LTE c (l + c)
          cLTElc = rewrite plusCommutative l c in
                   lteAddRight {m = l} c

partial -- totality checker bug?
minusPlusEqualsPlusMinus : (l, c, r: Nat) -> LTE r c -> LTE r (l + c) -> (l + c) - r = l + (c - r)
minusPlusEqualsPlusMinus Z _ _ _ _ = Refl
minusPlusEqualsPlusMinus (S _) Z Z _ _ = Refl
minusPlusEqualsPlusMinus (S _) (S Z) Z _ _ = Refl
-- minusPlusEqualsPlusMinus l Z Z _ _ = rewrite sym $ minusZeroRight (l + Z) in Refl
-- minusPlusEqualsPlusMinus l (S Z) Z _ _ = rewrite sym $ minusZeroRight (l + 1) in Refl
minusPlusEqualsPlusMinus _ Z (S Z) _ _ impossible
minusPlusEqualsPlusMinus l (S c) (S r) smaller _
  = let smaller' = fromLteSucc smaller in
    rewrite sym $ plusSuccRightSucc l c in
    minusPlusEqualsPlusMinus l c r smaller' (lteAddRightLemma smaller')

make_ : {n : Nat}
     -> (f : Vect n ty)
     -> {m : Nat}
     -> (r : Vect m ty)
     -> (ret : PhysicistsQueue (n + m) ty
         ** ({x : ty} -> {idx : Nat} -> RankedElem x f idx -> RankedElem x ret idx,
             {x : ty} -> {idx : Nat} -> RankedElem x r idx -> RankedElem x ret (n + m `minus` S idx)))
make_ {n} f {m} r with (order {to = LTE} m n)
  | Left _ = (Queue f r ** (FrontElem, BackElem))
  | Right _ = let (reversed ** rProj) = rev_ r
                  (f' ** (fProj, reversedProj)) = f `concat_` reversed in
              rewrite sym $ plusZeroRightNeutral (n + m) in
              (Queue f' [] ** (FrontElem . fProj,
                               rewrite plusZeroRightNeutral (n + m) in
                               FrontElem . (proj $ reversedProj . rProj)))
              where proj : {f' : Vect (n + m) ty}
                        -> (trans : {x : ty} -> {idx : Nat} -> RankedElem x r idx -> RankedElem x f' (n + (m `minus` S idx)))
                        -> {x : ty} -> {idx' : Nat} -> RankedElem x r idx'
                        -> RankedElem x f' (n + m `minus` S idx')
                    proj {f'} trans {idx'} elem = let smaller = indexSmallerThanSize elem
                                                      elem' = trans elem in
                                                  rewrite assert_total $
                                                          minusPlusEqualsPlusMinus n m (S idx') smaller (lteAddRightLemma smaller) in
                                                  elem'

export
snoc_ : (q : PhysicistsQueue size ty) -> (x : ty)
     -> (ret : PhysicistsQueue (S size) ty
         ** ({x : ty} -> {idx : Nat} -> RankedElem x q idx -> RankedElem x ret idx,
             RankedElem x ret size))
snoc_ (Queue {n} f {m} r) x = rewrite plusSuccRightSucc n m in
                              let (ret ** (fProj, rProj)) = make_ f (x::r) in
                              (ret ** ((\el => case el of
                                               (FrontElem el) => fProj el
                                               (BackElem el {idx}) => rewrite sym $ lemma n m (S idx) in
                                                                      rProj $ There el),
                                       rewrite sym $ minusZeroRight (n + m) in
                                       rewrite sym $ lemma n m Z in
                                       rProj Here))
                              where lemma : (l, c, r : Nat) -> l + S c `minus` S r = l + c `minus` r
                                    lemma Z Z _ = Refl
                                    lemma Z (S _) _ = Refl
                                    lemma (S l) c r = rewrite plusSuccRightSucc l c in Refl

export
snoc : PhysicistsQueue size ty -> ty -> PhysicistsQueue (S size) ty
snoc q x = fst $ snoc_ q x

export
head_ : (q : PhysicistsQueue (S _) ty) -> (x : ty ** RankedElem x q Z)
head_ (Queue (x :: xs) ys) = (x ** FrontElem Here)

export
head : PhysicistsQueue (S _) ty -> ty
head q = fst $ head_ q

export
tail_ : (q : PhysicistsQueue (S size) ty)
     -> (ret : PhysicistsQueue size ty
         ** {x : ty} -> {idx : Nat} -> RankedElem x q (S idx) -> RankedElem x ret idx)
tail_ (Queue (_::fs) r)
  = let (ret ** (fProj, rProj)) = make_ fs r in
    (ret ** \el =>
      case toPattern el of
      (Z ** (_, prf)) => void $ SIsNotZ prf
      (S _ ** (FrontElem (There x), prf)) => rewrite toPredEq prf in fProj x
      (_ ** (BackElem x, prf)) => rewrite toMinusSuccPredEq $ toPredEq prf in rProj x)
    where toPattern : {q : PhysicistsQueue (S _) ty}
                   -> {i : Nat}
                   -> RankedElem x q (S i)
                   -> (i' ** (RankedElem x q i', S i = i'))
          toPattern {i} el = (S i ** (el, Refl))
          toPredEq : S i = i' -> i = pred i'
          toPredEq prf = cong {f = Nat.pred} prf
          toMinusSuccPredEq : c = pred (x + y `minus` z) -> c = x + y `minus` S z
          toMinusSuccPredEq {x} {y} {z} prf = rewrite minusSuccPred (x + y) z in prf

export
tail : PhysicistsQueue (S size) ty -> PhysicistsQueue size ty
tail q = fst $ tail_ q