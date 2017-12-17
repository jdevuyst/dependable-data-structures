module Data.Queue

import Data.Vect
import Data.VectRankedElem
import Decidable.Order

%default total

export
data Queue : (size : Nat) -> (ty : Type) -> Type where
  MkQueue : {n : Nat}
         -> (f : Vect n ty)
         -> {m : Nat}
         -> (r : Vect m ty)
         -> .{auto invariant : LTE m n}
         -> Queue (n + m) ty

queues : {ty : Type} -> Queue _ ty -> ((size1 : Nat ** Vect size1 ty),
                                       (size2 : Nat ** Vect size2 ty))
queues (MkQueue {n} f {m} r) = ((n ** f), (m ** r))

export
data RankedElem : ty -> Queue size ty -> (idx : Nat) -> Type where
  FrontElem : {q : Queue size ty}
           -> {idx : Nat}
           -> RankedElem x (snd $ fst $ queues q) idx
           -> RankedElem x q idx
  BackElem : {q : Queue size ty}
          -> {idx : Nat}
          -> RankedElem x (snd $ snd $ queues q) idx
          -> RankedElem x q (size `minus` S idx)

export
empty : Queue Z _
empty = MkQueue [] []

lteAddRightLemma : LTE r c -> LTE r (l + c)
lteAddRightLemma {l} {r} {c} smaller
  = lteTransitive smaller cLTElc
    where cLTElc : LTE c (l + c)
          cLTElc = rewrite plusCommutative l c in
                   lteAddRight {m = l} c

minusPlusEqualsPlusMinus : (l, c, r: Nat) -> LTE r c -> LTE r (l + c) -> (l + c) - r = l + (c - r)
minusPlusEqualsPlusMinus Z _ _ _ _ = Refl
minusPlusEqualsPlusMinus (S _) Z Z _ _ = Refl
minusPlusEqualsPlusMinus (S _) (S _) Z _ _ = Refl
minusPlusEqualsPlusMinus _ Z (S _) _ _ impossible
minusPlusEqualsPlusMinus l (S c) (S r) smaller _
  = let smaller' = fromLteSucc smaller in
    rewrite sym $ plusSuccRightSucc l c in
    minusPlusEqualsPlusMinus l c r smaller' (lteAddRightLemma smaller')

make_ : {n : Nat}
     -> (f : Vect n ty)
     -> {m : Nat}
     -> (r : Vect m ty)
     -> (ret : Queue (n + m) ty
         ** ({x : ty} -> {idx : Nat} -> RankedElem x f idx -> RankedElem x ret idx,
             {x : ty} -> {idx : Nat} -> RankedElem x r idx -> RankedElem x ret (n + m `minus` S idx)))
make_ {n} f {m} r with (order {to = LTE} m n)
  | Left _ = (MkQueue f r ** (FrontElem, BackElem))
  | Right _ = let (reversed ** rProj) = rev_ r
                  (f' ** (fProj, reversedProj)) = f `concat_` reversed in
              rewrite sym $ plusZeroRightNeutral (n + m) in
              (MkQueue f' [] ** (FrontElem . fProj,
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
snoc_ : (q : Queue size ty) -> (x : ty)
     -> (ret : Queue (S size) ty
         ** ({x : ty} -> {idx : Nat} -> RankedElem x q idx -> RankedElem x ret idx,
             RankedElem x ret size))
snoc_ (MkQueue {n} f {m} r) x = rewrite plusSuccRightSucc n m in
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
snoc : Queue size ty -> ty -> Queue (S size) ty
snoc q x = fst $ snoc_ q x

export
head_ : (q : Queue (S _) ty) -> (x : ty ** RankedElem x q Z)
head_ (MkQueue (x :: xs) ys) = (x ** FrontElem Here)

export
head : Queue (S _) ty -> ty
head q = fst $ head_ q

export
tail_ : (q : Queue (S size) ty)
     -> (ret : Queue size ty
         ** {x : ty} -> {idx : Nat} -> RankedElem x q (S idx) -> RankedElem x ret idx)
tail_ (MkQueue (_::fs) r)
  = let (ret ** (fProj, rProj)) = make_ fs r in
    (ret ** \el =>
      case toPattern el of
      (Z ** (_, Refl)) impossible
      (S _ ** (FrontElem (There x), Refl)) => fProj x
      (_ ** (BackElem x, prf)) => rewrite toMinusSuccPredEq prf in rProj x)
    where toPattern : {q : Queue (S _) ty}
                   -> {i : Nat}
                   -> RankedElem x q (S i)
                   -> (i' ** (RankedElem x q i', S i = i'))
          toPattern {i} el = (S i ** (el, Refl))
          toMinusSuccPredEq : S c = x + y `minus` z -> c = x + y `minus` S z
          toMinusSuccPredEq {x} {y} {z} prf = rewrite minusSuccPred (x + y) z in cong {f = Nat.pred} prf

export
tail : Queue (S size) ty -> Queue size ty
tail q = fst $ tail_ q
