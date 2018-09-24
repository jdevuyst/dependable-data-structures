module Data.RandomAccessList

import Rekenaar

import Data.Fin

%default total
%language ElabReflection

-- TODO: Use idris-quickcheck to verify that the chosen implementation matches the
-- behavior of an implementation that uses induction (see comments)
select : (size1 : Nat) -> {size2 : Nat} -> Fin (size1 + size2) -> Either (Fin size1) (Fin size2)
-- select Z {size2} idx = Right idx
-- select (S size1) FZ = Left FZ
-- select (S size1) {size2} (FS idx)
--   = case select size1 idx of
--     Left n => Left $ FS n
--     Right n => Right n
select size1 {size2 = Z} idx = Left $ rewrite the (size1 = size1 + 0) (%runElab natPlusRefl) in idx
select size1 {size2 = S _} idx
  = let idxInt = finToInteger idx in
    case integerToFin idxInt size1 of
    Just idx' => Left idx'
    Nothing => Right $ restrict _ (idxInt - cast size1)

data Tree : (size : Nat) -> (ty : Type) -> Type where
  Singleton : (value : ty) -> Tree (S Z) ty
  Merged : .{halfSize : Nat} -> (left : Tree halfSize ty) -> (right : Tree halfSize ty) -> Tree (halfSize + halfSize) ty

treeLookup : {size : Nat} -> Fin size -> Tree size ty -> ty
treeLookup FZ (Singleton x) = x
treeLookup {size = halfSize + halfSize} idx (Merged left right) with (select halfSize idx)
  | (Left idx') = treeLookup idx' left
  | (Right idx') = treeLookup idx' right

treeUpdate : {size : Nat} -> Fin size -> Tree size ty -> (ty -> ty) -> Tree size ty
treeUpdate FZ (Singleton x) f = Singleton $ f x
treeUpdate {size = halfSize + halfSize} idx (Merged left right) f with (select halfSize idx)
  | (Left idx') = Merged (treeUpdate idx' left f) right
  | (Right idx') = Merged left (treeUpdate idx' right f)

pow2 : Nat -> Nat
pow2 n = power 2 n

data TreeList : (pos : Nat) -> (size : Nat) -> (ty : Type) -> Type where
  Nil : TreeList _ Z _
  (::) : {nextPos : Nat} -> .{auto posPrf : LT pos nextPos}
         -> .{size : Nat} -> .{auto smaller : LTE (pow2 pos) size}
         -> Tree (pow2 pos) ty -> TreeList nextPos (size - (pow2 pos)) ty
         -> TreeList pos size ty

minusLeftPlusRight : {x, y, z : Nat} -> {auto smaller : LTE y x}
                  -> x - y = z -> x = y + z
minusLeftPlusRight {x} {y = Z} {z} prf = rewrite sym $ minusZeroRight x in prf
minusLeftPlusRight {x = Z} {y = S _} _ impossible
minusLeftPlusRight {x = S x'} {y = S y'} {z} {smaller} prf
  = let smaller' = fromLteSucc smaller
        prf' = replace {P = \var => var = z} (minusSuccSucc x' y') prf
        ind = minusLeftPlusRight prf' in
    cong {f = S} ind

treeSizeComponents : (pos, size : Nat) -> {auto smaller : LTE (pow2 pos) size}
                     -> size = pow2 pos + (size - pow2 pos)
treeSizeComponents pos size {smaller} = minusLeftPlusRight Refl

treeListLookup : {pos, size : Nat} -> Fin size -> TreeList pos size ty -> ty
treeListLookup {pos} {size} idx (t :: ts)
  with (let eqPrf = treeSizeComponents pos size
            idx' = (replace {P = \x => Fin x} eqPrf idx) in
        select (pow2 pos) idx')
  | (Left idx') = treeLookup idx' t
  | (Right idx') = treeListLookup idx' ts

treeListUpdate : {pos, size : Nat} -> Fin size -> TreeList pos size ty -> (ty -> ty) -> TreeList pos size ty
treeListUpdate {pos} {size} idx (t :: ts) f
  with (let eqPrf = treeSizeComponents pos size
            idx' = (replace {P = \x => Fin x} eqPrf idx) in
        select (pow2 pos) idx')
  | (Left idx') = treeUpdate idx' t f :: ts
  | (Right idx') = t :: treeListUpdate idx' ts f

pow2Lemma : (x : Nat) -> (pow2 x + pow2 x) = pow2 (S x)
pow2Lemma Z = Refl
pow2Lemma (S x)
  = let hyp = pow2Lemma x in
    rewrite sym hyp in
    rewrite the (pow2 x + pow2 x + 0 = pow2 x + pow2 x) (%runElab natPlusRefl) in
    Refl

lteAddLeft : (m, n : Nat) -> LTE n (m + n)
lteAddLeft m n = rewrite the (m + n = n + m) (%runElab natPlusRefl) in lteAddRight {m} n

ltAddRight : (n : Nat) -> {m : Nat} -> LT n (n + (S m))
ltAddRight n {m} = rewrite the (n + S m = S (n + m)) (%runElab natPlusRefl) in lteAddRight {m} (S n)

lteAddBoth : {x, y, x', y' : Nat} -> LTE x y -> LTE x' y' -> LTE (x + x') (y + y')
lteAddBoth {x' = S _} {y' = Z} _ _ impossible
lteAddBoth {x} {y} {x' = Z} {y'} smaller _
  = rewrite the (x + 0 = x) (%runElab natPlusRefl) in
    lteTransitive smaller (lteAddRight y)
lteAddBoth {x} {y} {x' = S x''} {y' = S y''} smaller smaller'
  = let ind = lteAddBoth smaller (fromLteSucc smaller') in
    rewrite the (x + (S x'') = S (x + x'')) (%runElab natPlusRefl) in
    rewrite the (y + (S y'') = S (y + y'')) (%runElab natPlusRefl) in
    LTESucc ind

pow2Monotone : {n, m : Nat} -> LTE n m -> LTE (pow2 n) (pow2 m)
pow2Monotone {n = Z} {m = Z} _ = LTESucc LTEZero
pow2Monotone {n = Z} {m = S m'} _
  = let prf = pow2Monotone {n = Z} {m = m'} LTEZero in
    lteTransitive prf (lteAddRight (pow2 m') {m = (pow2 m' + 0)})
pow2Monotone {n = S _} {m = Z} _ impossible
pow2Monotone {n = S n'} {m = S m'} smaller
  = let prf = pow2Monotone {n = n'} {m = m'} (fromLteSucc smaller)
        prf' = lteAddBoth prf (lteRefl {n = Z}) in
    lteAddBoth prf prf'

minusPlusNeutral : (x, y : Nat) -> LTE y x -> (x - y) + y = x
minusPlusNeutral x Z _
  = replace {P = \var => var = x}
            (the (x `minus` Z = (x `minus` Z) + Z) (%runElab natPlusRefl))
            (minusZeroRight x)
minusPlusNeutral Z (S _) _ impossible
minusPlusNeutral (S x) (S y) prf
  = let ind = minusPlusNeutral x y (fromLteSucc prf) in
    rewrite the ((x `minus` y) + (S y) = S ((x `minus` y) + y)) (%runElab natPlusRefl) in
    cong {f = S} ind

plusMinusAssociative : (a, b, c : Nat) -> {auto smaller : LTE c b} -> a + (b `minus` c) = (a + b) `minus` c
plusMinusAssociative a b Z
  = rewrite minusZeroRight b in
    rewrite minusZeroRight (a + b) in
    Refl
plusMinusAssociative a Z (S _) impossible
plusMinusAssociative a (S b) (S c) {smaller}
  = let ind = plusMinusAssociative {smaller = fromLteSucc smaller} a b c
        succPrf = sym $ minusSuccSucc (a + b) c
        p = \x => (a + b) `minus` c = x `minus` (S c)
        succPrf' = replace {P = p} (the (S (a + b) = a + S b) (%runElab natPlusRefl)) succPrf in
    replace {P = \x => a + (b `minus` c) = x} succPrf' ind

lteReflAddLeftContra : LTE (x + S y) x -> Void
lteReflAddLeftContra {x = S _} LTEZero impossible
lteReflAddLeftContra (LTESucc {left = Z + S y} {right = Z} prf) impossible
lteReflAddLeftContra (LTESucc {left = S x + S y} {right = S x} prf) = absurd $ lteReflAddLeftContra prf

treeListCons : {tPos, pos : Nat} -> Tree (pow2 tPos) ty -> TreeList pos size ty -> .{auto fits : LTE tPos pos}
               -> (newPos : Nat ** TreeList newPos (size + (pow2 tPos)) ty)
treeListCons {ty} {tPos} t Nil = let nil = replace {P = \x => TreeList (S tPos) x ty}
                                                   (minusZeroN (pow2 tPos))
                                                   RandomAccessList.Nil
                                     ts' = (::) {nextPos = S tPos} {posPrf = lteRefl} {smaller = lteRefl} t nil in
                                 (tPos ** ts')
treeListCons {tPos} {pos} {size} t' ((::) {smaller} t ts) {fits} {ty}
  = case cmp tPos pos of
    CmpEQ => let merged = Merged t' t
                 merged' = replace {P = \x => Tree x ty} (pow2Lemma tPos) merged
                 (newPos ** ts') = treeListCons {tPos = S tPos} merged' ts in
             rewrite sym $ minusPlusNeutral size (pow2 tPos) $
                     lteTransitive (pow2Monotone fits) smaller in
             rewrite the (plus (plus (minus size (power 2 tPos)) (power 2 tPos)) (power 2 tPos)
                         = plus (minus size (power 2 tPos)) (plus (power 2 tPos) (plus (power 2 tPos) 0)))
                     (%runElab natPlusRefl) in
             (newPos ** ts')
    CmpLT diff => let p = the (size + 0 = size) (%runElab natPlusRefl)
                      p' = minusZeroN $ pow2 tPos
                      p'' = replace {P = \x => size + x = size} p' p
                      p''' = replace {P = \x => x = size} (plusMinusAssociative {smaller = lteRefl} size (pow2 tPos) (pow2 tPos)) p''
                      ts' = (::) {smaller} t ts
                      ts'' = replace {P = \s => TreeList (tPos + (S diff)) s ty} (sym p''') ts'
                      ts''' = RandomAccessList.(::) {posPrf = ltAddRight tPos} {smaller = lteAddLeft size (pow2 tPos)} t' ts'' in
                  (tPos ** ts''')
    CmpGT diff => absurd $ lteReflAddLeftContra fits

pow2StrictlyPositive : (n : Nat) -> LTE 1 (pow2 n)
pow2StrictlyPositive Z = lteRefl
pow2StrictlyPositive (S n)
  = let ind = pow2StrictlyPositive n in
    lteTransitive ind (lteAddRight {m = pow2 n + Z} (pow2 n))

equalsNotLT : {n, m : Nat} -> n = m -> LT n m -> Void
equalsNotLT {n = Z} {m = Z} _ lt impossible
equalsNotLT {n = Z} {m = S _} Refl _ impossible
equalsNotLT {n = S _} {m = Z} Refl _ impossible
equalsNotLT {n = S n'} {m = S m'} eq (LTESucc lt')
  = equalsNotLT (cong {f = Nat.pred} eq) lt'

treeListTailHelper : {tPos, tsPos, size : Nat}
                  -> Tree (pow2 tPos) ty
                  -> TreeList tsPos size ty
                  -> {posPrf : LTE tPos tsPos}
                  -> let smaller = lteTransitive (pow2StrictlyPositive tPos)
                                                 (lteAddRight {m = size} (pow2 tPos)) in
                     (pos' ** TreeList pos' ((-) {smaller} (pow2 tPos + size) (S Z)) ty)
treeListTailHelper {size} {tPos = Z} _ ts = rewrite minusZeroRight size in (_ ** ts)
treeListTailHelper {ty} {size} {tPos = S pos'} t {tsPos} {posPrf} ts
  = let (_ ** (t', eqPrf)) = eraseSize t in
    case t' of
      Singleton _ => void $ notSingleton eqPrf
      Merged {halfSize} l r =>
        let eqPrf' = replace {P = \y => halfSize + halfSize = pow2 pos' + y} (the (pow2 pos' + 0 = pow2 pos') (%runElab natPlusRefl)) eqPrf
            l' = replace {P = \x => Tree x ty} (halve eqPrf') l
            r' = replace {P = \x => Tree x ty} (halve eqPrf') r
            p = plusZeroRightNeutral size
            p' = minusZeroN $ pow2 pos'
            p'' = replace {P = \x => size + x = size} p' p
            p''' = replace {P = \x => x = size} (plusMinusAssociative {smaller = lteRefl} size (pow2 pos') (pow2 pos')) p''
            ts' = replace {P = \x => TreeList tsPos x ty} (sym p''') ts
            ts'' = RandomAccessList.(::) {posPrf} {smaller = lteAddLeft size (pow2 pos')} r' ts' in
        rewrite the (pow2 pos' + (pow2 pos' + 0) + size = pow2 pos' + (size + pow2 pos')) (%runElab natPlusRefl) in
        treeListTailHelper {posPrf = lteRefl} l' ts''
    where eraseSize : {n : Nat} -> Tree n ty -> (n' : Nat ** (Tree n' ty, n' = n))
          eraseSize t = (_ ** (t, Refl))
          halve : {x, y : Nat} -> x + x = y + y -> x = y
          halve {x = Z} {y = S _} Refl impossible
          halve {x = S _} {y = Z} Refl impossible
          halve {x = Z} {y = Z} _ = Refl
          halve {x = S x'} {y = S y'} prf = cong {f = S} $ halve prev
            where prev : x' + x' = y' + y'
                  prev = let prf' = replace {P = \var => var = S (S y' + y')}
                                            (the (S x' + S x' = S (S x' + x')) (%runElab natPlusRefl)) $
                                    replace {P = \var => S x' + S x' = var}
                                            (the (S y' + S y' = S (S y' + y')) (%runElab natPlusRefl)) $
                                            prf in
                         cong {f = Nat.pred . Nat.pred} prf'
          notSingleton : {n : Nat} -> 1 = (pow2 n) + (pow2 n + Z) -> Void
          notSingleton {n} eq
            = let eq' = replace {P = \var => 1 = pow2 n + var}
                                (the (pow2 n + Z = pow2 n) (%runElab natPlusRefl))
                                eq
                  lte = pow2StrictlyPositive n
                  lte' = lteAddBoth lte lte in
              void $ equalsNotLT eq' lte'

treeListTail : {pos, size : Nat} -> TreeList pos (S size) ty -> (newPos : Nat ** TreeList newPos size ty)
treeListTail {ty} {pos} {size} ((::) {posPrf} t ts)
  = let (newPos ** newList) = treeListTailHelper {posPrf = lteSuccLeft posPrf} t ts
        p = plusMinusAssociative (pow2 pos) (S size) (pow2 pos)
        newList' = replace {P = \x => TreeList newPos (x `minus` 1) ty} p newList
        p' = the (pow2 pos + S size = S size + pow2 pos) (%runElab natPlusRefl)
        newList'' = replace {P = \x => TreeList newPos ((x `minus` pow2 pos) `minus` 1) ty} p' newList'
        p'' = sym $ plusMinusAssociative {smaller = lteRefl} (S size) (pow2 pos) (pow2 pos)
        newList''' = replace {P = \x => TreeList newPos (x `minus` 1) ty} p'' newList'' in
    rewrite the (size = size + 0) (%runElab natPlusRefl) in
    rewrite minusZeroN $ pow2 pos in
    rewrite sym $ minusZeroRight (size + (pow2 pos `minus` pow2 pos)) in
    (newPos ** newList''')

namespace RandomAccessList
  export
  RandomAccessList : Nat -> Type -> Type
  RandomAccessList size ty = (pos : Nat ** TreeList pos size ty)

  export
  empty : RandomAccessList Z ty
  empty = (Z ** Nil)

  export
  cons : ty -> RandomAccessList size ty -> RandomAccessList (S size) ty
  cons {size} x (pos ** l)
    = let (pos' ** l') = treeListCons (Singleton x) l in
      rewrite the (S Z + size = size + S Z) (%runElab natPlusRefl) in
      (pos' ** l')

  export
  tail : {size : Nat} -> RandomAccessList (S size) ty -> RandomAccessList size ty
  tail (pos ** l) = treeListTail l

  export
  index : {size : Nat} -> Fin size -> RandomAccessList size ty -> ty
  index idx (pos ** l) = treeListLookup idx l

  export
  update : {size : Nat} -> Fin size -> RandomAccessList size ty -> (ty -> ty) -> RandomAccessList size ty
  update idx (pos ** l) f = (pos ** treeListUpdate idx l f)

namespace CountedRandomAccessList
  export
  CountedRandomAccessList : Type -> Type
  CountedRandomAccessList ty = (len : Nat ** RandomAccessList len ty)

  export
  empty : CountedRandomAccessList ty
  empty = (Z ** RandomAccessList.empty)

  export
  cons : ty -> CountedRandomAccessList ty -> CountedRandomAccessList ty
  cons x (size ** arr) = (S size ** cons x arr)

  export
  tail : CountedRandomAccessList ty -> CountedRandomAccessList ty
  tail (Z ** arr) = (Z ** arr)
  tail (S size ** arr) = (size ** tail arr)

  export
  size : CountedRandomAccessList ty -> Nat
  size (size ** _) = size

  export
  index : (idx : Nat) -> (carr : CountedRandomAccessList ty) -> Maybe ty
  index idx (size ** arr)
    = do finIdx <- natToFin idx size
         pure $ index finIdx arr

  export
  update : (idx : Nat) -> (carr : CountedRandomAccessList ty) -> (ty -> ty) -> CountedRandomAccessList ty
  update idx (size ** arr) f
    = maybe (size ** arr) 
            (\finIdx => (size ** update finIdx arr f))
            (natToFin idx size)
