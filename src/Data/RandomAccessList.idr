module Data.RandomAccessList

import Data.Fin

%default total

select : (size1 : Nat) -> {size2 : Nat} -> Fin (size1 + size2) -> Either (Fin size1) (Fin size2)
select size1 {size2 = Z} idx = Left $ rewrite sym $ plusZeroRightNeutral size1 in idx
select size1 {size2 = (S _)} idx =
  let idxInt = finToInteger idx in
  case integerToFin idxInt size1 of
  Just idx' => Left idx'
  Nothing => Right $ restrict _ idxInt

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
  (::) : {nextPos, nextSize : Nat} -> .{auto posPrf : LT pos nextPos}
         -> Tree (pow2 pos) ty -> TreeList nextPos nextSize ty
         -> TreeList pos (pow2 pos + nextSize) ty

treeListLookup : {pos : Nat} -> Fin size -> TreeList pos size ty -> ty
treeListLookup {pos} idx (t :: ts) with (select (pow2 pos) idx)
  | (Left idx') = treeLookup idx' t
  | (Right idx') = treeListLookup idx' ts

treeListUpdate : {pos : Nat} -> Fin size -> TreeList pos size ty -> (ty -> ty) -> TreeList pos size ty
treeListUpdate {pos} idx (t :: ts) f with (select (pow2 pos) idx)
  | (Left idx') = treeUpdate idx' t f :: ts
  | (Right idx') = t :: treeListUpdate idx' ts f

pow2Lemma : (x : Nat) -> (pow2 x + pow2 x) = pow2 (S x)
pow2Lemma Z = Refl
pow2Lemma (S x)
  = let hyp = pow2Lemma x in
    rewrite sym hyp in
    rewrite plusZeroRightNeutral (pow2 x + pow2 x) in
    Refl

lteReflAddLeftContra : LTE (x + S y) x -> Void
lteReflAddLeftContra {x = S _} LTEZero impossible
lteReflAddLeftContra (LTESucc {left = Z + S y} {right = Z} prf) impossible
lteReflAddLeftContra (LTESucc {left = S x + S y} {right = S x} prf) = absurd $ lteReflAddLeftContra prf

treeListCons : {tPos, pos : Nat} -> Tree (pow2 tPos) ty -> TreeList pos size ty -> .{auto fits : LTE tPos pos}
               -> (newPos : Nat ** TreeList newPos (size + (pow2 tPos)) ty)
treeListCons {tPos} t Nil = rewrite sym $ plusZeroRightNeutral (pow2 tPos) in 
                            (tPos ** (::) {nextPos = S tPos} {posPrf = lteRefl} t Nil)
treeListCons {tPos} {pos} t' ((::) {nextSize} t ts) {fits}
  = case cmp tPos pos of
    CmpEQ => let merged = Merged t' t
                 merged' = replace {P = \x => Tree x ty} (pow2Lemma tPos) merged
                 (newPos ** ts') = treeListCons {tPos = S tPos} merged' ts in
             rewrite plusCommutative (pow2 tPos) nextSize in
             rewrite sym $ plusAssociative nextSize (pow2 tPos) (pow2 tPos) in
             rewrite pow2Lemma tPos in
             (newPos ** ts')
    CmpLT diff => let prf = lteAddRight {m = diff} (S tPos)
                      prf' = replace {P = \x => LTE (S tPos) x} (plusSuccRightSucc tPos diff) prf
                      ts' = t' :: (t :: ts) in
                  rewrite plusCommutative (pow2 (tPos + S diff) + nextSize) (pow2 tPos) in
                  (tPos ** ts')
    CmpGT diff => absurd $ lteReflAddLeftContra fits

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
      rewrite plusCommutative (S Z) size in
      (pos' ** l')

  export
  index : Fin size -> RandomAccessList size ty -> ty
  index idx (pos ** l) = treeListLookup idx l

  export
  update : Fin size -> RandomAccessList size ty -> (ty -> ty) -> RandomAccessList size ty
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
