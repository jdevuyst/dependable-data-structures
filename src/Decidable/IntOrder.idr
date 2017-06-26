module Decidable.IntOrder

import Decidable.Order

%default total

public export
data LTE : Int -> Int -> Type where
  Compare : (a : Int) -> (b : Int) -> { auto prf : a <= b = True} -> LTE a b
  Reflexive : (a : Int) -> LTE a a
  Transitive : (a : Int) -> (b : Int) -> (c : Int) -> (ab : LTE a b) -> (bc : LTE b c) -> LTE a c
  Ordered : (a : Int) -> (b : Int) -> { auto contra : (a <= b = True) -> Void } -> LTE b a

export
implementation Preorder Int LTE where
  transitive = Transitive
  reflexive = Reflexive

export
implementation Poset Int LTE where
  antisymmetric a b _ _ = really_believe_me ()

export
implementation Ordered Int LTE where
  order a b = case decEq (a <= b) True of
              Yes prf => Left $ Compare {prf} a b
              No contra => Right $ Ordered {contra} a b