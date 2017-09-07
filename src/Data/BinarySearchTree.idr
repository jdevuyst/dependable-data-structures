module Data.BinarySearchTree

import Decidable.Order

%default total

contraSym : ((lhs = rhs) -> Void) -> (rhs = lhs) -> Void
contraSym contra eq = contra $ sym eq

strictRel : Ordered ty rel => {lhs : ty} -> {rhs : ty} ->
  lhs `rel` rhs -> (lhs = rhs -> Void ) -> (rhs `rel` lhs -> Void)
strictRel {lhs} {rhs} smaller notEq assumption =
  notEq $ antisymmetric lhs rhs smaller assumption

revStrictRel : {auto constraint : Ordered ty rel} -> {lhs : ty} -> {rhs : ty} ->
  (lhs `rel` rhs -> Void) -> (rhs `rel` lhs)
revStrictRel {rel} {lhs} {rhs} gt =
  case order {to = rel} lhs rhs of
    Left lte => absurd $ gt lte
    Right gte => gte

using (constraint : Ordered ty rel)
  export
  data Bounded : Ordered ty rel -> Maybe ty -> ty -> Maybe ty -> Type where
    WithinBounds : {lbound, ubound : Maybe ty} -> {pivot : ty} ->
      (gt : (x ** (lbound = Just x, rel pivot x)) -> Void) ->
      (lt : (x ** (ubound = Just x, rel x pivot)) -> Void) ->
      Bounded constraint lbound pivot ubound

  GTNothing : {auto constraint : Ordered ty rel} -> {value: ty} -> Type
  GTNothing {ty} {rel} {value} = (x : ty ** (Nothing = Just x, rel value x))

  anythingGTNothing : {auto constraint : Ordered ty rel} -> GTNothing -> Void
  anythingGTNothing (_ ** (Refl, _)) impossible

  LTNothing : {auto constraint : Ordered ty rel} -> {value: ty} -> Type
  LTNothing {ty} {rel} {value} = (x : ty ** (Nothing = Just x, rel x value))

  anythingLTNothing : {auto constraint : Ordered ty rel} -> LTNothing -> Void
  anythingLTNothing (_ ** (Refl, _)) impossible

  export
  WithinUnconstrainedBounds : {pivot : ty} -> Bounded _ Nothing pivot Nothing
  WithinUnconstrainedBounds {pivot} =
    WithinBounds {pivot} anythingGTNothing anythingLTNothing

  export
  changeLbound : Bounded constraint _ pivot ubound -> (rel pivot v -> Void) ->
    Bounded constraint (Just v) pivot ubound
  changeLbound {v} (WithinBounds _ lt) gt = WithinBounds {pivot} gt' lt
    where gt' : (x ** (Just v = Just x, rel pivot x)) -> Void
          gt' (x ** (prf, gte)) = gt $ rewrite justInjective prf in gte

  export
  changeUbound : Bounded constraint lbound pivot _ -> (rel v pivot -> Void) ->
    Bounded constraint lbound pivot (Just v)
  changeUbound {v} (WithinBounds gt _) lt = WithinBounds {pivot} gt lt'
    where lt' : (x ** (Just v = Just x, rel x pivot)) -> Void
          lt' (x ** (prf, lte)) = lt $ rewrite justInjective prf in lte

  public export
  data BinarySearchTree_ : Ordered ty rel -> Maybe ty -> Maybe ty -> Nat -> Type where
    Empty : BinarySearchTree_ _ _ _ Z
    Node : (v : ty) ->
      .{bounded : Bounded constraint lbound v ubound} ->
      {leftCount, rightCount : Nat} ->
      (left : BinarySearchTree_ constraint lbound (Just v) leftCount) ->
      (right : BinarySearchTree_ constraint (Just v) ubound rightCount) ->
      BinarySearchTree_ constraint lbound ubound (S $ leftCount + rightCount)

  value : BinarySearchTree_ constraint _ _ (S _) -> ty
  value (Node v _ _) = v

  leftCount : BinarySearchTree_ constraint _ _ (S _) -> Nat
  leftCount (Node {leftCount = len} _ _ _) = len

  left : {constraint : Ordered ty rel} ->
    (orig : BinarySearchTree_ constraint lbound _ (S _)) ->
      BinarySearchTree_ constraint lbound (Just (value orig)) (leftCount orig)
  left (Node _ l _) = l

  rightCount : BinarySearchTree_ constraint _ _ (S _) -> Nat
  rightCount (Node {rightCount = len} _ _ _) = len

  right : {constraint : Ordered ty rel} ->
    (orig : BinarySearchTree_ constraint _ ubound (S _)) ->
      BinarySearchTree_ constraint (Just (value orig)) ubound (rightCount orig)
  right (Node _ _ r) = r

  export
  data Elem : ty -> BinarySearchTree_ constraint _ _ _ -> Type where
    Here : Elem v (Node {constraint} v _ _)
    Left : Elem v l -> Elem v (Node _ l _)
    Right : Elem v r -> Elem v (Node _ _ r)

  export
  noEmptyElem : Elem _ Empty -> Void
  noEmptyElem _ impossible

  export
  lboundRespected :
    {lbound : ty} -> {tree : BinarySearchTree_ constraint (Just lbound) _ _} ->
    Elem pivot tree -> rel pivot lbound -> Void
  lboundRespected {rel} {lbound} {tree} elem {pivot} prf =
    let Node {bounded = WithinBounds gt _} v _ _ = tree in
      case elem of
        Here => gt (lbound ** (Refl, prf))
        Left elemL => lboundRespected elemL prf
        Right elemR => case order {to = rel} lbound v of
                         Left lte => let prf' = transitive pivot _ _ prf lte in
                                       lboundRespected elemR prf'
                         Right gte => gt (lbound ** (Refl, gte))

  export
  uboundRespected :
    {ubound : ty} -> {tree : BinarySearchTree_ constraint _ (Just ubound) _} ->
    Elem pivot tree -> rel ubound pivot -> Void
  uboundRespected {rel} {ubound} {tree} elem {pivot} prf =
    let Node {bounded = WithinBounds _ lt} v _ _ = tree in
      case elem of
        Here => lt (ubound ** (Refl, prf))
        Left elemL => case order {to = rel} v ubound of
                        Left lte => let prf' = transitive v _ _ lte prf in
                                      uboundRespected elemL prf'
                        Right gte => lt (ubound ** (Refl, gte))
        Right elemR => uboundRespected elemR prf

  data SearchSpace : Type where
    MkSearchSpace : Bounded constraint lbound pivot ubound ->
      BinarySearchTree_ constraint lbound ubound len -> SearchSpace

  data Finding : SearchSpace -> (SearchSpace -> Type) -> Type where
    GoLeft : .{retCalc : SearchSpace -> Type} ->
      .{bounded : Bounded constraint lbound pivot ubound} ->
      {orig : BinarySearchTree_ constraint lbound ubound (S _)} ->
      {leftBounded : Bounded constraint lbound pivot (Just (value orig))} ->
      (rel (value orig) pivot -> Void) ->
      retCalc (MkSearchSpace leftBounded (left orig)) ->
      Finding (MkSearchSpace bounded orig) retCalc
    GoRight : .{retCalc : SearchSpace -> Type} ->
      .{bounded : Bounded constraint lbound pivot ubound} ->
      {orig : BinarySearchTree_ constraint lbound ubound (S _)} ->
      {rightBounded : Bounded constraint (Just (value orig)) pivot ubound} ->
      (rel pivot (value orig) -> Void) ->
      retCalc (MkSearchSpace rightBounded (right orig)) ->
      Finding (MkSearchSpace bounded orig) retCalc
    Found : .{bounded : Bounded constraint lbound pivot ubound} ->
      {orig : BinarySearchTree_ constraint lbound ubound (S _)} ->
      (pivot = value orig) -> Finding (MkSearchSpace bounded orig) _
    DeadEnd : .{bounded : Bounded constraint lbound pivot ubound} ->
      {orig : BinarySearchTree_ constraint lbound ubound Z} ->
      Finding (MkSearchSpace bounded orig) _

  FindingTransform : Ordered ty _ -> ty -> (SearchSpace -> Type) -> Type
  FindingTransform {ty} constraint pivot retCalc =
    (lbound', ubound': Maybe ty) ->
    (bounded' : Bounded constraint lbound' pivot ubound') ->
    {len' : Nat} ->
    (tree' : BinarySearchTree_ constraint lbound' ubound' len') ->
    Finding (MkSearchSpace bounded' tree') retCalc ->
    retCalc (MkSearchSpace bounded' tree')

  find_ : DecEq ty => (pivot : ty) ->
    {lbound, ubound : Maybe ty} -> {len : Nat} ->
    (tree : BinarySearchTree_ constraint lbound ubound len) ->
    (bounded : Bounded constraint lbound pivot ubound) ->
    FindingTransform constraint pivot retCalc ->
    Finding (MkSearchSpace bounded tree) retCalc
  find_ _ Empty _ _ = DeadEnd
  find_ {rel} {len = S _} pivot (Node v l r) pivotBounded extract =
    case decEq pivot v of
      Yes Refl => Found Refl
      No contra => case order {to = rel} pivot v of
                     Left prf => let lt = strictRel prf contra
                                     bounded = changeUbound pivotBounded lt
                                     finding = find_ pivot l bounded extract
                                     ret = extract _ _ _ _ finding in
                                   GoLeft lt ret
                     Right prf => let gt = strictRel prf (contraSym contra)
                                      bounded = changeLbound pivotBounded gt
                                      finding = find_ pivot r bounded extract
                                      ret = extract _ _ _ _ finding in
                                    GoRight gt ret

  public export
  BinarySearchTree : Ordered ty rel -> Nat -> Type
  BinarySearchTree constraint len =
    BinarySearchTree_ constraint Nothing Nothing len

  public export
  CountedBinarySearchTree : Ordered ty rel -> Type
  CountedBinarySearchTree constraint =
    (len : Nat ** BinarySearchTree constraint len)

  find : DecEq ty => (pivot : ty) ->
    (ct : CountedBinarySearchTree constraint) ->
    FindingTransform constraint pivot retCalc ->
    retCalc $ MkSearchSpace (WithinUnconstrainedBounds {pivot}) (snd ct)
  find pivot (_ ** tree) transform =
    transform _ _ _ _ $ find_ pivot tree _ transform

  export
  decElem : DecEq ty => (v : ty) ->
    (ct : CountedBinarySearchTree constraint) ->
    Dec (Elem v (snd ct))
  decElem {constraint} value ct = find value ct transform
    where retCalc : SearchSpace -> Type
          retCalc (MkSearchSpace (WithinBounds {pivot} _ _) tree') =
            Dec (Elem pivot tree')
          transform : FindingTransform constraint value retCalc
          transform lbound' ubound' (WithinBounds {pivot = value} _ _) len tree' finding =
            case finding of
              GoLeft {orig = Node _ _ _} {leftBounded} contra prev =>
                let WithinBounds _ _ = leftBounded in
                case prev of
                  Yes prf => Yes $ Left prf
                  No contra' => No $ \prop => case prop of
                                                Here => contra $ reflexive value
                                                Left elem => contra' elem
                                                Right elem => lboundRespected elem (revStrictRel contra)
              GoRight {orig = Node _ _ _} {rightBounded} contra prev =>
                let WithinBounds _ _ = rightBounded in
                case prev of
                  Yes prf => Yes $ Right prf
                  No contra' => No $ \prop => case prop of
                                                Here => contra $ reflexive value
                                                Left elem => uboundRespected elem (revStrictRel contra)
                                                Right elem => contra' elem
              Found {orig = Node _ _ _} Refl => Yes Here
              DeadEnd {orig = Empty} => No noEmptyElem

  export
  elem : DecEq ty => ty -> CountedBinarySearchTree constraint -> Bool
  elem v ct = decAsBool $ decElem v ct

  export
  insert : DecEq ty => CountedBinarySearchTree constraint -> ty ->
    CountedBinarySearchTree constraint
  insert {constraint} ct value = find value ct transform
    where retCalc : SearchSpace -> Type
          retCalc (MkSearchSpace {constraint} (WithinBounds {pivot} {lbound} {ubound} _ _) tree') =
            (len : Nat ** BinarySearchTree_ constraint lbound ubound len)
          transform : FindingTransform constraint value retCalc
          transform lbound' ubound' (WithinBounds {pivot = value} gt lt) len tree' finding =
            case finding of
              GoLeft {orig} {leftBounded} _ prev =>
                let Node {bounded} v _ r = orig
                    WithinBounds _ _ = leftBounded
                    (_ ** l') = prev in
                  (_ ** Node {bounded} v l' r)
              GoRight {orig} {rightBounded} _ prev =>
                let Node {bounded} v l _ = orig
                    WithinBounds _ _ = rightBounded
                    (_ ** r') = prev in
                  (_ ** Node {bounded} v l r')
              Found {orig} Refl => (_ ** orig)
              DeadEnd {orig = Empty} =>
                let bounded = WithinBounds gt lt in
                  (_ ** Node {bounded} value Empty Empty)