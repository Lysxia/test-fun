{-# LANGUAGE
    DeriveFunctor,
    DeriveFoldable,
    DeriveTraversable,
    EmptyCase,
    FlexibleContexts,
    FlexibleInstances,
    GADTs,
    ScopedTypeVariables,
    TypeOperators,
    UndecidableInstances #-}

-- | Representation of (higher-order) functions.
--
-- === Warning
--
-- This is an internal module: it is not subject to any versioning policy,
-- breaking changes can happen at any time.
-- It is made available only for debugging.
-- Otherwise, use "Test.Fun".
--
-- If something here seems useful, please open an issue to export it from an
-- external module.

module Test.Fun.Internal.Types where

import Data.Maybe (fromMaybe)
import Data.Void (Void)

type FunName = String
type TypeName = String
type ConName = String

-- | The type of 'Text.Show.showsPrec'.
type ShowsPrec r = Int -> r -> String -> String

-- | Dictionary with shrinker and printer.
data Concrete r = Concrete
  { shrinkC :: r -> [r]
  , showsPrecC :: ShowsPrec r
  }

infixr 1 :->

-- | Testable representation of functions @(a -> r)@.
--
-- This representation supports random generation, shrinking, and printing,
-- for property testing with QuickCheck or Hedgehog.
--
-- Higher-order functions can be represented ('Test.Fun.cogenFun').
data a :-> r where
  -- | Constant function, ignore the argument.
  Const :: r -> a :-> r

  -- | Apply the argument @(a -> b)@ to a value @a@, stored in some representation @w@,
  -- and describe what to do with the result @b@ in another function.
  CoApply :: Concrete w -> w -> (w -> a) -> (b :-> (a -> b) :-> r) -> (a -> b) :-> r

  -- | Apply some function to the argument @a@.
  Apply :: FunName -> (a -> b) -> (b :-> r) -> (a :-> r)

  -- | Pattern-match on the argument (in some ADT).
  -- The branches may be incomplete, in which case a default value @r@ is used.
  Case :: TypeName -> (a -> x) -> Branches x r -> r -> (a :-> r)

  -- | Pattern-match on the argument (of some integral type).
  CaseInteger :: TypeName -> (a -> Integer) -> Bin r -> r -> (a :-> r)

  -- | There is no value for the argument, so we're done.
  Absurd :: (a -> Void) -> a :-> r

  -- | Marker for truncating infinite representations.
  ToShrink :: (a :-> r) -> a :-> r

-- | Representation of the branches of a 'Case'.
data Branches x r where
  Fail :: Branches x r
  Alt :: !(Branches x r) -> !(Branches y r) -> Branches (Either x y) r
  Pat :: ConName -> !(Fields x r) -> Branches x r

-- | Representation of one branch of a 'Case'.
data Fields x r where
  NoField :: r -> Fields () r
  Field :: !(Fields x (y :-> r)) -> Fields (x, y) r

-- | Representation of branches of a 'CaseInteger'.
data Bin r
  = BinEmpty
  | BinAlt (Maybe r) (Bin r) (Bin r)
  | BinToShrink (Bin r)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- Smart constructors to enforce some invariants

coapply :: Concrete w -> w -> (w -> a) -> (b :-> (a -> b) :-> r) -> (a -> b) :-> r
coapply _ _ _ (Const h) = h
coapply c w f h = CoApply c w f h

apply :: FunName -> (a -> b) -> (b :-> r) -> (a :-> r)
apply _ _ (Const r) = Const r
apply fn f h = Apply fn f h

case_ :: TypeName -> (a -> x) -> Branches x r -> r -> (a :-> r)
case_ _ _ Fail r = Const r
case_ tn f b r = Case tn f b r

caseInteger :: TypeName -> (a -> Integer) -> Bin r -> r -> (a :-> r)
caseInteger _ _ BinEmpty r = Const r
caseInteger tn f b r = CaseInteger tn f b r

alt :: Branches x r -> Branches y r -> Branches (Either x y) r
alt Fail Fail = Fail
alt b1 b2 = Alt b1 b2

binAlt :: r -> Bin r -> Bin r -> Bin r
binAlt = BinAlt . Just

--

applyFun :: (a :-> r) -> a -> r
applyFun (Const r) _ = r
applyFun (CoApply _ w f h) x = applyFun (applyFun h (x (f w))) x
applyFun (Apply _ f h) x = applyFun h (f x)
applyFun (Case _ f b r) x = applyBranches r b (f x)
applyFun (CaseInteger _ f b r) x = applyBin r b (f x)
applyFun (Absurd f) x = case f x of {}
applyFun (ToShrink h) x = applyFun h x

applyBranches :: r -> Branches x r -> x -> r
applyBranches r Fail _ = r
applyBranches r (Alt b1 _) (Left  x) = applyBranches r b1 x
applyBranches r (Alt _ b2) (Right y) = applyBranches r b2 y
applyBranches _ (Pat _ d) x = applyFields d x

applyFields :: Fields x r -> x -> r
applyFields (NoField h) _ = h
applyFields (Field h) (x, y) = applyFun (applyFields h x) y

applyBin :: r -> Bin r -> Integer -> r
applyBin r BinEmpty _ = r
applyBin r (BinAlt r0 b0 b1) x = case compare x 0 of
  EQ -> fromMaybe r r0
  GT -> applyBin' r b0 (x - 1)
  LT -> applyBin' r b1 (- x - 1)
applyBin r (BinToShrink b) x = applyBin r b x

applyBin' :: r -> Bin r -> Integer -> r
applyBin' r BinEmpty _ = r
applyBin' r (BinAlt r0 b0 b1) x
  | x == 0 = fromMaybe r r0
  | x `div` 2 == 0 = applyBin' r b0 (x `div` 2)
  | otherwise      = applyBin' r b1 (x `div` 2)
applyBin' r (BinToShrink b) x = applyBin' r b x

--

instance Functor ((:->) a) where
  fmap g h0 = case h0 of
    Const r -> Const (g r)
    Apply fn f h -> Apply fn f (fmap g h)
    CoApply c w f h -> CoApply c w f (fmap (fmap g) h)
    Case tn f b r -> Case tn f (fmap g b) (g r)
    CaseInteger tn f b r -> CaseInteger tn f (fmap g b) (g r)
    Absurd f -> Absurd f
    ToShrink h -> ToShrink (fmap g h)

instance Functor (Branches x) where
  fmap g b = case b of
    Fail -> Fail
    Alt b1 b2 -> Alt (fmap g b1) (fmap g b2)
    Pat cn d -> Pat cn (fmap g d)

instance Functor (Fields x) where
  fmap g d = case d of
    NoField h -> NoField (g h)
    Field h -> Field (fmap (fmap g) h)

instance Foldable ((:->) a) where
  foldMap foldR h0 = case h0 of
    Const r -> foldR r
    Apply _ _ h -> foldMap foldR h
    CoApply _ _ _ h -> foldMap (foldMap foldR) h
    Case _ _ b r -> foldMap foldR b <> foldR r
    CaseInteger _ _ b r -> foldMap foldR b <> foldR r
    Absurd _ -> mempty
    ToShrink h -> foldMap foldR h

instance Foldable (Branches x) where
  foldMap foldR b = case b of
    Fail -> mempty
    Alt b1 b2 -> foldMap foldR b1 <> foldMap foldR b2
    Pat _ d -> foldMap foldR d

instance Foldable (Fields x) where
  foldMap foldR d = case d of
    NoField h -> foldR h
    Field h -> foldMap (foldMap foldR) h

instance Traversable ((:->) a) where
  traverse traverseR h0 = case h0 of
    Const r -> Const <$> traverseR r
    Apply fn f h -> Apply fn f <$> traverse traverseR h
    CoApply c w f h -> CoApply c w f <$> traverse (traverse traverseR) h
    Case tn f b r -> Case tn f <$> traverse traverseR b <*> traverseR r
    CaseInteger tn f b r -> CaseInteger tn f <$> traverse traverseR b <*> traverseR r
    Absurd f -> pure (Absurd f)
    ToShrink h -> ToShrink <$> traverse traverseR h

instance Traversable (Branches x) where
  traverse traverseR b = case b of
    Fail -> pure Fail
    Alt b1 b2 -> Alt <$> traverse traverseR b1 <*> traverse traverseR b2
    Pat cn d -> Pat cn <$> traverse traverseR d

instance Traversable (Fields x) where
  traverse traverseR d = case d of
    NoField h -> NoField <$> traverseR h
    Field h -> Field <$> traverse (traverse traverseR) h

truncateFun :: Int -> (r -> t) -> t -> (a :-> r) -> (a :-> t)
truncateFun 0 _ s _ = Const s
truncateFun n truncateR r h0 = case h0 of
  Const s -> Const (truncateR s)
  Apply fn f h -> Apply fn f (truncateFun (n-1) truncateR r h)
  CoApply c w f h -> CoApply c w f (truncateFun (n-1) (truncateFun (n-1) truncateR r) (Const r) h)
  Case tn f b s -> Case tn f (fmap truncateR b) (truncateR s)
  CaseInteger tn f b s -> CaseInteger tn f (truncateBin (n-1) truncateR b) (truncateR s)
  Absurd f -> Absurd f
  ToShrink h -> truncateFun (n-1) truncateR r h

truncateBin :: Int -> (r -> s) -> Bin r -> Bin s
truncateBin 0 _ _ = BinEmpty
truncateBin n truncateR d = case d of
    BinEmpty -> BinEmpty
    BinAlt r d0 d1 -> BinAlt (fmap truncateR r) (go d0) (go d1)
    BinToShrink d' -> go d'
  where go = truncateBin (n-1) truncateR
