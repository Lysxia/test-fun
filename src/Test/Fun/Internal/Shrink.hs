{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators #-}

-- | Shrinker for representation of functions.
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

module Test.Fun.Internal.Shrink where

import Test.Fun.Internal.Types

-- | Simplify function.
shrinkFun :: forall a r. (r -> [r]) -> (a :-> r) -> [a :-> r]
shrinkFun shrinkR = go where
  go :: forall b. (b :-> r) -> [b :-> r]
  go (ToShrink h) = go h ++ [h]
  go (Absurd _) = []
  go (Const r) = fmap Const (shrinkR r)
  go (CoApply c a f h) = fmap (coapply c a f) (shrinkFun go h) ++ fmap (\a' -> CoApply c a' f h) (shrinkC c a)
  go (Apply fn f h) = apply fn f <$> go h
  go (Case tn f b r)
    =  Const r
    :  fmap (\b' -> case_ tn f b' r) (shrinkBranches shrinkR b)
    ++ fmap (\r' -> Case tn f b r') (shrinkR r)
  go (CaseInteger tn f b r)
    =  root b
    :  fmap (\b' -> caseInteger tn f b' r) (shrinkBin shrinkR b)
    ++ fmap (\r' -> CaseInteger tn f b r') (shrinkR r)
   where
    root BinEmpty = Const r
    root (BinAlt Nothing _ _) = Const r
    root (BinAlt (Just r') _ _) = Const r'
    root (BinToShrink b') = root b'

shrinkBranches :: forall x r. (r -> [r]) -> Branches x r -> [Branches x r]
shrinkBranches shrinkR = go where
  go :: forall y. Branches y r -> [Branches y r]
  go Fail = []
  go (Alt b1 b2) = Fail : fmap (\b1' -> alt b1' b2) (go b1) ++ fmap (alt b1) (go b2)
  go (Pat cn d) = Fail : fmap (Pat cn) (shrinkFields shrinkR d)

shrinkFields :: forall x r. (r -> [r]) -> Fields x r -> [Fields x r]
shrinkFields shrinkR = go where
  go :: forall y. Fields y r -> [Fields y r]
  go (NoField r) = fmap NoField (shrinkR r)
  go (Field h) = fmap Field (shrinkFields (shrinkFun shrinkR) h)

shrinkBin :: forall r. (r -> [r]) -> Bin r -> [Bin r]
shrinkBin shrinkR = go where
  go BinEmpty = []
  go (BinAlt r b0 b1) =
    BinEmpty
      :  fmap (\r' -> BinAlt r' b0 b1) (shrinkMaybe shrinkR r)
      ++ fmap (\b0' -> BinAlt r b0' b1) (go b0)
      ++ fmap (\b1' -> BinAlt r b0 b1') (go b1)
  go (BinToShrink b) = go b' ++ [b'] where b' = binToShrink b

binToShrink :: forall r. Bin r -> Bin r
binToShrink BinEmpty = BinEmpty
binToShrink (BinAlt r b0 b1) = BinAlt r (BinToShrink b0) (BinToShrink b1)
binToShrink (BinToShrink b) = b  -- Should not happen, but no problem if it does.

shrinkMaybe :: (r -> [r]) -> Maybe r -> [Maybe r]
shrinkMaybe _ Nothing = []
shrinkMaybe shrinkR (Just r) = Nothing : fmap Just (shrinkR r)
