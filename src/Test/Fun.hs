{-# LANGUAGE TypeFamilies, TypeOperators #-}

-- | Testable representation of (higher-order) functions.

module Test.Fun
  ( -- * Testable functions
    (:->)()
  , applyFun
  , applyFun2
  , applyFun3

    -- * Shrink and show
  , shrinkFun
  , showsPrecFun
  , indent
  , ShowsPrec

    -- * Cogenerators
  , Co
  , cogenEmbed
  , cogenIntegral
  , cogenIntegral'
  , cogenFun
  , cogenApply
  , cogenConst
  , Concrete(..)
  , cogenGeneric
  , (:+)(..)
  , cogenList

  , FunName
  , TypeName

    -- ** @CoArbitrary@
  , CoArbitrary(..)
  , coarbitraryGeneric

    -- ** Generic classes
  , GCoGen()
  , GCoArbitrary()
  , GSumCo
  ) where

import Test.Fun.Internal.Types
  ((:->), applyFun, applyFun2, applyFun3, Concrete(..), ShowsPrec, FunName, TypeName)
import Test.Fun.Internal.CoArbitrary
import Test.Fun.Internal.Pretty (showsPrecFun, indent)
import Test.Fun.Internal.Shrink (shrinkFun)
import Test.Fun.Internal.Orphan ()
