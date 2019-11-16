{-# LANGUAGE TypeApplications, TypeOperators #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Test.Fun.Internal.Pretty
import Test.Fun.Internal.Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "tests"
  [ testFunctionPretty
  ]

prettyFun_ :: (a :-> String) -> String
prettyFun_ = prettyFun tConst

testFunctionPretty :: TestTree
testFunctionPretty = testGroup "pretty"
  [ testCase "case"
      $ "case a0 :: Either _ _ of { Left a1 -> 0 ; Right a1 -> case a1 of {} }"
      @=? prettyFun_
        (Case "Either _ _" id
          (Alt
            (Pat "Left" (Field (NoField (Const "0"))))
            (Pat "Right" (Field (NoField (Absurd id))))) "0")
  , testCase "coapply"
      $ "case a0 0 of {}"
      @=? prettyFun_ (CoApply hardConcrete (0 :: Int) id (Absurd id))
  , testCase "apply"
      $ "case f a0 of {}"
      @=? prettyFun_ (Apply "f" id (Absurd id))
  , testCase "case-Integer"
      $ "case a0 :: Integer of { -1 -> -1 ; 0 -> 0 ; 1 -> 1 ; _ -> 2 }"
      @=? prettyFun_
        (CaseInteger "Integer" id
          (binAlt "0" (binAlt "1" BinEmpty BinEmpty) (binAlt "-1" BinEmpty BinEmpty)) "2")
  ]

