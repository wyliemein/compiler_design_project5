{-# LANGUAGE FlexibleContexts #-}

--------------------------------------------------------------------------------
-- | This module contains the code for converting an `Expr` to a "A-Normal" form.
--------------------------------------------------------------------------------
module Language.Egg.Checker
  ( -- * Top-level Static Checker
    check

    -- * Error Constructors
  , errUnboundVar
  , errUnboundFun
  ) where

import           Control.Exception
import           Text.Printf        (printf)
import           Language.Egg.Types
import           Language.Egg.Utils

--------------------------------------------------------------------------------
check :: BareProgram -> BareProgram
--------------------------------------------------------------------------------
check p = case wellFormed p of
            [] -> p
            es -> throw es

-- | Map from function name to arity
type FunEnv = Env

--------------------------------------------------------------------------------
-- | `wellFormed p` returns the list of errors for a program `p`
--------------------------------------------------------------------------------
wellFormed :: BareProgram -> [UserError]
--------------------------------------------------------------------------------
wellFormed (Prog ds e) = duplicateFunErrors ds
                      ++ concatMap (wellFormedD fEnv) ds
                      ++ wellFormedE fEnv emptyEnv e
  where
    fEnv               = fromListEnv [(bindId f, length xs) | Decl f xs _ _ <- ds]

--------------------------------------------------------------------------------
-- | `wellFormedD fEnv vEnv d` returns the list of errors for a func-decl `d`
--------------------------------------------------------------------------------
wellFormedD :: FunEnv -> BareDecl -> [UserError]
wellFormedD fEnv (Decl _ xs e _) = error "TBD:wellFormedD"

--------------------------------------------------------------------------------
-- | `wellFormedE vEnv e` returns the list of errors for an expression `e`
--------------------------------------------------------------------------------
wellFormedE :: FunEnv -> Env -> Bare -> [UserError]
wellFormedE fEnv env e = error "TBD:wellFormedE"

--------------------------------------------------------------------------------
-- | Error Checkers: In each case, return an empty list if no errors.
--------------------------------------------------------------------------------
duplicateFunErrors :: [BareDecl] -> [UserError]
duplicateFunErrors
  = fmap errDupFun
  . concat
  . dupBy (bindId . fName)

-- | `maxInt` is the largest number you can represent with 31 bits (accounting for sign
--    and the tag bit.

maxInt :: Integer
maxInt = 1073741823

--------------------------------------------------------------------------------
-- | Error Constructors: Use these functions to construct `UserError` values
--   when the corresponding situation arises. e.g see how `errDupFun` is used.
--------------------------------------------------------------------------------

errDupFun d       = mkError (printf "duplicate function '%s'" (pprint f))    (sourceSpan f) where f = fName d
errDupParam     x = mkError (printf "duplicate parameter '%s'" (bindId x)) (sourceSpan x)
errDupBind      x = mkError (printf "shadow binding '%s'" (bindId x))      (sourceSpan x)
errLargeNum   l n = mkError (printf "number '%d' is too large" n) l
errUnboundVar l x = mkError (printf "unbound variable '%s'" x) l
errUnboundFun l f = mkError (printf "function '%s' is not defined" f) l
errCallArity  l f = mkError (printf "wrong arity of arguments at call of %s" f) l
