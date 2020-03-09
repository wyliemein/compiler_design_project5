{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

--------------------------------------------------------------------------------
-- | The entry point for the compiler: a function that takes a Text
--   representation of the source and returns a (Text) representation
--   of the assembly-program string representing the compiled version
--------------------------------------------------------------------------------

module Language.Egg.Compiler ( compiler, compile ) where

import           Data.Monoid
import           Control.Arrow                    ((>>>))
import           Prelude                  hiding (compare)
import           Control.Monad                   (void)
import           Data.Maybe
import           Data.Bits                       (shift)
import           Language.Egg.Types
import           Language.Egg.Parser     (parse)
import           Language.Egg.Checker    (check, errUnboundVar)
import           Language.Egg.Normalizer (anormal)
import           Language.Egg.Label
import           Language.Egg.Asm        (asm)


--------------------------------------------------------------------------------
compiler :: FilePath -> Text -> Text
--------------------------------------------------------------------------------
compiler f = parse f >>> check >>> anormal >>> tag >>> tails >>> compile >>> asm


--------------------------------------------------------------------------------
-- | The compilation (code generation) works with AST nodes labeled by @Ann@
--------------------------------------------------------------------------------
type Ann   = ((SourceSpan, Int), Bool)
type AExp  = AnfExpr Ann
type IExp  = ImmExpr Ann
type ABind = Bind    Ann
type ADcl  = Decl    Ann
type APgm  = Program Ann

instance Located Ann where
  sourceSpan = fst . fst

instance Located a => Located (Expr a) where
  sourceSpan = sourceSpan . getLabel

annTag :: Ann -> Int
annTag = snd . fst

annTail :: Ann -> Bool
annTail = snd


--------------------------------------------------------------------------------
compile :: APgm -> [Instruction]
--------------------------------------------------------------------------------
compile (Prog ds e) = compileBody emptyEnv e
                      ++ concatMap compileDecl ds

compileDecl :: ADcl -> [Instruction]
compileDecl (Decl f xs e l) = [ ILabel (DefFun (bindId f))] ++  compileBody (paramsEnv xs) e

paramsEnv :: [Bind a] -> Env
paramsEnv xs = fromListEnv (zip (bindId <$> xs) [-2, -3..])

compileBody :: Env -> AExp -> [Instruction]
compileBody env e = funInstrs (countVars e) (compileEnv env e)

-- | @funInstrs n body@ returns the instructions of `body` wrapped
--   with code that sets up the stack (by allocating space for n local vars)
--   and restores the callees stack prior to return.

funInstrs :: Int -> [Instruction] -> [Instruction]
funInstrs n instrs
  = funEntry n
 ++ instrs
 ++ funExit
 ++ [IRet]

-- FILL: insert instructions for setting up stack for `n` local vars
funEntry :: Int -> [Instruction]
funEntry n = [ IPush (Reg EBP)
              , IMov  (Reg EBP) (Reg ESP)
              , ISub  (Reg ESP) (Const (4 * n))
              ]

-- FILL: clean up stack & labels for jumping to error
funExit :: [Instruction]
funExit = [ IMov (Reg ESP) (Reg EBP)
          , IPop  (Reg EBP)
          ]


-- Prelude: Intialize ESI with start position of Heap passed in by the runtime
prelude :: [Instruction]
prelude = [ IMov (Reg ESI) (RegOffest 4 ESP)
          , IAdd (Reg ESI) (Const 8)
          , I and (Reg ESI) (HexConst 0xfffffff8)
          ]

--------------------------------------------------------------------------------
-- | @countVars e@ returns the maximum stack-size needed to evaluate e,
--   which is the maximum number of let-binds in scope at any point in e.
--------------------------------------------------------------------------------
countVars :: AnfExpr a -> Int
--------------------------------------------------------------------------------
countVars (Let _ e b _)  = max (countVars e)  (1 + countVars b)
countVars (If v e1 e2 _) = maximum [countVars v, countVars e1, countVars e2]
countVars _              = 0

--------------------------------------------------------------------------------
compileEnv :: Env -> AExp -> [Instruction]
--------------------------------------------------------------------------------
compileEnv env v@Number {}       = [ compileImm env v  ]

compileEnv env v@Boolean {}      = [ compileImm env v  ]

compileEnv env v@Id {}           = [ compileImm env v  ]

compileEnv env e@Let {}          = is ++ compileEnv env' body
  where
    (env', is)                   = compileBinds env [] binds
    (binds, body)                = exprBinds e

compileEnv env (Prim1 o v l)     = compilePrim1 l env o v

compileEnv env (Prim2 o v1 v2 l) = compilePrim2 l env o v1 v2

compileEnv env (If v e1 e2 l)    = compileIf l env v e1 e2

compileEnv env (App f vs l)
  | annTail l                    = tailcall (DefFun f) (param env <$> vs)
  | otherwise                    = call (DefFun f) (param env <$> vs)

compileEnv env (Tuple v1 v2)      = compieExpr env v1 v2

call :: Label -> [Arg] -> [Instruction]
call f a = concatMap push (reverse a) ++
           [ ICall f
           , IAdd (Reg ESP) (Const (4 * n))]
  where
    n        = length a
    push arg = [ IPush arg]


tailcall :: Label -> [Arg] -> [Instruction]
tailcall f a = concatMap move (zip a [0,1..]) ++
               [ IMov (Reg ESP) (Reg EBP)
               , IPop (Reg EBP)
               , IJmp f]
  where
    move (arg,n) = [ IMov (Reg EAX)              arg 
                   , IMov (RegOffset (8+n*4) EBP)  (Reg EAX)]
 
-------------------------------------------------------------------------------
compilePrim1 :: Ann -> Env -> Prim1 -> IExp -> [Instruction]
compilePrim1 _ env Add1 v = assertType env v TNumber 
                            ++ [ IAdd (Reg EAX) (Const 2) 
                               , IJo (DynamicErr ArithOverflow)]
compilePrim1 _ env Sub1 v = assertType env v TNumber  
                            ++ [ IAdd (Reg EAX) (Const (-2)) 
                               , IJo (DynamicErr ArithOverflow)]
compilePrim1 _ env Print v = compileEnv env v ++
                             [ IMov (Reg EBX) (Reg EAX)
                             , IPush (Reg EBX)
                             , ICall (Builtin "print")]
compilePrim1 _ env IsNum v = compileEnv env v ++
                            [ IAnd (Reg EAX) (HexConst 0x00000001)      
                            , IShl (Reg EAX) (Const 31)
                            , IOr  (Reg EAX) (typeMask TBoolean)
                            , IXor (Reg EAX) (HexConst 0x80000000)]
compilePrim1 _ env IsBool v = compileEnv env v ++
                            [ IAnd (Reg EAX) (HexConst 0x00000001)
                            , IShl (Reg EAX) (Const 31)
                            , IOr  (Reg EAX) (typeMask TBoolean)]


compilePrim2 :: Ann -> Env -> Prim2 -> IExp -> IExp -> [Instruction]
compilePrim2 _ env Plus v1 v2 = assertType env v1 TNumber
                                ++ assertType env v2 TNumber
                                ++ [ IMov (Reg EAX) (immArg env v1)
                                , IAdd (Reg EAX) (immArg env v2)
                                , IJo (DynamicErr ArithOverflow)]
compilePrim2 _ env Minus v1 v2  = assertType env v1 TNumber
                                ++ assertType env v2 TNumber
                                ++ [ IMov (Reg EAX) (immArg env v1)
                                , ISub (Reg EAX) (immArg env v2)
                                , IJo (DynamicErr ArithOverflow)]
compilePrim2 _ env Times v1 v2  = assertType env v1 TNumber
                                ++ assertType env v2 TNumber
                                ++ [ IMov (Reg EAX) (immArg env v1)
                                , IMul (Reg EAX) (immArg env v2)
                                , IJo (DynamicErr ArithOverflow)
                                , ISar (Reg EAX) (Const 1)]

compilePrim2 _ env Greater v1 v2  = assertType env v1 TNumber
                                  ++ assertType env v2 TNumber
                                  ++ [ IMov (Reg EAX) (immArg env v2)
                                  , ISub (Reg EAX) (immArg env v1)
                                  , IAnd (Reg EAX) (HexConst 0x80000000)
                                  , IOr  (Reg EAX) (typeMask TBoolean)
                                  ]

compilePrim2 _ env Less v1 v2  = assertType env v1 TNumber
                                  ++ assertType env v2 TNumber
                                  ++ [ IMov (Reg EAX) (immArg env v1)
                                  , ISub (Reg EAX) (immArg env v2)
                                  , IAnd (Reg EAX) (HexConst 0x80000000)
                                  , IOr  (Reg EAX) (typeMask TBoolean)
                                  ]

compilePrim2 l env Equal v1 v2  = assertType env v1 TNumber
                                ++ assertType env v2 TNumber
                                ++ [ IMov (Reg EAX) (immArg env v1)
                                , ICmp (Reg EAX) (immArg env v2)
                                , IJe (BranchTrue (annTag l))
                                , IMov (Reg EAX) (repr False)
                                , IJmp (BranchDone (annTag l))
                                , ILabel (BranchTrue (annTag l))
                                , IMov (Reg EAX) (repr True)
                                , ILabel (BranchDone (annTag l))
                                ]
                    
compileExpr env (Tuple v1 v2) = pairAlloc 
                                ++ pairCopy First (immArg env v1) 
                                ++ pairCopy Second (immArg env v2) 
                                ++ setTag (Reg EAX) (TPair)

pairAlloc :: Asm 
pairAlloc = [ IMov (Reg EAX) (Reg ESI)
            , IAdd (Reg ESI) (Const 8)
            ]

pairCopy :: Field -> Arg -> Asm
pairCopy fld a = [ IMov (Reg EBX) a
                  , IMov (pairAddr fld) (Reg EBX)
                  ]

pairAddr :: Field -> Arg
pairAddr fld = Sized DwordPtr (RegOffset (4 * fieldOffset fld) EAX)

fieldOffset :: Field -> Int
fieldOffset First = 0
fieldOffset Second = 1


compileIf :: Ann -> Env -> IExp -> AExp -> AExp -> [Instruction]
compileIf l env v e1 e2 = assertType env v TBoolean
                          ++ [ IMov (Reg EAX) (immArg env v) 
                             , ICmp (Reg EAX) (repr True)
                             , IJe (BranchTrue (annTag l))
                             ]
                          ++ compileEnv env e2
                          ++ [ IJmp   (BranchDone (annTag l))
                             , ILabel (BranchTrue (annTag l))
                             ]
                          ++ compileEnv env e1
                          ++ [ ILabel (BranchDone (annTag l)) ]

assertType :: Env -> IExp -> Ty -> [Instruction]
assertType env v ty
  = [ IMov (Reg EAX) (immArg env v)
    , IMov (Reg EBX) (Reg EAX)
    , IAnd (Reg EBX) (typeMask ty)
    , ICmp (Reg EBX) (typeTag  ty)
    , IJne (DynamicErr (TypeError ty))]

---------------------------------------------------------------------

compileImm :: Env -> IExp -> Instruction
compileImm env v = IMov (Reg EAX) (immArg env v)

compileBinds :: Env -> [Instruction] -> [(ABind, AExp)] -> (Env, [Instruction])
compileBinds env is []     = (env, is)
compileBinds env is (b:bs) = compileBinds env' (is <> is') bs
  where
    (env', is')            = compileBind env b

compileBind :: Env -> (ABind, AExp) -> (Env, [Instruction])
compileBind env (x, e) = (env', is)
  where
    is                 = compileEnv env e
                      <> [IMov (stackVar i) (Reg EAX)]
    (i, env')          = pushEnv x env

immArg :: Env -> IExp -> Arg
immArg _   (Number n _)  = repr n
immArg _   (Boolean b _) = repr b
immArg env e@(Id x _)    = stackVar (fromMaybe err (lookupEnv x env))
  where
    err                  = abort (errUnboundVar (sourceSpan e) x)
immArg _   e             = panic msg (sourceSpan e)
  where
    msg                  = "Unexpected non-immExpr in immArg: " <> show (void e)

param :: Env -> IExp -> Arg
param env v = Sized DWordPtr (immArg env v)

stackVar :: Int -> Arg
stackVar i = RegOffset (-4 * i) EBP


--------------------------------------------------------------------------------
-- | Representing Values
--------------------------------------------------------------------------------

class Repr a where
  repr :: a -> Arg

instance Repr Bool where
  repr True  = HexConst 0xffffffff
  repr False = HexConst 0x7fffffff

instance Repr Int where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Integer where
  repr n = Const (fromIntegral (shift n 1))

typeTag :: Ty -> Arg
typeTag TNumber   = HexConst 0x00000000
typeTag TBoolean  = HexConst 0x7fffffff
typeTag TTuple    = HexConst 0x00000001

typeMask :: Ty -> Arg
typeMask TNumber  = HexConst 0x00000001
typeMask TBoolean = HexConst 0x7fffffff
typeMask TTuple   = HexConst 0x00000007

setTag :: Register -> Ty -> Asm
setTag r ty = [IAdd (Reg r) (typrTag ty) ]