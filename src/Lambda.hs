{-
 -   The Lambda Shell, an interactive environment for evaluating pure untyped lambda terms.
 -   Copyright (C) 2005-2011, Robert Dockins
 -
 -   This program is free software; you can redistribute it and/or modify
 -   it under the terms of the GNU General Public License as published by
 -   the Free Software Foundation; either version 2 of the License, or
 -   (at your option) any later version.
 -
 -   This program is distributed in the hope that it will be useful,
 -   but WITHOUT ANY WARRANTY; without even the implied warranty of
 -   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -   GNU General Public License for more details.
 -
 -   You should have received a copy of the GNU General Public License
 -   along with this program; if not, write to the Free Software
 -   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 -}

{- |
 This module defines the pure lambda calculus and
 some associated operations.

 Lambda terms are represented with de Brujin indicies.  Lambdas
 are annotated with a label for the variable that is used when
 displaying.  Lambda terms may be references to let-bindings;
 these are unfolded in explicit reduction steps.  Let bindings are
 non-recursive; that is, the bound name is not in scope during
 the definition.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Lambda (
-- * Type Definitions
  Bindings
, ReductionStrategy
, Fuel

-- * Lamda Term Datatype
, PureLambda (..)

-- * Comparison Functions
, alphaEq
, normalEq

-- * Auxilary Functions
, lookupBinding
, lookupBindingM
, printLam
, showLam
, lamSubst
, lamShift
, unfoldTop

-- * Reduction Strategies
, lamReduceNull
, lamReduceWHNF
, lamReduceHNF
, lamReduceNF
, lamStrictNF

-- * Evaluation Functions
, lamEvalF
, lamEval
, lamEvalCount
, lamEvalTrace

) where

import Data.List
import qualified Data.Map as Map
import Control.Monad (MonadPlus (..))
import qualified Control.Monad.Fail as Fail

-- Local imports
import qualified Env as Env

------------------------------------------------------------------------------

type Bindings a l = Map.Map String (Maybe (PureLambda a l))

type Fuel = Int

-- From Agda source code: src/full/Agda/Utils/Fail.hs
-- | A pure MonadFail.
newtype Fail a = Fail { runFail :: Either String a }
  deriving (Functor, Applicative, Monad)

instance Fail.MonadFail Fail where
  fail = Fail . Left

runFail_ :: Fail a -> a
runFail_ = either error id . runFail

lookupBinding :: String -> Bindings a l -> Maybe (PureLambda a l)
lookupBinding name b = runFail_ (lookupBindingM name b)

lookupBindingM :: Fail.MonadFail m => String -> Bindings a l -> m (Maybe (PureLambda a l))
lookupBindingM name b =
   case Map.lookup name b of
      Just x -> return x
      Nothing -> fail (concat ["'",name,"' not bound"])

----------------------------------------------------------------
-- | The type of lambda terms;
--   they are polymorphic in an annotation type \'a\' and the type
--   of labels \'l\'.

data PureLambda a l
   = Lam a l (PureLambda a l)
   | App a (PureLambda a l) (PureLambda a l)
   | Var a Int
   | Binding a String
 deriving (Show)

------------------------------------------------------------------
-- | Alpha equivalance on lambda terms.  Defined in the usual
--   way, except that bindings are compared by name.

alphaEq      :: PureLambda a l
             -> PureLambda a l
             -> Bool

alphaEq (Lam _ _ t1)   (Lam _ _ t2)   = alphaEq t1 t2
alphaEq (App _ x1 y1)  (App _ x2 y2)  = alphaEq x1 x2 && alphaEq y1 y2
alphaEq (Var _ i1)     (Var _ i2)     = i1 == i2
alphaEq (Binding _ n1) (Binding _ n2) = n1 == n2
alphaEq _              _              = False


-------------------------------------------------------------------
-- | Defines an eqivalance predicate on normalizing terms, where
--   terms with alpha-equivalant normal forms are in the relation.
--   This function will diverge for non-normalizing terms.

normalEq :: Bindings a l    -- ^ Let bindings in scope
         -> Fuel
         -> PureLambda a l
         -> PureLambda a l
         -> Bool

normalEq binds f t1 t2 =
    let (n1, _) = lamEval binds True lamReduceNF f t1
        (n2, _) = lamEval binds True lamReduceNF f t2
    in alphaEq n1 n2

-------------------------------------------------------------------
-- | Show a lambda term, minimizing parenthises and disambiguating
--   variables in nested scopes with identical labels.

printLam :: Bindings a String -> PureLambda a String -> String
printLam binds lam = showLam binds lam []

showLam :: Bindings a String -> PureLambda a String -> ShowS
showLam binds = showLam_ (Env.empty (Map.keysSet binds)) TopContext 0


data LamContext
   = TopContext
   | AppLeft
   | AppRight
 deriving (Eq)


showLam_     :: Env.Env
             -> LamContext
             -> Int
             -> PureLambda a String
             -> ShowS

showLam_ env c x lam = case lam of

  Binding _ name -> showLambdas env x . showString name

  Var _ v        -> showLambdas env x . showString (Env.lookup v env)

  Lam _ label t  ->
       showParen (c /= TopContext)
       ( showLam_ (Env.insert label env) TopContext (x+1) t )

  App _ t1 t2    ->
       showParen (c == AppRight)
       ( showLambdas env x
       . showLam_ env AppLeft 0 t1
       . showChar ' '
       . showLam_ env AppRight 0 t2
       )


showLambdas :: Env.Env
            -> Int
            -> ShowS

showLambdas _   0 = id
showLambdas env x =
    ( showChar '\\'
    . showString
          (concat . intersperse " " . map (\i -> Env.lookup i env) $ [x-1, x-2 .. 0])
    . showString ". "
    )


-----------------------------------------------------------------------------
-- shifts all free variables by a specified amount
-- ancillary function for substitution

lamShift     :: Int
             -> Int
             -> PureLambda a l
             -> PureLambda a l

lamShift c d v@(Var a x)
   | x >= c    = Var a (x+d)
   | otherwise = v

lamShift c d (Lam a label t)  = Lam a label (lamShift (c+1) d t)
lamShift c d (App a t1 t2)    = App a (lamShift c d t1) (lamShift c d t2)
lamShift _ _ b@(Binding _ _)  = b


------------------------------------------------------------------------------
-- | Capture-avoiding substitution;
--   substitute \'s\' into \'t\', replacing all free variables with index 0.

lamSubst     :: PureLambda a l -- ^ s
             -> PureLambda a l -- ^ t
             -> PureLambda a l

lamSubst s t = lamShift 0 (-1) (lamSubst' (lamShift 0 1 s) 0 0 t)



lamSubst'    :: PureLambda a l
             -> Int
             -> Int
             -> PureLambda a l
             -> PureLambda a l

lamSubst' s var c v@(Var _ x)
   | x == (var+c) = lamShift 0 c s
   | otherwise    = v

lamSubst' s var c (Lam a label t)  = Lam a label (lamSubst' s var (c+1) t)
lamSubst' s var c (App a t1 t2)    = App a (lamSubst' s var c t1) (lamSubst' s var c t2)
lamSubst' _ _   _ b@(Binding _ _)  = b


-------------------------------------------------------------------------------------
-- | The type of reduction strategies.

type ReductionStrategy a l
     = Bindings a l
    -> Bool
    -> PureLambda a l
    -> Maybe (PureLambda a l)


-------------------------------------------------------------------------------------
-- | The \'null\' reduction strategy, which does no reduction
lamReduceNull :: ReductionStrategy a l
lamReduceNull _ _ _ = Nothing

-------------------------------------------------------------------------------------
-- | Single-step normal order reduction to Weak Head Normal Form (WHNF)

lamReduceWHNF :: ReductionStrategy a l

lamReduceWHNF _ _      (App _ (Lam _ _ t1) t2) = Just (lamSubst t2 t1)
lamReduceWHNF b _      (App a t1 t2)           = lamReduceWHNF b True t1   >>= \t1' -> return (App a t1' t2)
lamReduceWHNF _ _      (Lam _ _ _)             = Nothing
lamReduceWHNF _ _      (Var _ _)               = Nothing
lamReduceWHNF b unfold (Binding _ name)        = if unfold then lookupBinding name b else Nothing


-------------------------------------------------------------------------------------
-- | Single-step normal order reduction to Head Normal Form (HNF)

lamReduceHNF :: ReductionStrategy a l

lamReduceHNF _ _      (App _ (Lam _ _ t1) t2) = Just (lamSubst t2 t1)
lamReduceHNF b _      (App a t1 t2)           = lamReduceHNF b True t1   >>= \t1' -> return (App a t1' t2)
lamReduceHNF b unfold (Lam a l t)             = lamReduceHNF b unfold t  >>= \t'  -> return (Lam a l t')
lamReduceHNF _ _      (Var _ _)               = Nothing
lamReduceHNF b unfold (Binding _ name)        = if unfold then lookupBinding name b else Nothing



--------------------------------------------------------------------------------------
-- | Single-step normal order reduction to Normal Form (NF)

lamReduceNF :: ReductionStrategy a l

lamReduceNF _ _      (App _ (Lam _ _ t1) t2) = Just (lamSubst t2 t1)
lamReduceNF b unfold (App a t1 t2)           = (lamReduceNF b True t1   >>= \t1' -> return (App a t1' t2))
                                                 `mplus`
                                               (lamReduceNF b unfold t2 >>= \t2' -> return (App a t1 t2'))
lamReduceNF b unfold (Lam a l t)             = lamReduceNF b unfold t   >>= \t'  -> return (Lam a l t')
lamReduceNF _ _      (Var _ _)               = Nothing
lamReduceNF b unfold (Binding _ name)        = if unfold then lookupBinding name b else Nothing



---------------------------------------------------------------------------------------
-- | Single-step applicative order reduction to Normal Form (NF)

lamStrictNF :: ReductionStrategy a l

lamStrictNF b _      (App a (Lam al l t1) t2) = (lamStrictNF b True t2 >>= \t2' -> return (App a (Lam al l t1) t2'))
                                                  `mplus`
                                                (Just (lamSubst t2 t1))
lamStrictNF b unfold (App a t1 t2)            = (lamStrictNF b True t1   >>= \t1' -> return (App a t1' t2))
                                                  `mplus`
                                                (lamStrictNF b unfold t2 >>= \t2' -> return (App a t1 t2'))
lamStrictNF b unfold (Lam a l t)              = lamStrictNF b unfold t   >>= \t'  -> return (Lam a l t')
lamStrictNF _ _      (Var _ _)                = Nothing
lamStrictNF b unfold (Binding _ name)         = if unfold then lookupBinding name b else Nothing



---------------------------------------------------------------------------------------
-- | Helper for various kinds of evaluation.  Applies the function \'z\' if
--   the evaluation strategy has terminated, and applies \'f\' to the
--   reduced term otherwise.

lamEvalF     :: Bindings a l             -- ^ A set of bindings for unfolding
             -> Bool                     -- ^ Apply full unfolding?
             -> ReductionStrategy a l    -- ^ Reduction strategy to use
             -> (PureLambda a l -> b)    -- ^ f
             -> (PureLambda a l -> b)    -- ^ z
             -> PureLambda a l           -- ^ The term to reduce
             -> b

lamEvalF b unfold reduce f z x =
   case reduce b unfold x of
        Just x' -> f x'
        Nothing -> z x




-------------------------------------------------------------------------------------
-- | Big-step reduction; that is, apply the reduction strategy until
--   it fails to reduce any futher.

lamEval :: forall a l.
  Bindings a l              -- ^ A set of bindings for unfolding
  -> Bool                   -- ^ Apply full unfolding ?
  -> ReductionStrategy a l  -- ^ Reduction strategy to use
  -> Fuel                   -- ^ Maximum number of reductions
  -> PureLambda a l         -- ^ The term to reduce
  -> (PureLambda a l, Fuel) -- ^ The evaluated term

lamEval bind unfold red f = eval f
  where
  evalF :: (PureLambda a l -> (PureLambda a l, Fuel))
        -> (PureLambda a l -> (PureLambda a l, Fuel))
        -> PureLambda a l
        -> (PureLambda a l, Fuel)
  evalF  = lamEvalF bind unfold red

  eval :: Fuel
       -> PureLambda a l
       -> (PureLambda a l, Fuel)
  eval f x =
    if f == 0
    then (x, f)
    else evalF (\t -> eval (pred f) t) (\t -> (t, f)) x



-------------------------------------------------------------------------------------
-- | Big-step reduction that counts the number of reductions performed

lamEvalCount :: forall a l.
  Bindings a l                    -- ^ A set of bindings for unfolding
  -> Bool                         -- ^ Apply full unfolding ?
  -> ReductionStrategy a l        -- ^ Reduction strategy to use
  -> Fuel                         -- ^ Maximum number of reductions
  -> PureLambda a l               -- ^ The term to reduce
  -> (PureLambda a l, Int, Fuel)  -- ^ The evaluated term and reduction count

lamEvalCount bind unfold red f = eval 0 f
  where
  evalF :: (PureLambda a l -> (PureLambda a l, Int, Fuel))
        -> (PureLambda a l -> (PureLambda a l, Int, Fuel))
        -> PureLambda a l
        -> (PureLambda a l, Int, Fuel)
  evalF = lamEvalF bind unfold red

  eval :: Int
       -> Fuel
       -> PureLambda a l
       -> (PureLambda a l, Int, Fuel)
  eval n f x  =
    if f == 0
    then (x, n, f)
    else evalF (\t -> eval (succ n) (pred f) t) (\t -> (t, n, f)) x


-------------------------------------------------------------------------------------
-- | Traced evaluation; the result is a list of the reduction
--   steps taken by the given reduction stragegy.  A non-terminating
--   term (under the given strategy) will result in an infinite list.
--   For a normalizing term, the last element in the list will be the
--   normal  form.

lamEvalTrace :: Bindings a l          -- ^ A set of bindings for unfolding
             -> Bool                  -- ^ Apply full unfolding ?
             -> ReductionStrategy a l -- ^ Reduction strategy to use
             -> PureLambda a l        -- ^ The term to reduce
             -> [PureLambda a l]      -- ^ The list of intermediate reductions

lamEvalTrace bind unfold red = eval
  where evalF  = lamEvalF bind unfold red
        eval x = evalF ((x:) . eval) (:[]) x





-----------------------------------------------------------------------------------------
-- | If a lambda term is just a let binding, this function will unfold it; otherwise
--   it will return the term unchanged.  It will result in bottom if the term is not bound.

unfoldTop     :: Bindings () String
              -> PureLambda () String
              -> PureLambda () String

unfoldTop binds (Binding a x) = maybe (Binding a x) id $
                                  Map.findWithDefault (error $ concat ["'",x,"' not bound"]) x binds
unfoldTop _     x             = x
