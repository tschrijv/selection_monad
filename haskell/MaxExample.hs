{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- | The "greedy algorithms" / password-strength example from
-- @jfp/sections/examples.lhs@, realised via the real 'EffectTH.effect'
-- quasiquoter. Unlike "Section4Example.hs" (which uses 'handlerRet'
-- with an explicit return clause), this exercises 'handler' (no return
-- clause -- defaults to 'return', per prototype.tex's "We can also use
-- |handler| without a return clause").
--
-- Same one deviation as "Section4Example.hs": @Max (operation (...))@
-- instead of @Max { max = operation (...) }@ -- see "EffectTH.hs"'s
-- module header for why real record syntax here is impossible under
-- plain GHC 8.10.2.
--
module MaxExample where

import Data.List (group, maximumBy, sort)
import Data.Monoid (Sum (..))
import EffectTH
import Prelude hiding (max)
import SelectionMonad_ParameterSupport2

[effect|data Max = Max { max :: Op [a] a } |]

-- | Same definition as @maxWith@ in "SelectionMonad_ParameterSupport2.hs"'s
-- commented password example / examples.lhs's @\begin{spec}@ block.
maxWith :: (Monad m, Ord b) => (a -> m b) -> [a] -> m a
maxWith f x = do
  bs <- mapM f x
  let r = maximumBy (\p q -> compare (fst p) (fst q)) $ zip bs [0 ..]
  return $ x !! snd r

len :: (Num r, Monoid r, Functor e) => String -> Sel r e ()
len x = loss (fromIntegral (length x))

distinct :: (Num r, Monoid r, Functor e) => String -> Sel r e ()
distinct x = let i = fromIntegral (length (group (sort x))) in loss (i * i)

password :: (Max_F String :? e, Monoid r, Num r) => Sel r e String
password = do
  s <- perform max ["aaa", "aabb", "abc"]
  len s
  distinct s
  return $ "password is " ++ s

hmax :: (Monoid r, Ord r, Functor e) => Sel r (Max_F String :* e) String -> Sel r e String
hmax = handler (Max (operation (\x l k -> do b <- maxWith l x; k b)))

main :: IO ()
main = print (runSel (hmax password :: Sel (Sum Int) VoidEff String))
