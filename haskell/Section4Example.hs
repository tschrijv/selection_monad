{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- | The worked example from @jfp/sections/prototype.tex@, sec:interface
-- (lines ~317-387), realised via the real 'EffectTH.effect' quasiquoter
-- (not a hand-written stand-in).
--
-- GHC's TH staging restriction requires this to live in a module
-- different from the one defining the @effect@ quasiquoter
-- (see "EffectTH.hs").
--
-- One textual correction from the paper's rendered LaTeX: the handler
-- clause below uses @(++)@ (list append), not the "@(+)@" the typeset
-- PDF shows. @(+) :: [Bool] -> [Bool] -> [Bool]@ has no 'Num' instance
-- and cannot typecheck; @(++)@ does, and is exactly what the equivalent
-- hand-written @nDetAlg@ in "SelectionMonad.hs" uses (@return (x ++
-- y)@). This is almost certainly lhs2TeX's pretty-printer collapsing
-- the @++@ operator glyph for display, not a change in semantics; with
-- it, the example below reproduces the paper's claimed output exactly.
module Section4Example where

import EffectTH
import SelectionMonad_ParameterSupport2

[effect|data NDet = NDet { decide :: Op () Bool } |]

-- | (See the module header on 'EffectTH' for why this is
-- @NDet (operation (...))@ rather than the paper's
-- @NDet { decide = operation (...) }@ -- real GHC record syntax here
-- would force a top-level name clash with the generated @decide@
-- perform-function.)
pgm :: Sel () VoidEff [Bool]
pgm =
  handlerRet
    (\x -> return [x])
    (NDet (operation (\x l k -> (++) <$> k True <*> k False)))
    $ do
      y <- perform decide ()
      return (not y)

main :: IO ()
main = print (runSel pgm)
