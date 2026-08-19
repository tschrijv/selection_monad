{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}


module InstSelect where

import SelectionMonad_ParameterSupport2
import Prelude hiding (min, max)
import Control.Monad (join)
import Data.Monoid (Sum)



type Temp = Int

data Tree = 
	T_Move Tree Tree 
  | T_Binop Bop Tree Tree
  | T_Mem Tree
  | T_Const Int
  | T_Temp Temp
  | FP

data Bop = Plus | Times

data Inst = ADD | MUL | ADDI | LOAD | STORE | MOVEM deriving Show

exTree :: Tree
exTree = T_Move (T_Mem (T_Binop Plus 
								(T_Mem (T_Binop Plus FP (T_Const 12)))
								(T_Binop Times 
										 FP 
										 (T_Const 8))
						))
				(T_Mem (T_Binop Plus FP (T_Const 4)))

isReg :: Tree -> Bool
isReg (T_Temp _) = True
isReg FP         = True
isReg _          = False
 
operands :: [Tree] -> [Tree]
operands = filter (not . isReg)
 
isConst :: Tree -> Bool
isConst (T_Const _) = True
isConst _           = False
 
-- +(e, CONST c) / +(CONST c, e) の形なら、定数でない側を返す
plusConst :: Tree -> [Tree]
plusConst (T_Binop Plus a b) = [a | isConst b] ++ [b | isConst a]
plusConst _                  = []                  

inst_candidate :: Tree -> [(Inst, [Tree])]
inst_candidate tree = case tree of
  T_Move (T_Mem addr) src ->
       [ (STORE, operands [a, src]) | a <- plusConst addr ] 
    ++ [ (STORE, operands [src]) | T_Const i <- [addr]]  
    ++ [ (STORE, operands [addr, src]) ]                      
    ++ [ (MOVEM, operands [addr, s]) | T_Mem s <- [src] ]     
  T_Move _ _ -> []           
 
  T_Mem addr ->
       [ (LOAD, operands [a]) | a <- plusConst addr ]
    ++ [ (LOAD, []) | T_Const i <- [addr]]         
    ++ [ (LOAD, operands [addr]) ]                           
 
  T_Binop Plus a b ->
       [ (ADDI, operands [x]) | x <- plusConst tree ]        
    ++ [ (ADD, operands [a, b]) ]                             
 
  T_Binop Times a b -> [ (MUL, operands [a, b]) ]            
 
  T_Const _ -> [ (ADDI, []) ]                                
  T_Temp _  -> [] 
  FP -> []                                           

cost_inst :: Inst -> Sum Int
cost_inst inst = 1



inst_select :: (Min (Inst, [Tree]) :? e) => Tree -> Sel (Sum Int) e [Inst]
inst_select tree = do
    let lst = inst_candidate tree
    (inst, subtrees) <- min lst
    loss $ cost_inst inst
    subinsts <- fmap join $ sequence $ map inst_select subtrees
    return (inst : subinsts)

selectResult :: ([Inst], Sum Int)
selectResult = run $ hMin @(Inst, [Tree]) $ inst_select exTree

