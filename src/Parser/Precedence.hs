{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

{-# LANGUAGE OverloadedStrings #-}

module Parser.Precedence (reorderExprs) where

import Basic.Location
import Basic.Fixity
import Support.Pretty
import Parser.Syntax
import Parser.SyntaxDump
import Typing.TcM

import Control.Lens.Plated
import Control.Lens
import Control.Monad
import Data.Text (pack, Text)
import qualified Data.Map as M

type PrecMap = M.Map Text (Precedence Text)

reorderExprs :: Program Text -> TcM (Program Text)
reorderExprs program = do
  let operSignatures = program ^.. to _programTopFunctions
                                 . folded
                                 . to unLocated
                                 . to _funSignature
                                 . to unLocated
                                 . filtered _sigIsOperator
  userPrecs <- do
        forM operSignatures $ \fn -> do
          let (Fixity assoc level) = maybe defaultFixity unLocated (_sigFixity fn)
          let name = unLocated $ _sigName fn
          return $ Precedence assoc level name
  let userPrecMap = M.fromList [(_operName p, p) | p <- userPrecs]
  traverseExprInProgram (orExpr userPrecMap) program

{-------------
 -- Utility --
 -------------}

builtinPrecedences :: [(String,Assoc,Integer)]
builtinPrecedences =
   [ ("+"           , LeftAssoc           , 70)
   , ("-"           , LeftAssoc           , 70)
   , ("*"           , LeftAssoc           , 80)
   , ("/"           , LeftAssoc           , 80)
   , ("%"           , LeftAssoc           , 80)
   , ("^"           , LeftAssoc           , 20)
   , ("&"           , LeftAssoc           , 30)
   , ("|"           , LeftAssoc           , 10)
   , ("<<"          , LeftAssoc           , 60)
   , ("<<<"         , LeftAssoc           , 60)
   , (">>"          , LeftAssoc           , 60)
   , (">>>"         , LeftAssoc           , 60)
   , ("~"           , NonAssoc            , 90)
   , ("!"           , NonAssoc            , 90)
   , ("=="          , NonAssoc            , 40)
   , ("<"           , NonAssoc            , 50)
   , ("<="          , NonAssoc            , 50)
   , (">"           , NonAssoc            , 50)
   , (">="          , NonAssoc            , 50)
   ]

precList :: [Precedence Text]
precList = [Precedence a p (pack n) | (n, a, p) <- builtinPrecedences]

precMap :: PrecMap
precMap = M.fromList [(_operName x, x) | x <- precList]

getOperPrecedence :: PrecMap -> Text -> TcM (Precedence Text)
getOperPrecedence userPrecMap name = case M.lookup name (precMap <> userPrecMap) of
  Nothing -> tcThrowErr "Operator without precedence."
  Just prec -> return prec

testExprPrecs :: PrecMap -> Located Text -> Located Text -> TcM Bool
testExprPrecs userPrecMap (Located l1 o1) (Located l2 o2) = do
  p1 <- tcSetLoc l1 $ getOperPrecedence userPrecMap o1
  p2 <- tcSetLoc l2 $ getOperPrecedence userPrecMap o2
  let b = leftAssoc p1 && prec p1 == prec p2 || prec p1 < prec p2
  when (_fixity p1 == NonAssoc && _fixity p2 == NonAssoc) $
    tcSetLoc (joinLocations l2 l1) $
      tcThrowErr $ "Operators" <+> pretty o1 <+> "and" <+> pretty o2
        <+> "are non associative and may not be used together."
  return b
  where
    prec = _precedence
    leftAssoc = (LeftAssoc ==) . _fixity

spanM :: (a -> TcM Bool) -> [a] -> TcM ([a],[a])
spanM _ [] = return ([],[])
spanM f xs@(x:xs') = do
  b <- f x
  if b
    then do
      (ys,zs) <- spanM f xs'
      return (x:ys,zs)
    else return ([],xs)

{---------------------------
 -- Expression reordering --
 ---------------------------}

type Eexp = Expr Text

orExpr :: PrecMap -> Eexp -> TcM Eexp
orExpr userPrecMap t = do
  (stack,out) <- orExpr' userPrecMap t [] []
  let output = reverse stack ++ out
  elems <- foldM buildExpr [] (reverse output)
  when (length elems > 1) $
    tcThrowErr $ "ICE: orExpr more then 1 elem for expr" <+> dumpExpr t
  return $ head elems

buildExpr :: [Eexp] -> Eexp -> TcM [Eexp]
buildExpr s (CallOper iv op _) = do
  let r:l:rest = s
  let loc = joinLocations (location l) (location r)
  let t = ExprLoc loc $ Call iv (Func op) [] [l,r]
  return $ t:rest
buildExpr s e = return (e:s)

orExpr' :: PrecMap -> Eexp -> [Eexp] -> [Eexp] -> TcM ([Eexp],[Eexp])
orExpr' userPrecMap (CallOper iv op@(Located _ occ) [a]) s o | occ == pack "-" = do
  a' <- orExpr userPrecMap a
  let e = Call iv (Func op) [] [Lit (ConstInt 0), a']
  return (s, e:o)
orExpr' userPrecMap (CallOper iv op [a]) s o = do
  a' <- orExpr userPrecMap a
  let e = Call iv (Func op) [] [a']
  return (s, e:o)
orExpr' userPrecMap (CallOper iv op [a,b]) s o = do
  (s',o') <- orExpr' userPrecMap a s o
  let
    testop callOp = case callOp of
      CallOper _ op' _ -> testExprPrecs userPrecMap op op'
      _ -> error "ICE: Parser.Precedence.orExpr': expecting call operator."
  (toOut,s'') <- spanM testop s'
  let e = CallOper iv op []
  orExpr' userPrecMap b (e:s'') (reverse toOut ++ o')
orExpr' userPrecMap (ExprLoc l (ExprLoc _ e)) s o = do -- XXX: double wrapped expr marks expr in parenthesis!
  e' <- orExpr userPrecMap e
  return (s, ExprLoc l e' : o)
orExpr' userPrecMap (ExprLoc l e) s o = do
  ~(s', e' : o') <- orExpr' userPrecMap e s o
  return (s', ExprLoc l e' : o')
orExpr' userPrecMap e s o = do
  e' <- plate (orExpr userPrecMap) e
  return (s, e':o)
