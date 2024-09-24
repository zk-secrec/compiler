{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Support.Pretty
  (Pretty(..), Doc,
   (<>), (<+>), ($$),
   parens, comma, colon,
   parensIf, punctuate, nest, emptyDoc,
   sep, cat, hcat, vcat, hsep,
   sep', cat', hcat', vcat', hsep',
   indent, hang, line, group,
   render, renderStrictText, renderLazyText,
   doubleQuotes, brackets, space, underscore
  )
where

import Data.Foldable
import Prelude hiding (foldr)
import Prettyprinter
import Prettyprinter.Render.String
import Prettyprinter.Render.Text
import qualified Data.Text as ST
import qualified Data.Text.Lazy as LT

parensIf :: Bool -> Doc a -> Doc a
parensIf True = parens
parensIf False = id

doubleQuotes :: Doc a -> Doc a
doubleQuotes d = pretty '"' <> d <> pretty '"'

underscore :: Doc a
underscore = pretty "_"

render :: Doc a -> String
render = renderString . layoutPretty defaultLayoutOptions

renderStrictText :: Doc a -> ST.Text
renderStrictText = renderStrict . layoutPretty defaultLayoutOptions

renderLazyText :: Doc a -> LT.Text
renderLazyText = renderLazy . layoutPretty defaultLayoutOptions

{-------------------------------------------------
 -- Generic versions of the functions on lists  --
 -------------------------------------------------}

infixl 5 $$
($$) :: Doc a -> Doc a -> Doc a
d $$ d' = vsep [d, d']

sep' :: Foldable t => t (Doc a) -> Doc a
sep' = sep . toList

cat' :: Foldable t => t (Doc a) -> Doc a
cat' = cat . toList

hcat' :: Foldable t => t (Doc a) -> Doc a
hcat' = foldr (<>) emptyDoc

vcat' :: Foldable t => t (Doc a) -> Doc a
vcat' = foldr ($$) emptyDoc

hsep' :: Foldable t => t (Doc a) -> Doc a
hsep' = foldr (<+>) emptyDoc
