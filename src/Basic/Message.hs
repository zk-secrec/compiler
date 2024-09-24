{-# LANGUAGE FlexibleInstances #-}
{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Basic.Message (
  Message,
  Messages,
  MessageLevel(..),
  getMsgLevel,
  getMsgLocs,
  getMsgText,
  warnMsg,
  errMsg,
  debugMsg,
  fatalMsg,
  isErrMsg,
  hasErrMsg,
  getSortedMsgs,
  prettyMessage,
) where

import Control.Exception
import Data.List (sortOn)

import Basic.Location
import Support.Bag
import Support.Pretty

data Message = Message {
    _msgLevel :: MessageLevel,
    _msgText  :: Doc (),
    _msgLocs  :: [Location]
  }

data MessageLevel
  = MsgWarning
  | MsgError
  | MsgFatal
  | MsgDebug

type Messages = Bag Message

instance Show Messages where
  
  show msgs
    = render . vcat . fmap prettyMessage . toListBag $ msgs

instance Exception Messages where

-- TODO: There are better ways to do colors with prettyprinter library!
instance Pretty MessageLevel where
  pretty MsgWarning = pretty "\x1b[33m[WARN]\x1b[0m"
  pretty MsgError   = pretty "\x1b[31m[ERROR]\x1b[0m"
  pretty MsgFatal   = pretty "\x1b[1;31m[FATAL]\x1b[0m"
  pretty MsgDebug   = pretty "[DEBUG]"

prettyMessage :: Message -> Doc ()
prettyMessage (Message level doc locs) = case locs of
  []    -> pretty level <+> doc
  [loc] -> pretty level <+> pretty loc <> colon $$ nest 2 doc
  _     -> pretty level <> line <> nest 2 (doc $$ vcat (map pretty locs))

mkMsg :: MessageLevel -> Doc () -> [Location] -> Message
mkMsg = Message

warnMsg :: Doc () -> [Location] -> Message
warnMsg = mkMsg MsgWarning

errMsg :: Doc () -> [Location] -> Message
errMsg = mkMsg MsgError

fatalMsg :: Doc () -> [Location] -> Message
fatalMsg = mkMsg MsgFatal

debugMsg :: Doc () -> [Location] -> Message
debugMsg = mkMsg MsgDebug

getMsgLevel :: Message -> MessageLevel
getMsgLevel = _msgLevel

getMsgLocs :: Message -> [Location]
getMsgLocs = _msgLocs

getMsgText :: Message -> Doc ()
getMsgText = _msgText

isErrMsg :: Message -> Bool
isErrMsg msg = case getMsgLevel msg of
  MsgError -> True
  MsgFatal -> True
  _        -> False

hasErrMsg :: Messages -> Bool
hasErrMsg = anyBag isErrMsg

getSortedMsgs :: Messages -> [Message]
getSortedMsgs = sortOn _msgLocs . toListBag
