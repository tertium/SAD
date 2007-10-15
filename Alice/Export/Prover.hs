{-
 -  Export/Prover.hs -- run external prover
 -  Copyright (c) 2001,2004,2007   Andrei Paskevich <atertium@gmail.com>
 -
 -  This file is part of SAD/Alice - a mathematical text verifier.
 -
 -  SAD/Alice is free software; you can redistribute it and/or modify
 -  it under the terms of the GNU General Public License as published by
 -  the Free Software Foundation; either version 3 of the License, or
 -  (at your option) any later version.
 -
 -  SAD/Alice is distributed in the hope that it will be useful,
 -  but WITHOUT ANY WARRANTY; without even the implied warranty of
 -  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -  GNU General Public License for more details.
 -
 -  You should have received a copy of the GNU General Public License
 -  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 -}

module Alice.Export.Prover where

import Control.Monad
import Data.List
import System.Exit
import System.IO
import System.IO.Error
import System.Process
import System.Time

import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Base
import Alice.Export.DFG
import Alice.Export.TPTP
import Alice.Export.Otter
import Alice.Export.Moses

-- Prover interface

export :: [Prover] -> [Instr] -> [Context] -> Context -> IO (IO Bool)
export prs ins cnt gl =
  do  when (null prs) $ die "no provers"

      let prn = askIS ISprvr (prName $ head prs) ins
          prr = filter ((==) prn . prName) prs

      when (null prr) $ die $ "no prover: " ++ prn

      let prv@(Prover _ lbl pth ags fmt yes nos uns) = head prr
          tlm = askII IItlim 3 ins; agl = map (setTlim tlm) ags
          run = runInteractiveProcess pth agl Nothing Nothing

      let dmp = case fmt of
                  DFG   -> dfgOut   ; TPTP  -> tptpOut
                  Otter -> otterOut ; Moses -> mosesOut
          tsk = dmp prv tlm cnt gl

      when (askIB IBPdmp False ins) $ putStrLn tsk

      seq (length tsk) $ return $
        do  rpr@(wh,rh,eh,ph) <- catch run
                $ \ e -> die $ "run error: " ++ ioeGetErrorString e

            hPutStrLn wh tsk ; hClose wh

            ofl <- hGetContents rh ; efl <- hGetContents eh
            let lns = filter (not . null) $ lines $ ofl ++ efl
                out = map (("[" ++ lbl ++ "] ") ++) lns

            when (length lns == 0) $ die "empty response"
            when (askIB IBPprv False ins) $ mapM_ putStrLn out

            let pos = any (\ l -> any (`isPrefixOf` l) yes) lns
                neg = any (\ l -> any (`isPrefixOf` l) nos) lns
                unk = any (\ l -> any (`isPrefixOf` l) uns) lns

            unless (pos || neg || unk) $ die "bad response"

            hClose eh ; waitForProcess ph

            return pos
  where
    setTlim tl ('%':'d':rs) = show tl ++ rs
    setTlim tl (s:rs)       = s : setTlim tl rs
    setTlim _ _             = []

    die s = putStrLn ("[Export] " ++ s) >> exitFailure

