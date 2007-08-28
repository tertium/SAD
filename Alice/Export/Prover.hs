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

export :: [Prover] -> [Instr] -> [Context] -> Context -> IO Bool
export prs ins cnt gl =
  do  when (null prs) $ die "no provers"

      let prn = askIS ins ISprvr $ prName $ head prs
          prr = filter ((==) prn . prName) prs

      when (null prr) $ die $ "no prover: " ++ prn

      let prv@(Prover _ lbl pth ags fmt yes nos uns) = head prr
          tlm = askII ins IItlim 3; agl = map (setTlim tlm) ags
          run = runInteractiveProcess pth agl Nothing Nothing

      rpr@(wh,rh,eh,ph) <- catch run
          $ \ e -> die $ "run error: " ++ ioeGetErrorString e

      let dmp = case fmt of
                  DFG   -> dfgOut   ; TPTP  -> tptpOut
                  Otter -> otterOut ; Moses -> mosesOut
          tsk = dmp prv tlm cnt gl

      when (askIB ins IBdump False) $ putStrLn tsk
      hPutStrLn wh tsk ; hClose wh

      ofl <- hGetContents rh ; efl <- hGetContents eh
      let lns = filter (not . null) $ lines $ ofl ++ efl
          out = map (("[" ++ lbl ++ "] ") ++) lns

      when (null lns) $ die "empty response"
      when (askIB ins IBplog False) $ mapM_ putStrLn out

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

