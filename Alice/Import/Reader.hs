{-
 -  Import/Reader.hs -- main text reading functions
 -  Copyright (c) 2001-2008  Andrei Paskevich <atertium@gmail.com>
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

module Alice.Import.Reader (readInit,readText) where

import Data.List
import Control.Monad
import Control.Exception
import System.IO
import System.IO.Error
import System.Exit

import Alice.Data.Text
import Alice.Data.Instr
import Alice.ForTheL.Base
import Alice.ForTheL.Text
import Alice.Import.FOL
import Alice.Import.TPTP
import Alice.Parser.Base
import Alice.Parser.Prim
import Alice.Parser.Instr
import Alice.Parser.Token

-- Init file parsing

readInit :: String -> IO [Instr]

readInit ""   = return []

readInit file =
  do  input <- catch (readFile file) $ quit file . ioeGetErrorString
      let tkn = tokenize input ; ips = initPS ()
          inp = ips { psRest = tkn, psFile = file, psLang = "Init" }
      liftM fst $ fireLPM instf inp

instf :: LPM a [Instr]
instf = skipSpace (return ()) >> after (optEx [] $ chnopEx instr) readEOI


-- Reader loop

readText :: String -> [Text] -> IO [Text]
readText lb = reader lb [] [initPS initFS]

reader :: String -> [String] -> [PState FState] -> [Text] -> IO [Text]

reader _ _ _ [TI (InStr ISread file)] | isInfixOf ".." file =
      quit file "contains \"..\", not allowed"

reader lb fs ss [TI (InStr ISread file)] =
      reader lb fs ss [TI $ InStr ISfile $ lb ++ '/' : file]

reader lb fs (ps:ss) [TI (InStr ISfile file)] | file `elem` fs =
  do  warn file "already read, skipping"
      (ntx, nps) <- fireLPM text ps
      reader lb fs (nps:ss) ntx

reader lb fs (ps:ss) [TI (InStr ISfile file)] =
  do  let gfl = if null file  then hGetContents stdin
                              else readFile file
      input <- catch gfl $ quit file . ioeGetErrorString
      let tkn = tokenize input
          ips = initPS $ (psProp ps) { tvr_expr = [] }
          sps = ips { psRest = tkn, psFile = file, psOffs = psOffs ps }
      (ntx, nps) <- fireLPM text sps
      reader lb (file:fs) (nps:ps:ss) ntx

reader lb fs ss (t:ts) = liftM (t:) $ reader lb fs ss ts

reader lb fs (sps:ps:ss) [] =
  do  info (psLang sps) (psFile sps) "parsing successful"
      let rps = ps { psOffs = psOffs sps, psProp = rst }
          rst = (psProp sps) { tvr_expr = tvr_expr (psProp ps) }
      (ntx, nps) <- fireLPM text rps
      reader lb fs (nps:ss) ntx

reader _ _ [_] [] = return []


-- Universal parser

text :: FTL [Text]
text  = skipSpace (return ()) >> askPS psLang >>= parser
  where
    parser "ForTheL"  = forthel
    parser "FOL"      = fol
    parser "TPTP"     = tptp
    parser _          = (lang "ForTheL" >> forthel)
                    -/- (lang "FOL" >> fol)
                    -/- (lang "TPTP" >> tptp)

    lang l = updatePS $ \ ps -> ps { psLang = l }


-- LPM launcher

fireLPM :: Show b => LPM a b -> PState a -> IO (PRes a b)
fireLPM p ps  = case runLPM (narrow p) ps of
                  Left e  ->  putStrLn e >> exitFailure
                  Right p ->  return p


-- Service stuff

info :: String -> String -> String -> IO ()
info la fn st = let fi = if null fn then "stdin" else fn
                in  putStrLn $ '[' : la ++ "] " ++ fi ++ ": " ++ st

warn :: String -> String -> IO ()
warn fn st = info "Main" fn st

quit :: String -> String -> IO a
quit fn st = warn fn st >> exitFailure

