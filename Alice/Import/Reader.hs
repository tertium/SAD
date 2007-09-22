{-
 -  Import/Reader.hs -- main text reading functions
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

module Alice.Import.Reader (readInit,readText) where

import Control.Monad
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
readInit file =
  do  input <- catch (readFile file) (const $ return "")
      let tkn = tokenize input ; ips = initPS ()
          inp = ips { psRest = tkn, psFile = file, psLang = "Init" }
          (res,err) = runLPM instf inp ; [(is, _)] = res
      when (null res) $ dieLn $ strerr err
      return is

instf :: LPM a [Instr]
instf = skipSpace (return ()) >> after (optEx [] $ chnopEx instr) readEOI


-- Reader loop

readText :: String -> IO [Text]
readText file = reader [] [initPS initFS] [TI $ InStr ISread file]

reader :: [String] -> [PState FState] -> [Text] -> IO [Text]

reader fs ss@(ps:_) [TI (InStr ISread file)] | file `elem` fs =
  do  putStrLn $ "[Main] " ++ file ++ " already read, skipping"
      let nps = (initPS (psProp ps)) { psOffs = psOffs ps }
      reader fs (nps:ss) []

reader fs ss@(ps:_) [TI (InStr ISread file)] =
  do  input <- catch
        (if null file then hGetContents stdin else readFile file)
          $ \ e -> dieLn $ "[Main] " ++ file ++ ": read error: "
                                        ++ ioeGetErrorString e
      let tkn = tokenize input
          ips = initPS $ (psProp ps) { tvr_expr = [] }
          sps = ips { psRest = tkn, psFile = file, psOffs = psOffs ps }
          (res, err) = runLPM text sps ; [(ntx, nps)] = res
      when (null res) $ dieLn $ strerr err
      reader (file:fs) (nps:ss) ntx

reader fs ss (t:ts) = liftM (t:) $ reader fs ss ts

reader fs (sps:ps:ss) [] =
  do  let fi = psFile sps ; la = psLang sps
          fn = if null fi then "stdin" else fi
      unless (null la) $ putStrLn $ '[' : la ++ "] "
                     ++ fn ++ ": parsing successful"
      let rps = ps { psOffs = psOffs sps, psProp = rst }
          rst = (psProp sps) { tvr_expr = tvr_expr (psProp ps) }
          (res, err) = runLPM text rps ; [(ntx, nps)] = res
      when (null res) $ dieLn $ strerr err
      reader fs (nps:ss) ntx

reader _ [_] [] = return []


-- Universal parser

text :: FTL [Text]
text  = do  p <- liftM parser $ askPS psLang
            narrow $ (skipSpace $ return ()) >> p
  where
    parser "ForTheL"  = forthel
    parser "FOL"      = fol
    parser "TPTP"     = tptp
    parser _          = lang "ForTheL" forthel
                    -/- lang "FOL"  fol
                    -/- lang "TPTP" tptp

    lang l p = updatePS (\ ps -> ps { psLang = l }) >> p


-- Service stuff

die s   = putStr   s >> exitFailure
dieLn s = putStrLn s >> exitFailure

