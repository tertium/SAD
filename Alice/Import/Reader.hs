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

import Data.List
import Control.Monad
import System.IO
import System.IO.Error
import System.Environment
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
      liftM fst $ fireLPM instf inp

instf :: LPM a [Instr]
instf = skipSpace (return ()) >> after (optEx [] $ chnopEx instr) readEOI


-- Reader loop

readText :: String -> IO [Text]
readText file = reader [] [initPS initFS] [TI $ InStr ISread file]

reader :: [String] -> [PState FState] -> [Text] -> IO [Text]

reader fs (ps:ss) [TI (InStr ISread file)] | file `elem` fs =
  do  putStrLn $ "[Main] " ++ file ++ " already read, skipping"
      (ntx, nps) <- fireLPM text ps
      reader fs (nps:ss) ntx

reader fs (ps:ss) [TI (InStr ISread file)] =
  do  input <- takeFile file
      let tkn = tokenize input
          ips = initPS $ (psProp ps) { tvr_expr = [] }
          sps = ips { psRest = tkn, psFile = file, psOffs = psOffs ps }
      (ntx, nps) <- fireLPM text sps
      reader (file:fs) (nps:ps:ss) ntx

reader fs ss (t:ts) = liftM (t:) $ reader fs ss ts

reader fs (sps:ps:ss) [] =
  do  let fi = psFile sps ; la = psLang sps
          fn = if null fi then "stdin" else fi
      putStrLn $ '[' : la ++ "] " ++ fn ++ ": parsing successful"
      let rps = ps { psOffs = psOffs sps, psProp = rst }
          rst = (psProp sps) { tvr_expr = tvr_expr (psProp ps) }
      (ntx, nps) <- fireLPM text rps
      reader fs (nps:ss) ntx

reader _ [_] [] = return []

takeFile file = catch (if null file then hGetContents stdin else
                jail >> readFile file) $ die . ioeGetErrorString
  where
    die e = putStrLn ("[Main] " ++ file ++ ": " ++ e) >> exitFailure

    tst j = null j || (isPrefixOf j file && not (isInfixOf ".." file))

    jail  = do  j <- catch (getEnv "ALICE_TEXT_DIR") $ const $ return ""
                if tst j then return () else die $ "must be under " ++ j


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
fireLPM p ps  = let (res, err) = runLPM (narrow p) ps
                    die s = putStrLn s >> exitFailure
                in  if null res then  die $ strerr err
                                else  return $ head res

