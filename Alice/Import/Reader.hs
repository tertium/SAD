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
import Alice.Parser.Trans

-- Init file parsing

readInit :: String -> IO [Instr]
readInit file =
  do  input <- catch (readFile file) (const $ return "")
      let tkn = tokenize input
          inp = initPS { psRest = tkn, psFile = file, psLang = "Init" }
          (res,err) = runLPM instf inp
          [(is, _)] = res
      when (null res) $ dieLn $ strerr err
      return is

instf :: LPM [Instr]
instf = skipSpace (return ()) >> after (optEx [] $ chnopEx instr) readEOI


-- Reader loop

readText :: String -> IO [Text]
readText file = reader [] [(initPS, initFS)] [TI $ InStr ISread file]

reader :: [String] -> [(PState, FState)] -> [Text] -> IO [Text]

reader fs ss@((ps, st):_) [TI (InStr ISread file)] | file `elem` fs =
  do  putStrLn $ "[Main] " ++ file ++ " already read, skipping"
      reader fs ((initPS { psOffs = psOffs ps }, st):ss) []

reader fs ss@((ps, st):_) [TI (InStr ISread file)] =
  do  input <- catch
        (if null file then hGetContents stdin else readFile file)
          $ \ e -> dieLn $ "[Main] " ++ file ++ ": read error: "
                                        ++ ioeGetErrorString e
      let sst = st { tvr_expr = [] }
          tkn = tokenize input
          sps = initPS { psRest = tkn, psFile = file, psOffs = psOffs ps }
          (res, err) = runLPM (runStateT text sst) sps
          [((ntx, nst), nps)] = res
      when (null res) $ dieLn $ strerr err
      reader (file:fs) ((nps, nst):ss) ntx

reader fs ss (t:ts) = liftM (t:) $ reader fs ss ts

reader fs ((sps, sst):(ps,st):ss) [] =
  do  let fi = psFile sps
          fn = if null fi then "stdin" else fi
      putStrLn $ '[' : psLang sps ++ "] "
          ++ fn ++ ": parsing successful"
      let rps = ps { psOffs = psOffs sps }
          rst = sst { tvr_expr = tvr_expr st }
          (res, err) = runLPM (runStateT text rst) rps
          [((ntx, nst), nps)] = res
      when (null res) $ dieLn $ strerr err
      reader fs ((nps, nst):ss) ntx

reader _ [_] [] = return []


-- Universal parser

text :: FTL [Text]
text  = do  p <- liftM parser $ askPS psLang
            narrow $ (skipSpace $ return ()) >> p
  where
    parser "ForTheL"  = forthel
    parser "FOL"      = lift fol
    parser "TPTP"     = lift tptp
    parser _          = lang "ForTheL" forthel
                    -/- lang "FOL"  (lift fol)
                    -/- lang "TPTP" (lift tptp)

    lang l p = updatePS (\ ps -> ps { psLang = l }) >> p


-- Service stuff

die s   = putStr   s >> exitFailure
dieLn s = putStrLn s >> exitFailure

