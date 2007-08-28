module Main where

import Data.IORef
import Data.Maybe
import Control.Monad
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import System.IO.Error
import System.Locale
import System.Time

import Alice.Core.Base
import Alice.Core.Verify
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Import.Reader

{- and what is the use of a book without pictures or conversation? -}

main :: IO ()
main  =
  do  hSetBuffering stdout LineBuffering
      cmdl <- readOpts
      init <- readInit $ askIS cmdl ISinit "init.opt"
      rstt <- newIORef initRS
      strt <- getClockTime

      verify rstt $ map TI $ init ++ cmdl

      fint <- getClockTime
      stat <- readIORef rstt

      let inst = rsInst stat
          cntr = rsCntr stat
          igno = cumulCI CIfail 0 cntr
          subt = cumulCI CIsubt 0 cntr
          prst = cumulCT CTpars strt cntr
          prvt = cumulCT CTprov prst cntr

      putStrLn $ "[Main] "
              ++ "sections "    ++ show (cumulCI CIsect 0 cntr)
              ++ " - goals "    ++ show (cumulCI CIgoal 0 cntr)
              ++ (if (igno == 0) then "" else
                 " - failed "   ++ show igno)
              ++ " - subgoals " ++ show (cumulCI CIprov subt cntr)
              ++ " - trivial "  ++ show subt
              ++ " - proved "   ++ show (cumulCI CIprvy 0 cntr)
      putStrLn $ "[Main] "
              ++ "parser "      ++ showTimeDiff (getTimeDiff prst strt)
              ++ " - reason "   ++ showTimeDiff (getTimeDiff fint prvt)
              ++ " - prover "   ++ showTimeDiff (getTimeDiff prvt prst)
              ++ "/" ++ showTimeDiff (maximCT CTprvy cntr)
      putStrLn $ "[Main] "
              ++ "total "       ++ showTimeDiff (getTimeDiff fint strt)

      return ()


-- Command line parsing

readOpts :: IO [Instr]
readOpts  =
  do  let rio = ReturnInOrder $ InStr ISread
      (is, _, es) <- liftM (getOpt rio options) getArgs
      unless (null es) $ die $ concatMap ("[Main] " ++) es
      if askIB is IBhelp False then helper else return is
  where
    helper  = do  putStr $ usageInfo header options
                  exitWith ExitSuccess

    header  = "Usage: alice [option|file]..."

    options =
      [ Option "h" [] (NoArg (InBin IBhelp True)) "this help",
        Option ""  ["init"] (ReqArg (InStr ISinit) "FILE")
            "init file, empty to skip (def: init.opt)",
        Option "T" [] (NoArg (InBin IBtext True))
            "translate input text and exit",
        Option "P" ["prover"] (ReqArg (InStr ISprvr) "NAME")
            "use prover NAME (def: first listed)",
        Option ""  ["provers"] (ReqArg (InStr ISprdb) "FILE")
            "import prover descriptions",
        Option "t" ["timelimit"] (ReqArg (InInt IItlim . number) "N")
            "N seconds for a prover call (def: 3)",
        Option ""  ["depthlimit"] (ReqArg (InInt IIdpth . number) "N")
            "N reasoner loops per goal (def: 7)",
        Option ""  ["checktime"] (ReqArg (InInt IIchtl . number) "N")
            "timelimit for checker's tasks (def: 1)",
        Option ""  ["checkdepth"] (ReqArg (InInt IIchdl . number) "N")
            "depthlimit for checker's tasks (def: 3)",
        Option "n" [] (NoArg (InBin IBprov False))
            "cursory mode (equivalent to --prove off)",
        Option "" ["prove"] (ReqArg (InBin IBprov . binary) "{on|off}")
            "prove goals in the text (default: on)",
        Option "" ["check"] (ReqArg (InBin IBdefn . binary) "{on|off}")
            "check symbols for definedness (def: on)",
        Option "" ["collect"] (ReqArg (InBin IBinfo . binary) "{on|off}")
            "collect \"evidence\" literals (def: on)",
        Option "" ["trim"] (ReqArg (InBin IBmotv . binary) "{on|off}")
            "maintain current thesis (def: on)",
        Option "" ["filter"] (ReqArg (InBin IBfilt . binary) "{on|off}")
            "filter prover tasks (def: on)",
        Option "" ["skipfail"] (ReqArg (InBin IBigno . binary) "{on|off}")
            "ignore failed goals (def: off)",
        Option "" ["flat"] (ReqArg (InBin IBflat . binary) "{on|off}")
            "do not read proofs (def: off)",
        Option "v" [] (NoArg (InBin IBverb True))
            "print more details (-vv, -vvv, ...)",
        Option "q" [] (NoArg (InBin IBverb False))
            "print no details",
        Option "" ["printgoal"] (ReqArg (InBin IBgoal . binary) "{on|off}")
            "print current goal (def: on)",
        Option "" ["printreason"] (ReqArg (InBin IBrlog . binary) "{on|off}")
            "print reasoner's logs (def: off)",
        Option "" ["printsection"] (ReqArg (InBin IBtran . binary) "{on|off}")
            "print sentence translations (def: off)",
        Option "" ["printcheck"] (ReqArg (InBin IBdchk . binary) "{on|off}")
            "print checker's logs (def: off)",
        Option "" ["printprover"] (ReqArg (InBin IBplog . binary) "{on|off}")
            "print prover's logs (def: off)",
        Option "" ["printunfold"] (ReqArg (InBin IBunfl . binary) "{on|off}")
            "print unfolded definitions (def: off)",
        Option "" ["printfulltask"] (ReqArg (InBin IBtask . binary) "{on|off}")
            "print full prover tasks (def: off)" ]

    binary "yes"  = True
    binary "on"   = True
    binary "no"   = False
    binary "off"  = False
    binary s      = error $ "invalid boolean argument: " ++ s

    number s  = case reads s of
      ((n,[]):_) | n >= 0 -> n
      _ -> error $ "invalid numeric argument: " ++ s

    die s = putStr s >> exitFailure

