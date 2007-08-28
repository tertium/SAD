module Main where

import Data.IORef
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
      init <- readInit "init.opt"
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

    header  = "Usage: alice [option|file]...\n"

    options =
      [ Option "h" ["help"] (NoArg (InBin IBhelp True)) "this help",
        Option "P" ["prvr"] (ReqArg (InStr ISprvr) "NAME")
            "use prover NAME",
        Option "t" ["tlim"] (ReqArg (InInt IItlim . number . reads) "N")
            "at most N seconds for a prover call (default: 3)",
        Option "d" ["dpth"] (ReqArg (InInt IIdpth . number . reads) "N")
            "at most N reasoner iterations per goal (default: 7)",
        Option "n" ["none"] (NoArg (InBin IBprov False))
            "cursory mode",
        Option "T" ["text"] (NoArg (InBin IBtext True))
            "translate input text" ]

    number ((n,[]):_) | n >= 0 = n
    number _ = error "invalid numeric argument"

    die s = putStr s >> exitFailure

