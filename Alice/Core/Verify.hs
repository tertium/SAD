{-
 -  Core/Verify.hs -- main verification loop
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

module Alice.Core.Verify (verify) where

import Control.Monad
import Data.Maybe

import Alice.Core.Base
import Alice.Core.Check
import Alice.Core.Reason
import Alice.Core.Thesis
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text

-- Main verification loop

verify file rst bs =
  do  let text = TI (InStr ISfile file) : bs
          fnam = if null file then "stdin" else file
      putStrLn $ "[Reason] " ++ fnam ++ ": verification started"

      res <- runRM (vLoop False (Context Bot []) [] [] text) rst

      let out = if isJust res then " successful" else " failed"
      putStrLn $ "[Reason] " ++ fnam ++ ": verification" ++ out
      return res

vLoop :: Bool -> Context -> [Block] -> [Context] -> [Text] -> RM [Text]
vLoop mot ths brn cnt (TB bl@(Block fr pr sg dv _ _ la _ _ _) : bs) =
  do  incRSCI CIsect ; tfn <- askRSIS ISfile "" ; whenIB IBPsct False $
        putStrRM $ '[' : la ++ "] " ++ blLabl tfn bl ++ showForm 0 bl ""

      let nbr = bl : brn; cbl = Context fr nbr

      nfr <- if noForm bl then return fr
                          else fillDef ths cnt cbl

      flt <- askRSIB IBflat False
      let sth = Context (foldr mbExi nfr dv) nbr
          bsg = null brn || blSign (head brn)
          smt = bsg && sg && not (noForm bl)
          spr = if flt then [] else pr

      npr <- if smt then splitTh smt sth nbr cnt spr
                    else splitTh smt ths nbr cnt pr

      mtv <- askRSIB IBthes True
      let nbl = bl { blForm = deICH nfr, blBody = npr }
          nct = Context (formulate nbl) nbr : cnt
          (nmt, nth) = if mtv then thesis nct ths
                              else (sg, ths)

      nbs <- splitTh (mot && nmt) nth brn nct bs

      let fth = Imp (compose $ TB nbl : nbs) (cnForm ths)
      splitTh (mot && not nmt) (setForm ths fth) brn cnt []

      return $ TB nbl : nbs

vLoop True ths _ cnt [] = whenIB IBprov True prove >> return []
  where
    prove = do  let rl = rlog bl $ "goal: " ++ tx
                    bl = cnHead ths ; tx = blText bl
                incRSCI CIgoal ; whenIB IBPgls True rl
                reason cnt ths <>
                  (guardIB IBskip False >> incRSCI CIfail)

vLoop mot ths brn cnt (TI ins : bs) =
      procTI mot ths brn cnt ins >> vLoop mot ths brn cnt bs

vLoop mot ths brn cnt (TD ind : bs) =
      procTD mot ths brn cnt ind >> vLoop mot ths brn cnt bs

vLoop _ _ _ _ _ = return []


splitTh mot ths brn cnt bs = dive id cnt $ cnForm ths
  where
    dive c cn (Imp (Tag DIH f) g)  | closed f
                                   = fine (setForm ths f : cn) (c g)
    dive c cn (Imp (Tag DCH f) g)  | closed f
                                   = fine (setForm ths f : cn) (c g)
    dive c cn (Imp f g)            = dive (c . Imp f) cn g
    dive c cn (All v f)            = dive (c . All v) cn f
    dive _ _ _                     = vLoop mot ths brn cnt bs

    fine nct f  = let nth = thesis nct $ setForm ths f
                  in  splitTh mot (snd nth) brn nct bs

deICH = dive id
  where
    dive c (Imp (Tag DIH _) f)  = c f
    dive c (Imp (Tag DCH f) _)  = c $ Not f
    dive c (Imp f g)            = dive (c . Imp f) g
    dive c (All v f)            = dive (c . All v) f
    dive c f                    = c f


-- Instruction handling

procTI mot ths _ cnt = proc
  where
    proc (InCom ICPths)
      = do  let smt = if mot then "(mot): " else "(nmt): "
            rlog0 $ "current thesis " ++ smt ++ show (cnForm ths)

    proc (InCom ICPcnt)
      = do  let tlb = filter cnTopL cnt
                tlf = map (lichten 0 . cnForm) tlb
                srl = filter (not . isTop) tlf
            rlog0 $ "current simple rules:"
            mapM_ printRM srl

    proc (InCom _)  = rlog0 $ "unsupported instruction"

    proc (InBin IBverb False)
      = do  addRSIn $ InBin IBPgls False
            addRSIn $ InBin IBPrsn False
            addRSIn $ InBin IBPsct False
            addRSIn $ InBin IBPchk False
            addRSIn $ InBin IBPprv False
            addRSIn $ InBin IBPunf False
            addRSIn $ InBin IBPtsk False

    proc (InBin IBverb True)
      = do (guardNotIB IBPgls True  >> addRSIn (InBin IBPgls True))
        <> (guardNotIB IBPrsn False >> addRSIn (InBin IBPrsn True))
        <> (guardNotIB IBPsct False >> addRSIn (InBin IBPsct True))
        <> (guardNotIB IBPchk False >> addRSIn (InBin IBPchk True))
        <> (guardNotIB IBPprv False >> addRSIn (InBin IBPprv True))
        <> (guardNotIB IBPunf False >> addRSIn (InBin IBPunf True))
        <> (guardNotIB IBPtsk False >> addRSIn (InBin IBPtsk True))
        <> return ()

    proc i  = addRSIn i

procTD _ _ _ _ = proc
  where
    proc i  = drpRSIn i

