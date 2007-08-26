module Alice.Export.DFG (dfgOut) where

import Data.List
import qualified Data.Monoid as Monoid

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Export.Base

dfgOut :: Prover -> Int -> [Context] -> Context -> String
dfgOut pr tl cn gl = (hdr . sym . axm . cnj . eop) ""
  where
    hdr = showString "begin_problem(A).list_of_descriptions.name({*EA*})."
        . showString "author({*EA*}).status(unknown).description({*EA*})."
        . eol

    sym = showString "list_of_symbols.\n" . dfgSLS (gl:cn) . eol

    axm = showString "list_of_formulae(axioms).\n" . axs . eol
    cnj = showString "list_of_formulae(conjectures).\n" . gll . eol

    eol = showString "end_of_list.\n"
    eop = showString "end_problem.\n"

    axs = foldr ((.) . dfgForm) id cn
    gll = dfgForm gl


-- Formula print

dfgForm :: Context -> ShowS
dfgForm (Context f (Block { blName = m } : _))
        = showString "formula(" . dfgTerm 0 f . showChar ','
        . showString (if null m then "_" else m) . showString ").\n"

dfgTerm :: Int -> Formula -> ShowS
dfgTerm d = dive
  where
    dive (All v f)  = showString "forall" . showParen True (binder f)
    dive (Exi v f)  = showString "exists" . showParen True (binder f)
    dive (Iff f g)  = showString "equiv" . showArgs dive [f,g]
    dive (Imp f g)  = showString "implies" . showArgs dive [f,g]
    dive (Or  f g)  = showString "or" . showArgs dive [f,g]
    dive (And f g)  = showString "and" . showArgs dive [f,g]
    dive (Ann a f)  = dive f
    dive (Not f)    = showString "not" . showArgs dive [f]
    dive Top        = showString "true"
    dive Bot        = showString "false"
    dive t| isEqu t = showString "equal" . showArgs dive (trArgs t)
          | isTrm t = showTrName t . showArgs dive (trArgs t)
          | isVar t = showTrName t
          | isInd t = showChar 'w' . shows (d - 1 - trIndx t)

    binder f  = showChar '[' . dfgTerm (succ d) (Ind 0 [])
              . showString "]," . dfgTerm (succ d) f

showTrName = showString . filter (/= ':') . trName


-- Symbol count

newtype SymSet = SS { getSS :: ([(String, Int)], [(String, Int)]) }

instance Monoid.Monoid SymSet where
  mempty  = SS ([], [])
  mappend (SS (psa, fsa)) (SS (psb, fsb))
          = SS (union psa psb, union fsa fsb)

dfgSLS :: [Context] -> ShowS
dfgSLS tsk  = sls "functions" fns . sls "predicates" pds
  where
    sls s (hd:tl) = showString s . showChar '[' . shs hd
                  . showTail shs tl . showString "].\n"
    sls _ _ = id

    shs (s, a)  = showParen True $ stn s . showChar ',' . shows a
    stn = showString . filter (/= ':')

    SS (pds, fns) = foldr fld (Monoid.mempty) tsk
    fld = Monoid.mappend . dfgSyms True . cnForm

dfgSyms :: Bool -> Formula -> SymSet
dfgSyms s (Trm t ts _)  = let h | t == "="  = Monoid.mempty
                                | s         = SS ([(t, length ts)], [])
                                | otherwise = SS ([], [(t, length ts)])
                              a = Monoid.mconcat $ map (dfgSyms False) ts
                          in  Monoid.mappend h a
dfgSyms s (Var v _)     = SS ([], [(v, 0)])
dfgSyms _ (Ind _ _)     = Monoid.mempty
dfgSyms s f             = foldF (dfgSyms s) f

