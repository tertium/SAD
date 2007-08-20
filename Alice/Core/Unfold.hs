module Alice.Core.Unfold where

import Alice.Data.Formula
import Alice.Data.Text
import Alice.Core.Local

-- Definition expansion

markup cnt    = return $ dlc ++ glb
  where
    (loc,glb) = span ((== "__") . blMark) cnt
    dlc = map (\ b -> b { blForm = mrk (blForm b) }) loc
    mrk f@(Trm _ ts _ d) = f {  trDefn = map (Ann DCN) d,
                                trArgs = map mrk ts }
    mrk v | isVar v = v
    mrk f = mapF mrk f


expand n  = roll
  where
    roll (bl:cnt) = let ecn = roll cnt ; fr = formulate bl
                    in  bl { blForm = fill ecn True fr } : ecn
    roll _        = []

    fill cnt sg f | isTrm f = reduce $ fillDLV cnt nfr
      where
        wip = (wipeDCN f {trInfo = []}) {trInfo = trInfo f}
        nbs = foldr (if sg then And else Or) wip (expU f)
        nfr = foldr (if sg then And else Imp) nbs arg
        arg = concatMap expT $ trArgs f
    fill cnt sg f = roundF fill cnt sg f

    expU (Not h)  = map Not (expU h)
    expU h  | isDCN h = [outDef h]
    expU h  = []

    expT h  | isDCN h = outDef h : expT (nullD h)
    expT h  | isTrm h = concatMap expT (trArgs h) ++
                        concatMap expU (trInfo h)
    expT h  | isVar h = concatMap expU (trInfo h)
    expT h  = foldF expT [] (++) h

    outDef (Trm _ _ _ [Ann DCN d])  = rebind undot d

    undot ('.':'.':x) = '.':x
    undot ('.':x) = 'd':show n ++ x
    undot x = error $ "undot " ++ x


isDCN (Trm _ _ _ [Ann DCN _]) = True
isDCN _ = False

wipeDCN f | isDCN f = wipeDCN (nullD f)
          | True    = mapF wipeDCN f

markDCN t = t { trDefn = map (Ann DCN) (trDefn t) }


markedF (Ann DIM _) = []
markedF (Ann DOR _) = []
markedF f | isDCN f = foldF markedF [f] (++) (nullD f)
          | isTrm f = foldF markedF []  (++) (nullD f)
          | True    = foldF markedF []  (++) f

tailleF (Ann DIM _) = 0
tailleF (Ann DOR _) = 0
tailleF f | isTrm f = foldF tailleF 1 (+) (nullD f)
          | isVar f = foldF tailleF 1 (+) f
          | True    = foldF tailleF 0 (+) f


