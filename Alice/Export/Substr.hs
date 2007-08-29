{-
 -  Export/Substr.hs -- state machine for substring search
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

module Alice.Export.Substr where

data SM a b = SMC a [SM a b] | SMF b deriving Show

strSM :: [a] -> b -> [SM a b]
strSM as b  = foldr (\ a m -> [SMC a m]) [SMF b] as

addSM :: (Eq a, Ord a) => [SM a b] -> [SM a b] -> [SM a b]
addSM m@(c@(SMC a p):r) n@(d@(SMC b q):s)
  | a == b  = SMC a (addSM p q) : addSM r s
  | a <  b  = c : addSM r n
  | True    = d : addSM m s
addSM m@(SMF _ : _) _ = m
addSM _ m@(SMF _ : _) = m
addSM m []  = m
addSM _  m  = m

tieSM :: (Eq a, Ord a) => [SM a b] -> [SM a b]
tieSM m = res
  where
    res = map tie m
    tie (SMC a n) = SMC a $ addSM (map tie n) res
    tie x = x

stpSM :: (Eq a, Ord a) => [SM a b] -> [a] -> Maybe b
stpSM m as  = stp m as
  where
    stp (SMC c p : m) ss@(a:as) | c == a  = stp p as
                                | c < a   = stp m ss
    stp (SMF e : _) _ = Just e
    stp _ (_:as)      = stp m as
    stp _ _           = Nothing

{-
main  = do  ars <- getArgs
            let sms = map (\ s -> strSM s s) ars
                fsm = tieSM $ foldr addSM [] sms
            inp <- hGetContents stdin
            putStrLn $ show $ stpSM fsm inp
-}
