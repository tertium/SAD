module Alice.Export.Base (Prover(..),Format(..),readPrDB) where

import Data.Char
import Data.List

import System.Exit
import System.IO
import System.IO.Error

data Prover = Prover {  prName :: String,   prLabl :: String,
                        prPath :: String,   prArgs :: [String],
                        prFrmt :: Format,   prSucc :: [String],
                        prFail :: [String], prUnkn :: [String] }

data Format = DFG | TPTP | Otter | Moses

initPrv l = Prover l "Prover" "" [] TPTP [] [] []


-- Database reader

readPrDB :: String -> IO [Prover]
readPrDB file = do  inp <- catch (readFile file) $ \ e ->
                      die $ "read error: " ++ ioeGetErrorString e

                    let dws = dropWhile isSpace
                        cln = reverse . dws . reverse . dws
                        lns = map cln $ lines inp

                    case readPrvs 1 Nothing lns of
                      Left e  ->  die e
                      Right d ->  return d
  where
    die e = putStrLn ("[Export] " ++ file ++ ": ") >> exitFailure


readPrvs :: Int -> Maybe Prover -> [String] -> Either String [Prover]

readPrvs n mbp ([]:ls)      = readPrvs (succ n) mbp ls
readPrvs n mbp (('#':_):ls) = readPrvs (succ n) mbp ls
readPrvs n _ (l@[c]:ls)     = Left $ show n ++ ": empty value"

readPrvs n (Nothing) (('P':l):ls)
  = readPrvs (succ n) (Just $ initPrv l) ls
readPrvs n (Just pr) (('P':l):ls)
  = fmap2 (:) (validate pr) $ readPrvs (succ n) (Just $ initPrv l) ls
readPrvs n (Just pr) (('L':l):ls)
  = readPrvs (succ n) (Just pr { prLabl = l }) ls
readPrvs n (Just pr) (('Y':l):ls)
  = readPrvs (succ n) (Just pr { prSucc = l : prSucc pr }) ls
readPrvs n (Just pr) (('N':l):ls)
  = readPrvs (succ n) (Just pr { prFail = l : prFail pr }) ls
readPrvs n (Just pr) (('U':l):ls)
  = readPrvs (succ n) (Just pr { prUnkn = l : prUnkn pr }) ls
readPrvs n (Just pr) (('C':l):ls)
  = let (p:a) = if null l then ("":[]) else words l
    in  readPrvs (succ n) (Just pr { prPath = p, prArgs = a }) ls
readPrvs n (Just pr) (('F':l):ls)
  = case l of
      "dfg"   ->  readPrvs (succ n) (Just pr { prFrmt = DFG }) ls
      "tptp"  ->  readPrvs (succ n) (Just pr { prFrmt = TPTP }) ls
      "otter" ->  readPrvs (succ n) (Just pr { prFrmt = Otter }) ls
      "moses" ->  readPrvs (succ n) (Just pr { prFrmt = Moses }) ls
      _       ->  Left $ show n ++ ": unknown format: " ++ l

readPrvs n (Just pr) ((c:_):ls) = Left $ show n ++ ": invalid tag: "   ++ [c]
readPrvs n (Nothing) ((c:_):ls) = Left $ show n ++ ": misplaced tag: " ++ [c]

readPrvs n (Just pr) [] = fmap1 (:[]) $ validate pr
readPrvs n (Nothing) [] = Right []


validate :: Prover -> Either String Prover
validate (Prover { prName = n, prPath = "" })
  = Left $ " prover '" ++ n ++ "' has no command line"
validate (Prover { prName = n, prSucc = [] })
  = Left $ " prover '" ++ n ++ "' has no success responses"
validate (Prover { prName = n, prFail = [], prUnkn = [] })
  = Left $ " prover '" ++ n ++ "' has no failure responses"
validate r = Right r


-- Service stuff

fmap1 :: (a -> b) -> Either e a -> Either e b
fmap1 f (Right a) = Right (f a)
fmap1 _ (Left e)  = Left e

fmap2 :: (a -> b -> c) -> Either e a -> Either e b -> Either e c
fmap2 _ (Left e) _          = Left e
fmap2 _ _ (Left e)          = Left e
fmap2 f (Right a) (Right b) = Right (f a b)

