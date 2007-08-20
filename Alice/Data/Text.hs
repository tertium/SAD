module Alice.Data.Text where

import Data.List

import Alice.Data.Formula
import Alice.Data.Instr


data Text = TB Block | TI Instr | TD Idrop

blocks :: [Text] -> [Block]
blocks (TB bl : tx) = bl : blocks tx
blocks (_ : tx)     = blocks tx
blocks _            = []


data Block  = Block { blForm :: Formula,  blBody :: [Text],
                      blSign :: Bool,     blDecl :: [String],
                      blName :: String,   blLink :: [String],
                      blLang :: String,   blFile :: String,
                      blLine :: Int,      blText :: String }

noForm :: Block -> Bool
noForm  = isHole . blForm

noBody :: Block -> Bool
noBody  = null . blBody

formulate :: Block -> Formula
formulate bl  | noForm bl = compose $ blocks $ blBody bl
              | otherwise = blForm bl

compose :: [Block] -> Formula
compose (bl : bs) | blSign bl = foldr zExi (bool $ And fbl fbs) dvs
                  | otherwise = foldr zAll (bool $ Imp fbl fbs) dvs
  where
    fbl = formulate bl
    fbs = compose bs
    dvs = blDecl bl
compose _ = Top


-- Show instances

instance Show Text where
  showsPrec p (TB bl) = showsPrec p bl
  showsPrec p (TI is) = showsPrec p is . showChar '\n'
  showsPrec p (TD id) = showsPrec p id . showChar '\n'

instance Show Block where
  showsPrec p bl  = showForm p bl . prf . sbody . suf
    where
      sbody = foldl (.) id $ map (showsPrec $ succ p) $ blBody bl
      prf = if nem then id else showIndent p . showString "proof.\n"
      suf = if nem then id else showIndent p . showString "qed.\n"
      nem = noForm bl || noBody bl

showForm p bl = showIndent p . sform (noForm bl) (blSign bl) . dt
  where
      sform True  True  = showString $ "conjecture" ++ mr
      sform True  False = showString $ "hypothesis" ++ mr
      sform False False = showString "assume " . shows fr
      sform False True  = shows fr

      mr = if null nm then "" else (' ':nm)
      fr = blForm bl ; nm = blName bl
      dt = showString ".\n"

showIndent :: Int -> ShowS
showIndent n  = showString $ replicate (n * 2) ' '

