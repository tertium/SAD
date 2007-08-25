module Alice.Data.Text where

import Data.List

import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Kit

data Text = TB Block | TI Instr | TD Idrop

data Block  = Block { blForm :: Formula,  blBody :: [Text],
                      blSign :: Bool,     blDecl :: [String],
                      blName :: String,   blLink :: [String],
                      blLang :: String,   blFile :: String,
                      blLine :: Int,      blText :: String }

data Context  = Context { cnForm :: Formula, cnBran :: [Block] }


-- Block utilities

noForm :: Block -> Bool
noForm  = isHole . blForm

noBody :: Block -> Bool
noBody  = null . blBody


-- Composition

formulate :: Block -> Formula
formulate bl  | noForm bl = compose $ blBody bl
              | otherwise = blForm bl

compose :: [Text] -> Formula
compose = foldr comp Top
  where
    comp (TB bl@(Block{ blDecl = dvs, blSign = True  })) fb
            = foldr zExi (bool $ And (formulate bl) fb) dvs
    comp (TB bl@(Block{ blDecl = dvs, blSign = False })) fb
            = foldr zAll (bool $ Imp (formulate bl) fb) dvs
    comp _ fb = fb


-- Context utilities

cnHead  = head . cnBran
cnTail  = tail . cnBran
cnTopL  = null . cnTail
cnLowL  = not  . cnTopL

cnSign  = blSign . cnHead
cnDecl  = blDecl . cnHead
cnName  = blName . cnHead
cnLink  = blLink . cnHead

setForm :: Context -> Formula -> Context
setForm cx fr = cx { cnForm = fr }

cnRaise :: [Context] -> Context -> [Formula] -> [Context]
cnRaise cnt cx fs = foldr ((:) . setForm cx) cnt fs


-- Show instances

instance Show Text where
  showsPrec p (TB bl) = showsPrec p bl
  showsPrec p (TI is) = showsPrec p is . showChar '\n'
  showsPrec p (TD id) = showsPrec p id . showChar '\n'

instance Show Block where
  showsPrec p bl  | noBody bl = showForm p bl
                  | noForm bl = showForm p bl . sbody
                  | otherwise = showForm p bl
                              . showIndent p . showString "proof.\n"
                              . sbody
                              . showIndent p . showString "qed.\n"
    where
      sbody = foldr ((.) . showsPrec (succ p)) id $ blBody bl

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

