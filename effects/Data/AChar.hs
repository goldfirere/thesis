{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, TypeInType,
             TypeFamilies, GADTs, FlexibleInstances,
             StandaloneDeriving #-}

module Data.AChar where

import Data.Singletons.TH
import qualified Prelude as P

$(singletons [d|
  data Char = CA
            | CB
            | CC
            | CD
            | CE
            | CF
            | CG
            | CH
            | CI
            | CJ
            | CK
            | CL
            | CM
            | CN
            | CO
            | CP
            | CQ
            | CR
            | CS
            | CT
            | CU
            | CV
            | CW
            | CX
            | CY
            | CZ
            | Ca
            | Cb
            | Cc
            | Cd
            | Ce
            | Cf
            | Cg
            | Ch
            | Ci
            | Cj
            | Ck
            | Cl
            | Cm
            | Cn
            | Co
            | Cp
            | Cq
            | Cr
            | Cs
            | Ct
            | Cu
            | Cv
            | Cw
            | Cx
            | Cy
            | Cz
            | C0
            | C1
            | C2
            | C3
            | C4
            | C5
            | C6
            | C7
            | C8
            | C9
            | C_
            | Cspace
            | Cnewline
            | Ccolon
            | Cperiod
            | Ccomma
            | Cbang
            | Cquestion
            | Cbracko
            | Cbrackc |])

deriving instance P.Eq Char

toChar :: Char -> P.Char
toChar CA = 'A'
toChar CB = 'B'
toChar CC = 'C'
toChar CD = 'D'
toChar CE = 'E'
toChar CF = 'F'
toChar CG = 'G'
toChar CH = 'H'
toChar CI = 'I'
toChar CJ = 'J'
toChar CK = 'K'
toChar CL = 'L'
toChar CM = 'M'
toChar CN = 'N'
toChar CO = 'O'
toChar CP = 'P'
toChar CQ = 'Q'
toChar CR = 'R'
toChar CS = 'S'
toChar CT = 'T'
toChar CU = 'U'
toChar CV = 'V'
toChar CW = 'W'
toChar CX = 'X'
toChar CY = 'Y'
toChar CZ = 'Z'
toChar Ca = 'a'
toChar Cb = 'b'
toChar Cc = 'c'
toChar Cd = 'd'
toChar Ce = 'e'
toChar Cf = 'f'
toChar Cg = 'g'
toChar Ch = 'h'
toChar Ci = 'i'
toChar Cj = 'j'
toChar Ck = 'k'
toChar Cl = 'l'
toChar Cm = 'm'
toChar Cn = 'n'
toChar Co = 'o'
toChar Cp = 'p'
toChar Cq = 'q'
toChar Cr = 'r'
toChar Cs = 's'
toChar Ct = 't'
toChar Cu = 'u'
toChar Cv = 'v'
toChar Cw = 'w'
toChar Cx = 'x'
toChar Cy = 'y'
toChar Cz = 'z'
toChar C0 = '0'
toChar C1 = '1'
toChar C2 = '2'
toChar C3 = '3'
toChar C4 = '4'
toChar C5 = '5'
toChar C6 = '6'
toChar C7 = '7'
toChar C8 = '8'
toChar C9 = '9'
toChar C_ = '_'
toChar Cspace = ' '
toChar Cnewline = '\n'
toChar Ccolon = ':'
toChar Cperiod = '.'
toChar Ccomma = ','
toChar Cbang = '!'
toChar Cquestion = '?'
toChar Cbracko = '['
toChar Cbrackc = ']'

fromChar :: P.Char -> Char
fromChar 'A' = CA
fromChar 'B' = CB
fromChar 'C' = CC
fromChar 'D' = CD
fromChar 'E' = CE
fromChar 'F' = CF
fromChar 'G' = CG
fromChar 'H' = CH
fromChar 'I' = CI
fromChar 'J' = CJ
fromChar 'K' = CK
fromChar 'L' = CL
fromChar 'M' = CM
fromChar 'N' = CN
fromChar 'O' = CO
fromChar 'P' = CP
fromChar 'Q' = CQ
fromChar 'R' = CR
fromChar 'S' = CS
fromChar 'T' = CT
fromChar 'U' = CU
fromChar 'V' = CV
fromChar 'W' = CW
fromChar 'X' = CX
fromChar 'Y' = CY
fromChar 'Z' = CZ
fromChar 'a' = Ca
fromChar 'b' = Cb
fromChar 'c' = Cc
fromChar 'd' = Cd
fromChar 'e' = Ce
fromChar 'f' = Cf
fromChar 'g' = Cg
fromChar 'h' = Ch
fromChar 'i' = Ci
fromChar 'j' = Cj
fromChar 'k' = Ck
fromChar 'l' = Cl
fromChar 'm' = Cm
fromChar 'n' = Cn
fromChar 'o' = Co
fromChar 'p' = Cp
fromChar 'q' = Cq
fromChar 'r' = Cr
fromChar 's' = Cs
fromChar 't' = Ct
fromChar 'u' = Cu
fromChar 'v' = Cv
fromChar 'w' = Cw
fromChar 'x' = Cx
fromChar 'y' = Cy
fromChar 'z' = Cz
fromChar '0' = C0
fromChar '1' = C1
fromChar '2' = C2
fromChar '3' = C3
fromChar '4' = C4
fromChar '5' = C5
fromChar '6' = C6
fromChar '7' = C7
fromChar '8' = C8
fromChar '9' = C9
fromChar '_' = C_
fromChar ' ' = Cspace
fromChar '\n' = Cnewline
fromChar ':' = Ccolon
fromChar '.' = Cperiod
fromChar ',' = Ccomma
fromChar '!' = Cbang
fromChar '?' = Cquestion
fromChar '[' = Cbracko
fromChar ']' = Cbrackc
fromChar c   = P.error ("character not supported: " P.++ [c])

type String = [Char]

fromString :: P.String -> String
fromString = P.map fromChar

toString :: String -> P.String
toString = P.map toChar

show :: P.Show a => a -> String
show = fromString P.. P.show

read :: P.Read a => String -> a
read = P.read P.. toString

instance P.Show Char where
  show x = [toChar x]
  showList xs = P.showString (toString xs)
