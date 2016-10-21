{-# LANGUAGE TemplateHaskell, TypeInType #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
  -- improves error messages during example

module Main where

import ReadDB
import Basics
import TH
import DB2  hiding ( Schema )

main :: IO ()
main = withSchema "classes.schema"  $ \classes_sch ->
       withSchema "students.schema" $ \students_sch ->
       $(checkSchema 'readDB ['classes_sch, 'students_sch])
