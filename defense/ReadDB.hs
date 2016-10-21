{-# LANGUAGE TypeApplications, TypeInType, RankNTypes, ScopedTypeVariables,
             FlexibleContexts, TemplateHaskell, ConstraintKinds, GADTs #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
  -- inference is the whole point!

module ReadDB where

import Prelude hiding ( last )
import DB2 hiding ( Schema )

type NameSchema = [ Col "first" String, Col "last" String ]

printName :: Row NameSchema -> IO ()
printName (first ::> last ::> _) = putStrLn (first ++ " " ++ last)

readDB classes_sch students_sch = do
  classes_tab  <- loadTable "classes.table" classes_sch
  students_tab <- loadTable "students.table" students_sch

  putStr "Whose students do you want to see? "
  prof <- getLine

  let joined = Project $
               Select (field @"id" @Int `ElementOf` field @"students") $
               Product (Select (field @"prof" :== Literal prof) (Read classes_tab))
                       (Read students_tab)
  rows <- query joined
  mapM_ printName rows
