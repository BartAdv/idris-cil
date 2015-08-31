{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module IRTS.Cil.FFI
       ( parseAssemblyQualifiedName
       , foreignTypeToCilType
       ) where

import           Data.Maybe
import           Data.Text
import           Text.ParserCombinators.Parsec
import qualified Data.HashMap.Strict as HM

import           IRTS.Lang (FDesc(..))
import           Idris.Core.TT (Name(..))
import           Language.Cil (PrimitiveType(..))

parseAssemblyQualifiedName :: String -> Either ParseError (Bool, String, String, String)
parseAssemblyQualifiedName = parse assemblyQualifiedName "foreign name"

assemblyQualifiedName :: Parser (Bool, String, String, String)
assemblyQualifiedName = do
  maybeInstance <- optionMaybe (string "instance")
  spaces
  asm <- assemblyName
  typeName <- anyChar `manyTill` string "::" <?> "type name"
  methodName <- many1 anyChar <?> "method name"
  return (isJust maybeInstance, asm, typeName, methodName)

assemblyName :: Parser String
assemblyName = do
  char '['
  asm <- many (noneOf "]") <?> "assembly name"
  char ']'
  return asm

foreignTypeToCilType :: FDesc -> PrimitiveType
foreignTypeToCilType (FApp (UN (unpack -> "CIL_RawT")) [FApp (UN (unpack -> "CILTyRef")) [FStr assembly, FStr typeName], _, _]) =
  ReferenceType assembly typeName
foreignTypeToCilType (FApp (UN (unpack -> "CIL_IntT")) _) = Int32
--foreignTypeToCilType (FApp t _) = foreignType t
foreignTypeToCilType (FCon t)   = foreignType t
foreignTypeToCilType (FIO t)    = foreignTypeToCilType t
foreignTypeToCilType d          = error $ "Unsupported foreign descriptor: " ++ show d

foreignType :: Name -> PrimitiveType
foreignType (UN typeName) =
  fromMaybe
    (error $ "Unsupported foreign type: " ++ unpack typeName)
    (HM.lookup typeName foreignTypes)

foreignTypes :: HM.HashMap Text PrimitiveType
foreignTypes = HM.fromList [("CIL_IntT", Int32)
                           ,("CIL_Str", String)
                           ,("CIL_Ptr", Object)
                           ,("CIL_Bool", Bool)
                           ,("CIL_Unit", Void)
                           ]
