{-
42
r
Void VoidFunction()
System.String exportedBoolToString(Boolean)
-}
module Main

data CILTy = CILTyRef String String -- a foreign reference type
           | CILTyVal String String -- a foreign value type

class ToCIL t where
  toCIL : CILTy

mutual
  data CIL_RawTypes : CILTy -> Type -> Type where
       CIL_RawType  : ToCIL r => (x : r) -> CIL_RawTypes (toCIL {t=r}) r

  data CIL_IntTypes  : Type -> Type where
       CIL_IntChar   : CIL_IntTypes Char
       CIL_IntNative : CIL_IntTypes Int

  data CIL_Types : Type -> Type where
       CIL_Str   : CIL_Types String
       CIL_Float : CIL_Types Float
       CIL_Ptr   : CIL_Types Ptr
       CIL_Bool  : CIL_Types Bool
       CIL_Unit  : CIL_Types ()
       CIL_IntT  : CIL_IntTypes i -> CIL_Types i
       CIL_RawT  : CIL_RawTypes r t -> CIL_Types t
  --   CIL_FnT   : CIL_FnTypes a -> CIL_Types (CilFn a)

  -- data CilFn t = MkCilFn t
  -- data CIL_FnTypes : Type -> Type where
  --      CIL_Fn      : CIL_Types s -> CIL_FnTypes t -> CIL_FnTypes (s -> t)
  --      CIL_FnIO    : CIL_Types t -> CIL_FnTypes (IO' l t)
  --      CIL_FnBase  : CIL_Types t -> CIL_FnTypes t

FFI_CIL : FFI
FFI_CIL = MkFFI CIL_Types String Type

CIL_IO : Type -> Type
CIL_IO a = IO' FFI_CIL a

-- FFI can be made type safe by declaring singleton types to
-- represent the foreign CIL types and using them in all FFI signatures.
--
-- The internal type is bound to their CIL counterpart via the ToCIL class.
--
%inline
corlib : String -> CILTy
corlib = CILTyRef "mscorlib"

data Object = MkObject
instance ToCIL Object where
  toCIL = corlib "System.Object"

data RuntimeType = MkRuntimeType
instance ToCIL RuntimeType where
  toCIL = corlib "System.Type"

data Assembly = MkAssembly
instance ToCIL Assembly where
  toCIL = corlib "System.Reflection.Assembly"

data MethodInfo = MkMethodInfo
instance ToCIL MethodInfo where
  toCIL = corlib "System.Reflection.MethodInfo"

-- inheritance can be encoded as class instances or implicit conversions
class IsA a b where {}
instance IsA Object MethodInfo where {}

-- implicit MethodInfoIsAObject : MethodInfo -> Object
-- MethodInfoIsAObject m = (believe_me m)

GetExecutingAssembly : CIL_IO Assembly
GetExecutingAssembly =
  foreign FFI_CIL
    "[mscorlib]System.Reflection.Assembly::GetExecutingAssembly"
    (CIL_IO Assembly)

GetType : Assembly -> String -> Bool -> CIL_IO RuntimeType
GetType =
  foreign FFI_CIL
    "instance [mscorlib]System.Reflection.Assembly::GetType"
    (Assembly -> String -> Bool -> CIL_IO RuntimeType)

GetMethod : RuntimeType -> String -> CIL_IO MethodInfo
GetMethod =
  foreign FFI_CIL
    "instance [mscorlib]System.Type::GetMethod"
    (RuntimeType -> String -> CIL_IO MethodInfo)

ToString : IsA Object o => o -> CIL_IO String
ToString o =
  foreign FFI_CIL
    "instance [mscorlib]System.Object::ToString"
    (Object -> CIL_IO String)
    (believe_me o)

exportedIO : CIL_IO ()
exportedIO = putStrLn "exported!"

exportedBoolToString : Bool -> String
exportedBoolToString = show

-- can't be exported because (ToCIL RuntimeType) is not evaluated in the export descriptor
showMethod : RuntimeType -> String -> CIL_IO ()
showMethod t n = do m <- t `GetMethod` n
                    ToString m >>= putStrLn

exports : FFI_Export FFI_CIL "" [] -- export under current module's namespace
exports = Fun exportedIO "VoidFunction" $ -- export function under different name
          Fun exportedBoolToString "" $ -- export function under original name
--          Fun showMethod ""  -- doesn't work becase toCIL applications are not evaluated
          End

Max : Int -> Int -> CIL_IO Int
Max =
  foreign FFI_CIL
    "[mscorlib]System.Math::Max"
    (Int -> Int -> CIL_IO Int)

Substring : String -> Int -> Int -> CIL_IO String
Substring this index count =
  foreign FFI_CIL
    "instance [mscorlib]System.String::Substring"
    (String -> Int -> Int -> CIL_IO String)
    this index count

main : CIL_IO ()
main = do Max 42 1 >>= printLn
          Substring "idris" 2 1 >>= putStrLn
          asm <- GetExecutingAssembly
          type <- GetType asm "Main" True
          for_ ["VoidFunction", "exportedBoolToString"] $
            showMethod type
