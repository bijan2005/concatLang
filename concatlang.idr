
import hlist

data DataType : Type where
	TyInt : DataType
	TyChar : DataType
	
	TyPair : DataType -> DataType -> DataType
	TyList : DataType -> DataType

resultOf : DataType -> Type
resultOf TyInt = Int
resultOf TyChar = Char
resultOf (TyPair f s) = (resultOf f, resultOf s)
resultOf (TyList t) = List (resultOf t)

ConcatFunc : List DataType -> List DataType -> Type
ConcatFunc ss ds = HList (map resultOf ss) -> HList (map resultOf ds)