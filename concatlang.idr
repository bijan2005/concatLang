import hlist

data DataType : Type where
	TyInt : DataType
	TyChar : DataType
	
	TyPair : DataType -> DataType -> DataType
	TyList : DataType -> DataType
	TyFunc : List DataType -> List DataType -> DataType

mutual
	resultOf : DataType -> Type
	resultOf TyInt = Int
	resultOf TyChar = Char
	resultOf (TyPair f s) = (resultOf f, resultOf s)
	resultOf (TyList t) = List (resultOf t)
	resultOf (TyFunc ss ds) = ConcatFunc ss ds

	ConcatFunc : List DataType -> List DataType -> Type
	ConcatFunc ss ds = HList (map resultOf ss) -> HList (map resultOf ds)

data Stack : List DataType -> Type where
	Nil : Stack []
	(::) : resultOf t -> Stack ts -> Stack (t :: ts)