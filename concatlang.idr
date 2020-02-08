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

function : List Type -> Type -> Type
function [] r = r
function (t :: ts) r = t -> function ts r

apply : function ts r -> HList ts -> r
apply x [] = x
apply f (x :: xs) = apply (f x) xs

convert : function (map resultOf ts) (resultOf r) -> ConcatFunc ts [r]
convert f = \x => apply f x :: Nil

namespace ConcatPrimitives
	plus : ConcatFunc [TyInt, TyInt] [TyInt]
	plus = the (ConcatFunc [TyInt, TyInt] [TyInt]) $
			convert ((+) {ty = Int})
	
	sub : ConcatFunc [TyInt, TyInt] [TyInt]
	sub = the (ConcatFunc [TyInt, TyInt] [TyInt]) $
			convert ((-) {ty = Int})
	
	mult : ConcatFunc [TyInt, TyInt] [TyInt]
	mult = the (ConcatFunc [TyInt, TyInt] [TyInt]) $
			convert ((*) {ty = Int})
	
	dup : ConcatFunc [x] [x, x]
	dup xs = let x = index Z xs in [x, x]