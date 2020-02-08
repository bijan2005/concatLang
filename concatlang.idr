
namespace HList
	data HList : List Type -> Type where
		Nil : HList []
		(::) : t -> HList ts -> HList (t :: ts)
