
namespace HList
	data HList : List Type -> Type where
		Nil : HList []
		(::) : t -> HList ts -> HList (t :: ts)
	
	head : HList (t :: ts) -> t
	head (x :: xs) = x
	
	tail : HList (t :: ts) -> HList ts
	tail (x :: xs) = xs
	
	take : (n : Nat) -> HList ts -> HList (take n ts)
	take Z     xs = []
	take (S n) [] = []
	take (S n) (x :: xs) = x :: take n xs
	
	drop : (n : Nat) -> HList ts -> HList (drop n ts)
	drop Z xs = xs
	drop (S n) [] = []
	drop (S n) (x :: xs) = drop n xs