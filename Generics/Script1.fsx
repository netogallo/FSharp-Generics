type Comp = A of int | B of string | C of bool

type List<'t> = Cons of 't*List<'t> | SemiCons of 't | Nil

let g = Generic<List<Comp>>()

g.To(Cons(A 4, Cons ((B "hello"), Cons((C true), Nil)))).Everywhere<Meta>(id)