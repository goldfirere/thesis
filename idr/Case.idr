module Case

ty : Bool -> Type
ty x = case x of True => Integer; False => Char

f : (x : Bool) -> ty x
f x = case x of True => 5; False => 'x'

g : (x : Bool) -> ty x
g x = the (ty x)
          (case x of True => 5; False => 'x')
{-
h : (x : Bool) -> ty x
h x = the (case x of True => Integer; False => Char)
          (case x of True => 5; False => 'x')
-}
{-
h : Int
h = 5

i : Integer
i = 5
-}

fix : (a -> a) -> a
fix f = f (fix f)

i : Bool -> Bool
i True = False

j : Bool -> Bool
j = i
