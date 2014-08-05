Date: Fri, 25 Jul 2014 11:48:47 +0200
From: Arthur Azevedo de Amorim <arthur.aa@gmail.com>
Subject: Re: [Coq-Club] Function that transforms types

Hi Bruno,

You can solve your problem by using one level of indirection. Instead
of writing f : Type -> Type, you can define a type "code", together
with a function denote : code -> Type:

Inductive code :=
| Arrow : code -> code -> code (* Function type *)
| (*... other types *)...

Fixpoint denote (c : code) : Type :=
match c with
| Arrow c1 c2 => denote c1 -> denote c2
| (* ... *)
end.

having done that, you can then define f directly on "code". You'll
have to restrict your universe of types to do this, but this should be
enough for many applications.

Best,



Date: Fri, 25 Jul 2014 12:13:55 +0200
From: Cedric Auger <sedrikov@gmail.com>
Subject: Re: [Coq-Club] Function that transforms types

2014-07-25 11:36 GMT+02:00 Bruno Woltzenlogel Paleo <bruno.wp@gmail.com>:

Hi!

I would like to implement a function that takes a type and returns another
type.
What I have in mind is something like this:

=====================
(* wrong code below! *)

Parameter i: Type.

Fixpoint f(A: Type) := match A with
| (A1 -> A2) => i -> f(A1) -> f(A2)
| A0 => i -> A0
end.
======================

I understand why this is wrong (in so many ways!).

My question is: is it possible at all to achieve this kind of type
transformation in some other way? If yes, how?


You can reify your types:

Inductive TypeStruct : Type -> Type :=
| Arrow : forall (A B : Type), TypeStruct A -> TypeStruct B -> TypeStruct
(A -> B)
| Leaf : forall (A : Type), TypeStruct A.

Fixpoint f(A:Type) (TA : TypeStruct A) :=
 match TA (* in TypeStruct A return <your output type which depends on A>
*) with
 | Arrow a b ta tb => i -> (f a ta) -> (f b tb)
 | Leaf a => i -> a
 end.

Example:

Definition Stransf : forall A B, f (A -> B) (Leaf (A->B)) -> f (A -> B)
(Arrow A B (Leaf A) (Leaf B)) :=
 fun A B (g : i -> A -> B) (x : i) (h : i -> A) (y : i) =>
 g x (h y).


You may also want to keep it reified:

Parameter i: Type.
Parameter si: TypeStruct i.

Record TTS := TTS_cons { ty : Type; sty : TypeStruct ty }.

Fixpoint f(A:Type) (TA : TypeStruct A) : {T & TypeStruct T} :=
 match TA (* in TypeStruct A return <your output type which depends on A>
*) with
 | Arrow a b ta tb =>
   let na := ty (f a ta) in
   let sna := sty (f a ta) in
   let nb := ty (f b tb) in
   let snb := sty (f b tb) in
   TTS_cons (i -> na -> nb)
                   (Arrow i (na -> nb) si (Arrow na nb sna snb)
 | Leaf a => TTS_cons i a si (Leaf a)
 end.




Best regards,

Bruno




--
.../Sedrikov\...