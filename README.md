# sound, complete

This repo contains a work-in-progress implementation of [Sound and Complete Bidirectional Typechecking for Higher-Rank Polymorphism with Existentials and Indexed Types](http://arxiv.org/abs/1601.05106), which I will refer to by the slightly more radio-friendly "Sound and Complete" hereafter. Once this is done, I plan to use it as the base for a practically useful Haskell-like language with row types, typeclasses, higher-rank polymorphism, GADTs, and composable pattern-matching. (That's the plan, anyway.)

This paper is a sequel to [Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism](http://www.cs.cmu.edu/%7Ejoshuad/papers/bidir/) ("Complete and Easy" hereafter).

## Help wanted!

This is (to my knowledge) the first implementation of Sound and Complete ever. I'm a PLT enthusiast who actually happens to know very little in the way of real typechecker / compiler engineering. If working with / learning from / mentoring me on the (as far as I know) third non-dependently typed language with GADTs sounds interesting, let's talk!

I'm @mrkgnaow on Twitter and chow.soham at Google's mail.

## Features

Sound and Complete is *significantly* more complex (by my inexpert evaluation) than Complete and Easy. However, it extends the latter with a number of highly desirable features.

### Indexed types / GADTs

Indexed types are familiar to Haskell and OCaml programmers as *generalized algebraic data types* or GADTs. The paper specifies a primitive sized-vector type with a builtin `Nat` kind as an example of how GADTs are handled in its system. This is equivalent to the familiar "old saw", but eliminating the need for type-promotion (via the `DataKinds` language extension for Haskell):

```haskell
data Nat = Zero | Succ Nat

data Vec :: Nat -> Type -> Type where
  Nil :: Vec 'Zero a
  Cons :: a -> Vec n a -> Vec ('Succ n) a
```

### A specification for pattern-matching

This is the real confounding factor in adding GADTs to a simple ML or Haskell 98-alike. 

> The hard part about implementing GADTs is pattern matching.
>
> -- @paf31 on [purescript/purescript#1448](https://github.com/purescript/purescript/issues/1448#issue-105282271)

Pattern-matching on a term of an indexed type reveals new information to the typechecker, which must be taken into account while checking the body of the match. Indeed:

```haskell

data Foo a where
  Bar :: Int    -> Foo Int
  Baz :: String -> Foo String
  
modifyFoo :: Foo a -> Foo a
modifyFoo (Bar i) = 
  -- the compiler knows that i is of type Int here!
  2 * i
modifyFoo (Baz i) =
  -- the compiler knows that i is a String in the body of the pattern match,
  -- as before
  i ++ " modified!"
```

Needless to say, this would never work with a simple `data Foo a = Bar a | Baz a` type.

### A specification for exhaustivity (match coverage) checking

This is somewhat related to the previous point and also happens to be a difficult thing to do (Phil refers to this problem in the issue referenced there) in the presence of GADTs. This may seem easy to do for simple types like `Foo`, but more involved indexed types with constructors like

```haskell
data HOAS a where
  WrapFun :: (a -> b) -> HOAS a -> HOAS b
```

quickly make this highly nontrivial. Sound and Complete gives a complete specification for algorithmically checking match coverage.

## References, resources, bibliographical things

### Complete and Easy

* Alexis King has written a clear [implementation](https://github.com/lexi-lambda/higher-rank) of Complete and Easy implementation in Haskell. She is also the principal developer of [Hackett](https://github.com/lexi-lambda/hackett), a Haskell-like language built on the Racket platform.

* The [PureScript](https://github.com/purescript/purescript) language has a type-system inspired by Complete and Easy.

### General language-implementation resources

* [Typing Haskell in Haskell](https://web.cecs.pdx.edu/~mpj/thih/), a small typechecker for most of Haskell 98. A much easier-to-read Markdown version can be found [here](https://gist.github.com/chrisdone/0075a16b32bfd4f62b7b), courtesy of Chris Done.

## (Poorly-thought-through) roadmap

- [ ] finish implementing Sound and Complete
- [ ] write a good test-suite
- [ ] write a frontend
- [ ] write a proof-of-concept interpreter
- [ ] investigate typeclasses
- [ ] LLVM backend
- [ ] don't think too far

## License

GPL-3 for now.
