import std/options
import std/macros
import ./binding
import ./chaining
import ./indexing
import ./operators
import ./without

include ./private/errorban

export options except get
export binding
export chaining
export indexing
export without

template `?`*(T: typed): type Option[T] =
  ## Use `?` to make a type optional. For example the type `?int` is short for
  ## `Option[int]`.

  Option[T]

template `!`*[T](option: ?T): T =
  ## Returns the value of an Option when you're absolutely sure that it
  ## contains value. Using `!` on an Option without a value raises a Defect.

  option.get

template `-->?`*[T, U](option: ?T, expression: U): untyped =
  if option.isSome:
    expression

template `->?`*[T,U](option: ?T, expression: ?U): ?U =
  if option.isSome:
    expression
  else:
    U.none

template `->?`*[T,U](option: ?T, expression: U): ?U =
  option ->? expression.some

template `->?`*[T,U,V](options: (?T, ?U), expression: ?V): ?V =
  if options[0].isSome and options[1].isSome:
    expression
  else:
    V.none

template `->?`*[T,U,V](options: (?T, ?U), expression: V): ?V =
  options ->? expression.some

template `|?`*[T](option: ?T, fallback: T): T =
  ## Use the `|?` operator to supply a fallback value when an Option does not
  ## hold a value.

  if option.isSome:
    option.unsafeGet()
  else:
    fallback

template `|?`*[T](option: ?T, fallback: ?T): ?T =
  ## Use the `|?` operator to supply a fallback value when an Option does not
  ## hold a value.

  if option.isSome:
    option
  else:
    fallback

macro `.?`*[T](option: ?T, brackets: untyped{nkBracket}): untyped =
  let index = brackets[0]
  result = quote do:
    type U = typeof(`option`.unsafeGet().?[`index`].unsafeGet())
    if `option`.isSome:
      `option`.unsafeGet().?[`index`]
    else:
      U.none
  #echo result.treeRepr

Option.liftUnary(`-`)
Option.liftUnary(`+`)
Option.liftUnary(`@`)
Option.liftBinary(`[]`)
Option.liftBinary(`*`)
Option.liftBinary(`/`)
Option.liftBinary(`div`)
Option.liftBinary(`mod`)
Option.liftBinary(`shl`)
Option.liftBinary(`shr`)
Option.liftBinary(`+`)
Option.liftBinary(`-`)
Option.liftBinary(`&`)
Option.liftBinary(`<=`)
Option.liftBinary(`<`)
Option.liftBinary(`>=`)
Option.liftBinary(`>`)
