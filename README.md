Jaqen
=====

A type-safe heterogenous Map or a Named field Tuple depending how you look at it.

* try it:
```
mvn clean compile
scala -classpath jaqen/target/classes
```
Examples: 
```

import ntuple.NTuple._

val foo = "FOO"
val bar = 3

// maps
val map = Map("a" -> foo, "b" -> bar)
map + ("d" -> 3f)
val ma: String = map("a")
val mb: Int = map("b")
map("c")
map - "a"

// tuples
val tuple1 = (foo, bar)

val tuple1a: String = tuple1._1
val tuple1b: Int = tuple1._2
// or
val (tuple1a, tuple1b) = tuple1
 
// tuple with named fields!
val t1 = t('a -> foo, 'b -> bar)
t1.mkString
val t1a: String = t1('a)
val t1b: Int = t1('b)
t1('c) // error: t1 does not contain key: "c"
(t1 - 'b).mkString
val t2 = t1 + ('c -> 2)
t2 + ('c -> 3) // error: t2 already contains key c
(t2 -+ ('c -> 3)).mkString
// also a tuple
t1._1
t1._2
val (t1a, t1b) = t1.toTuple
t1.toMap

val empty = t()
val notempty = empty + ("A" -> foo)
notempty("A")

case class Person(val name: String, val age: Int)
val input = List(Person("John", 10), Person("Jack", 5))

case class PersonBirthYear(val name: String, val birthYear: Int)
input.map((in) => PersonBirthYear(in.name, 2014 - in.age)).filter(_.birthYear > 2005).map(_.name)

input.map((in) => (in.name, 2014 - in.age)).filter{ case (_, birthYear) => birthYear > 2005 }.map { case (name, _) => name }

input.map((in) => t('name -> in.name, 'birthYear -> (2014 - in.age))).filter(_('birthYear) > 2005).map(_('name))


```
