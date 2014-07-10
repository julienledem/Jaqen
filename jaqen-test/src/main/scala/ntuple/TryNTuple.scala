package ntuple

import ntuple.NTuple._
import printexpr.PrintExpr._

class Foo {

}

object TryNTuple {
  def main(args: Array[String]) {
//     printExpr(println(List("a" -> 0, "b" -> "1")))
//     printExpr(t("a" -> "FOO", "b" -> 3).mkString)
     println("mkString: " + t("a" -> "FOO", "b" -> 3).mkString)

     //    printExpr(new NTuple1[Any, Foo](new Foo))
    /*
               param: new ntuple.NTuple1[Any,ntuple.Foo](new Foo())
           raw param: Apply(Select(New(TypeTree().setOriginal(AppliedTypeTree(Ident(ntuple.NTuple1), List(TypeTree().setOriginal(Select(Ident(scala), scala.Any)), TypeTree().setOriginal(Ident(ntuple.Foo)))))), nme.CONSTRUCTOR), List(Apply(Select(New(Ident(ntuple.Foo)), nme.CONSTRUCTOR), List())))
raw param actualType: TypeRef(ThisType(ntuple), ntuple.NTuple1, List(TypeRef(ThisType(scala), scala.Any, List()), TypeRef(ThisType(ntuple), ntuple.Foo, List())))
     */
//    println()
//    printExpr(^("foo"))
//    val a = ^("foo")
    /*
               param: new litsing.LiteralSingleton[String("foo")]()
           raw param: Apply(Select(New(TypeTree()), nme.CONSTRUCTOR), List())
raw param actualType: TypeRef(ThisType(litsing), litsing.LiteralSingleton, List(ConstantType(Constant(foo))))
     */

//    println()
//    printExpr(new Foo)
/*
               param: new Foo()
           raw param: Apply(Select(New(Ident(ntuple.Foo)), nme.CONSTRUCTOR), List())
raw param actualType: TypeRef(ThisType(ntuple), ntuple.Foo, List())

 */

//    printExpr(NTuple1.t("foo", "bar"))

//    printExpr(NTuple1.t("a", new Foo))

    val name = "foo"
    // does not compile: name must be a literal
//    val tuple0 = NTuple1.t(name, "bar")

    val map = Map("a" -> 1, "b" -> "boo")
    val ma = map("a")
    val mb = map("b")
    val map2 = map + ("a" -> 2)
    val ma2 = map2("a")

    // runtime error: key not found: c
//    val mc = map("c")

    val tuple00 = t("a" -> 1)
    println('symbol.name)
    val tuple000 = t('a -> 1)
    val tuple001 = t("a" -> 1, "b" -> "bar")
    val b001 = tuple001("b")
    val a001 = tuple001('a)
    // does not compile: tuple001 does not contain key "c"
//    val c001 = tuple001("c")

    val tuple01 = t("a" -> 1)
    val a01 = tuple01("a")

    val val1 = 1
    val tuple1 = t("a" -> val1)
    println(tuple1)

    val v: Int = tuple1("a")
    println(v)

    // does not compile: name is not a literal
//    val v1: Int = tuple1(name)

    // does not compile: tuple1 does not contain key "b"
//    val v2 = tuple1("b")

    val tuple2 = t("a" -> 1, "b" -> "bar")
    println(tuple2)

    val v3 = tuple2("a")
    println(v3)

    val v4 = tuple2("b")
    println(v4)

    // does not compile: tuple2 does not contain key "c"
//    val v5 = tuple2("c")
    val b = "FOOBAR"
    val tuple3 = t(b)
    println(tuple3("b"))
    println(tuple3('b))

    // does not compile: ntuple.NTuple already contains key a
//    val tuple4 = t('a->1, 'a->2)
//    println(tuple4('a))

    val tuple5 = t("a" -> 1)
    val tuple6 = t("b" -> "bar")
    val tuple7 = tuple5 ++ tuple6
    println("tuple7.toString " + tuple7)
    println("tuple7.mkString " + tuple7.mkString)
    println("tuple7.toMap " + tuple7.toMap)
    val m = t("b" -> "bar").toMap

    // does not compile: tuple7 already contains key a
//    val tuple8 = tuple7 ++ tuple1 ++ tuple7
    val tuple8 = tuple7 ++ tuple1.prefix("t1.") ++ tuple7.prefix("t7.")
//    println("tuple8 " + tuple8)
//     println("tuple8 x 2 " + tuple8 ++ tuple8))

    val tuple9 = t("a" -> 1).-("a")
    println((tuple2 - 'b).mkString)
    println((tuple2 - 'a).mkString)
    println((tuple2 - 'a - "b").mkString)

    println(tuple7.prefix("foo.").mkString)

    val tuple10 = tuple7.prefix("foo.")

    println(tuple10("foo.a"))
    println(tuple7.prefix("foo.").apply("foo.a"))

    println((t("a" -> 1) -+ ("a" -> 2)).mkString)

  }
}
