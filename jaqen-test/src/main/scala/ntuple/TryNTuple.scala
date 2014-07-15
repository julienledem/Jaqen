package ntuple

import ntuple.NTuple._
import printexpr.PrintExpr._

class Foo {

}

object TryNTuple {
  def main(args: Array[String]) {
     println("mkString: " + t("a" -> "FOO", "b" -> 3).mkString)
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
    println(t("a" -> 1, "b" -> "bar") + "")
    println("" + t("a" -> 1, "b" -> "bar"))
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
//restore //    val tuple8 = tuple7 ++ tuple1.prefix("t1.") ++ tuple7.prefix("t7.")
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

    val tuple11 = t('a -> 1, 'b ->2)
    val tuple12 = tuple11 + ('c -> (tuple11('a) + tuple11('b)))
    val f = (a: Int, b: Int) => a + b
//    printExpr((a: Int, b: Int) => a + b)

//    printExpr(f)
    val tuple13 = tuple11.map(('a, 'b) -> 'c) { (a: Int, b: Int) => a + b }
//    val tuple14 = tuple11.map(('a, 'b) -> 'a) { (a: Int, b: Int) => a + b }
    println(tuple13.mkString)

    def foo(a: Int)(b: Int) = a + b

//    printExpr({
//      class Function1Impl extends Function1[(Int, Int) => Any, Any] {
//        def apply[T](f: (Int,Int)=>T) = new NTuple3(tuple11._1, tuple11._2, f(tuple11._1, tuple11._2))
//      }
//      new Function1Impl().apply[Int]((a,b) => a + b)
//    })
//
//    val tuple14 = {
//      class Function1Impl extends Function1[(Int, Int) => Any, Any] {
//        def apply[T](f: (Int,Int)=>T) = new NTuple3(tuple11._1, tuple11._2, f(tuple11._1, tuple11._2))
//      }
//      new Function1Impl().apply[Int]((a,b) => a + b)
//    }
    val tuple15 = t('a -> 1, 'b -> 2)
    println("blah")
    def fooFunction[N1, T1, N2, T2](tuple: NTuple2[N1, T1, N2, T2]) = {
//      printExpr(new ntuple.NFunction2[T1, T2, Any] (tuple._1, tuple._2, tuple))
      printExpr(new ntuple.NFunction2[T1, T2, N2] (tuple._1, tuple._2, tuple) {
        type NTUPLENP1[N, T] = NTuple3[N1, T1, N2, T2, N, T]
      })
      new ntuple.NFunction2[T1, T2, Any] (tuple._1, tuple._2, tuple) {
        type NTUPLENP1[N, T] = NTuple3[N1, T1, N2, T2, N, T]
      }
    }
    val foof1 = fooFunction(tuple15)
    val foofr1 = foof1 { (a, b) => a + b }
    val tuple16 = fooFunction(tuple15) { (a, b) => a + b }
//    println (tuple16.mkString)

    val foof = tuple15.map2(('a, 'b) -> 'c)
    val foofr = foof.apply((a, b) => a + b)
//println (foofr.mkString)
    val tuple17 = tuple15.map2(('a, 'b) -> 'c).apply(_ + _)
    println ("WOOHOO")
    println (tuple17.mkString)
//    val tuple18 = tuple15.map2(('a, 'b) -> 'c) { _ + _ }

  }
}
