package ntuple

import scala.language.experimental.macros
import scala.reflect.macros.Context
import log._
import NTupleMacros._
import scala.collection.IterableLike
import scala.collection.immutable.Iterable

object NTupleMacros {

  private def fail(c: Context)(message: String) = {
    import c.universe._
    c.abort(c.enclosingPosition, message)
  }

  private def keyName(c: Context)(key: c.Tree): Any = {
    import c.universe._
    key match {
      case Literal(Constant(v)) => v
      case Apply(Select(Select(Ident(scala), symbol), apply), List(Literal(Constant(key))))
                   if (apply.decoded == "apply" && scala.decoded == "scala")
                     => key
      case _ => fail(c)(show(key) + " is not a literal")
    }
  }

  private def keyNameToKeyType(c: Context)(name: Any): c.universe.Type = {
    import c.universe._
    ConstantType(Constant(name))
  }

  private def keyTypeToKeyName(c: Context)(t: c.Type) = {
    import c.universe._
    t match {
      case ConstantType(Constant(name)) => name
      case _ => fail(c)(showRaw(t) + " type is not understood")
    }
  }

  private def `new`(c: Context)(t: c.Type, params: List[c.universe.Tree]) = {
    import c.universe._
    Apply(Select(New(TypeTree(t)), nme.CONSTRUCTOR), params)
  }

  private def pairToKV(c: Context)(pair: c.Expr[Any]): (Any, c.universe.Tree) = {
    import c.universe._

    pair.tree match {
      // TODO: allow tuple2
      case Apply(
             TypeApply(Select(
                 Apply(
                     TypeApply(Select(Select(This(_), _), assoc), List(TypeTree())),
                     List(key)
                 ),
                 arrow
             ),
             List(TypeTree())),
             List(value)
          ) if (arrow.decoded == "->" && assoc.decoded == "any2ArrowAssoc")
             => (keyName(c)(key), value)
      // allow identifiers directly
      case value@Ident(name) => (name.decoded, value)
      // do we want magically named "expression" -> expression ?
//      case v => (show(v), v)
      case _ => fail(c)(show(pair.tree) + " is not a valid key-value pair")
    }
  }

  private def wttToParams(c: Context)(wtt: c.WeakTypeTag[_]) = {
    import c.universe._
    wtt.tpe match {
      case TypeRef(ThisType(ntuplePackage), nTupleName, parameters) => parameters
      case _ => fail(c)(showRaw(wtt) + " is not an understood type")
    }
  }

  private def keys(c: Context)(params: List[c.universe.Type]) = {
    import c.universe._
    params
      .zipWithIndex
      .filter(_._2 % 2 == 0)
      .map((t) => keyTypeToKeyName(c)(t._1))
  }

  private def types(c: Context)(params: List[c.universe.Type]) = {
    import c.universe._
    params
      .zipWithIndex
      .filter(_._2 % 2 == 1)
      .map(_._1)
  }

  private def derefField(c: Context)(tree: c.universe.Tree, index: Int) = {
    import c.universe._
    Select(tree, newTermName("_" + (index + 1)))
  }

  private def newTuple(c: Context)(finalTypeParams: List[c.universe.Type], finalParams: List[c.universe.Tree]) = {
    import c.universe._
    try {
      val distinctKeys = keys(c)(finalTypeParams)
          .foldLeft(Set.empty[Any])(
              (agg, key) =>
                if (agg.contains(key))
                  fail(c)(show(c.prefix.tree) + " already contains key " + key)
                else
                  agg + key
          )
      if (distinctKeys.size != finalParams.size) {
        fail(c)("keys size does not match values size " + distinctKeys.size + " != " + finalParams.size)
      }
      val rawType = c.mirror.staticClass(classOf[NTuple[_]].getName() + finalParams.size).toType
      val t = appliedType(rawType.typeConstructor, finalTypeParams)
      c.Expr[Any](`new`(c)(t, finalParams))
    } catch {
      case e: scala.reflect.internal.MissingRequirementError => fail(c)("no NTuple of size " + finalParams.size)
    }
  }

  private def mkTypeParams(c: Context)(keys: Iterable[Any], types: Iterable[c.universe.Type]) = keys.zip(types).flatMap {
        case (key, value) => List(keyNameToKeyType(c)(key), value)
      }.toList

  private def keyIndex[T](c: Context)(key: c.Expr[Any], wtt: c.WeakTypeTag[T]) = {
    import c.universe._
    val kName = keyName(c)(key.tree)
    val params = wttToParams(c)(wtt)
    val r = keys(c)(params).zipWithIndex.collect {
          case (name, index) if (name == kName) => index
        }
    if (r.isEmpty) c.abort(c.enclosingPosition, show(c.prefix.tree) + " does not contain key " + kName)
    else if (r.size > 1) fail(c)("more than one result for key " + kName)
    r(0)
  }

  private def removeIndex[U](i:Int, l: Iterable[U]) = l.zipWithIndex.collect{ case (v, index) if index != i => v } toList

  def applyImp[T](c: Context)(key: c.Expr[Any])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    c.Expr[Any](derefField(c)(c.prefix.tree, keyIndex(c)(key, wttt)))
  }

  def plusplusImpl[T1,T2](c: Context)(t: c.Expr[T2])(implicit wttt1: c.WeakTypeTag[T1], wttt2: c.WeakTypeTag[T2]) = {
    import c.universe._
    val params1 = wttToParams(c)(wttt1)
    val params2 = wttToParams(c)(wttt2)

    val t1params = (0 until params1.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    val t2params = (0 until params2.size / 2) map ((i) => derefField(c)(t.tree, i))

    newTuple(c)(params1 ++ params2, (t1params ++ t2params).toList)
  }

  def mkStringImpl[T](c: Context)(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    val params = wttToParams(c)(wttt)

    val toStringParams = keys(c)(params)
            .zipWithIndex
            .flatMap {
              case (name, index) => List(
                  Literal(Constant(name)),
                  Literal(Constant(" -> ")),
                  derefField(c)(c.prefix.tree, index),
                  Literal(Constant(", "))
              )
            }.dropRight(1)

    val list = c.Expr[List[Any]](Apply(Select(reify(List).tree, newTermName("apply")), toStringParams))

    reify {
      "(" + list.splice.mkString("") + ")"
    }
  }

  def newTupleImpl(c: Context)(pairs: c.Expr[Any]*) = {
    import c.universe._
    val keyValues = pairs.toList.map(pairToKV(c)(_))

    val finalTypeParams = keyValues.flatMap {
      case (name, value) => List(keyNameToKeyType(c)(name), c.Expr[Any](value).actualType)
    }
    val finalParams = keyValues.map {
      case (name, value) => value
    }

    newTuple(c)(finalTypeParams, finalParams)
  }

  def plusImpl[T](c: Context)(pair: c.Expr[(Any, Any)])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._

    val (key, value) = pairToKV(c)(pair)
    val params = wttToParams(c)(wttt)

    val finalKeys = keys(c)(params) :+ key
    val finalTypes = types(c)(params) :+ c.Expr[Any](value).actualType

    val tparams = (0 until params.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    val finalValues = (tparams :+ value).toList

    newTuple(c)(mkTypeParams(c)(finalKeys, finalTypes), finalValues)
  }

  def minusImpl[T](c: Context)(key: c.Expr[Any])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    val params = wttToParams(c)(wttt)
    val i = keyIndex(c)(key, wttt)
    val finalKeys = removeIndex(i, keys(c)(params))
    val finalTypes = removeIndex(i, types(c)(params))
    val finalValues = removeIndex(i, 0 until params.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    newTuple(c)(mkTypeParams(c)(finalKeys, finalTypes), finalValues)
  }

  def replaceImpl[T](c: Context)(pair: c.Expr[(Any, Any)])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._

    val (key, value) = pairToKV(c)(pair)
    val params = wttToParams(c)(wttt)
    val i = keyIndex(c)(c.Expr[Any](Literal(Constant(key))), wttt)

    val finalKeys = removeIndex(i, keys(c)(params)) :+ key
    val finalTypes = removeIndex(i, types(c)(params)) :+ c.Expr[Any](value).actualType

    val tparams = removeIndex(i, 0 until params.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    val finalValues = (tparams :+ value)

    newTuple(c)(mkTypeParams(c)(finalKeys, finalTypes), finalValues)
  }

  def prefixImpl[T](c: Context)(prefix: c.Expr[String])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._

    val prefixString = keyName(c)(prefix.tree)
    val params = wttToParams(c)(wttt)

    val finalKeys = keys(c)(params).map((a) => prefixString + String.valueOf(a))
    val finalTypes = types(c)(params)

    val finalValues = (0 until params.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    newTuple(c)(mkTypeParams(c)(finalKeys, finalTypes), finalValues.toList)
  }

  def toMapImpl[T](c: Context)(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    val params = wttToParams(c)(wttt)
    val ts = types(c)(params)
    val mapParams = keys(c)(params)
            .zipWithIndex
            .map {
              case (name, index) =>
                Apply(Select(reify(Tuple2).tree, newTermName("apply")),
                    List(
                        Literal(Constant(name)),
                        derefField(c)(c.prefix.tree, index)
                    )
                )
            }
    c.Expr[Map[Any, Any]](Apply(Select(reify(Map).tree, newTermName("apply")), mapParams))
  }

  def mapImpl[T](c: Context)(pair: c.Expr[Any], f: c.Expr[Any])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    val params = wttToParams(c)(wttt)
    val (sources, target) = pair.tree match {
      case Apply(
             TypeApply(
               Select(
                 Apply(
                     TypeApply(Select(scalaPredef, assoc), List(TypeTree())),
                     List(
                         Apply(
                             TypeApply(
                                 Select(Select(Ident(scala), tupleClass), apply),
                                 types
                              ),
                              sources
                         )
                     )
                 ),
                 arrow
             ),
             List(TypeTree())),
             List(target)
          ) if (arrow.decoded == "->"
                && assoc.decoded == "any2ArrowAssoc"
                && scala.decoded == "scala"
                && tupleClass.decoded.startsWith("Tuple")
                && apply.decoded == "apply")
             => (sources, target)
      case _ => fail(c)(show(pair.tree) + " is not a valid mapping")
    }

    val finalKeys = keys(c)(params) :+ keyName(c)(target)

    val t = f.actualType match {
      case TypeRef(
            ThisType(scala),
            function,
            types) if (function.fullName.startsWith("scala.Function")) => types.last
      case _ => fail(c)(show(f) + " is not a valid function")
    }

    val finalTypes = types(c)(params) :+ t

    val tparams = (0 until params.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    val fParams = sources map (keyName(c)(_)) map ((key) => derefField(c)(c.prefix.tree, keyIndex(c)(c.Expr[Any](Literal(Constant(key))), wttt)))
    val appF = Apply(Select(f.tree, newTermName("apply")), fParams)
    val finalValues = (tparams :+ appF).toList
    newTuple(c)(mkTypeParams(c)(finalKeys, finalTypes), finalValues)

  }

}

object Generator {
  def main(args: Array[String]) {
    for (i <- 1 to 22) {
      val sig = "NTuple" + i + "[" + (for (j <- 1 to i) yield "N" + j + ", T" + j).mkString(", ") + "]"
      println("class " + sig + "(" + (for (j <- 1 to i) yield "val _" + j + ": T" + j).mkString(", ") + ") extends NTuple[" + sig + "] {")
      println("  def toTuple = (" + (for (j <- 1 to i) yield "_" + j).mkString(", ") + ")")
      println("  override def toString = toTuple.toString")
      println("}")
    }
  }
}

trait NTuple[T <: NTuple[T]] {

  def get(key: Any) = macro applyImp[T]
  def apply(key: Any) = macro applyImp[T]

  def add(pair: (Any, Any)) = macro plusImpl[T]
  def +(pair: (Any, Any)) = macro plusImpl[T]

  def concat[T2 <: NTuple[T2]](t: T2) = macro plusplusImpl[T,T2]
  def ++[T2 <: NTuple[T2]](t: T2) = macro plusplusImpl[T,T2]

  def remove(key: Any) = macro minusImpl[T]
  def -(key: Any) = macro minusImpl[T]

  def replace(pair: (Any, Any)) = macro replaceImpl[T]
  def -+(pair: (Any, Any)) = macro replaceImpl[T]

  def prefix(prefix: String) = macro prefixImpl[T]

  // tuple.map(('a, 'b) -> 'c, (a, b) => a + b)
//  def map(pair: Any) = macro mapImpl[T]
  def map(pair: Any, f: Any) = macro mapImpl[T]

//  def map2(pair: Any) = macro map2Impl[T]

  def mkString = macro mkStringImpl[T]
  def toMap = macro toMapImpl[T]
}

object NTuple {
  def t(pairs: Any*) = macro newTupleImpl
}

class NTuple0 extends NTuple[NTuple0] {
  override def toString = "()"
}
// classes bellow have been generated by the object Generator above
class NTuple1[N1, T1](val _1: T1) extends NTuple[NTuple1[N1, T1]] {
  def toTuple = (_1)
  override def toString = toTuple.toString
}
class NTuple2[N1, T1, N2, T2](val _1: T1, val _2: T2) extends NTuple[NTuple2[N1, T1, N2, T2]] {
  def toTuple = (_1, _2)
  override def toString = toTuple.toString
}
class NTuple3[N1, T1, N2, T2, N3, T3](val _1: T1, val _2: T2, val _3: T3) extends NTuple[NTuple3[N1, T1, N2, T2, N3, T3]] {
  def toTuple = (_1, _2, _3)
  override def toString = toTuple.toString
}
class NTuple4[N1, T1, N2, T2, N3, T3, N4, T4](val _1: T1, val _2: T2, val _3: T3, val _4: T4) extends NTuple[NTuple4[N1, T1, N2, T2, N3, T3, N4, T4]] {
  def toTuple = (_1, _2, _3, _4)
  override def toString = toTuple.toString
}
class NTuple5[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5) extends NTuple[NTuple5[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5]] {
  def toTuple = (_1, _2, _3, _4, _5)
  override def toString = toTuple.toString
}
class NTuple6[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6) extends NTuple[NTuple6[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6]] {
  def toTuple = (_1, _2, _3, _4, _5, _6)
  override def toString = toTuple.toString
}
class NTuple7[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7) extends NTuple[NTuple7[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7)
  override def toString = toTuple.toString
}
class NTuple8[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8) extends NTuple[NTuple8[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8)
  override def toString = toTuple.toString
}
class NTuple9[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9) extends NTuple[NTuple9[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9)
  override def toString = toTuple.toString
}
class NTuple10[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10) extends NTuple[NTuple10[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10)
  override def toString = toTuple.toString
}
class NTuple11[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11) extends NTuple[NTuple11[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11)
  override def toString = toTuple.toString
}
class NTuple12[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12) extends NTuple[NTuple12[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12)
  override def toString = toTuple.toString
}
class NTuple13[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13) extends NTuple[NTuple13[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13)
  override def toString = toTuple.toString
}
class NTuple14[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14) extends NTuple[NTuple14[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14)
  override def toString = toTuple.toString
}
class NTuple15[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15) extends NTuple[NTuple15[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15)
  override def toString = toTuple.toString
}
class NTuple16[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16) extends NTuple[NTuple16[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16)
  override def toString = toTuple.toString
}
class NTuple17[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17) extends NTuple[NTuple17[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17)
  override def toString = toTuple.toString
}
class NTuple18[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18) extends NTuple[NTuple18[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18)
  override def toString = toTuple.toString
}
class NTuple19[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19) extends NTuple[NTuple19[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19)
  override def toString = toTuple.toString
}
class NTuple20[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20) extends NTuple[NTuple20[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20)
  override def toString = toTuple.toString
}
class NTuple21[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20, val _21: T21) extends NTuple[NTuple21[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21)
  override def toString = toTuple.toString
}
class NTuple22[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21, N22, T22](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20, val _21: T21, val _22: T22) extends NTuple[NTuple22[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21, N22, T22]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, _22)
  override def toString = toTuple.toString
}