package ntuple

import scala.language.experimental.macros
import scala.reflect.macros.Context
import java.io.PrintWriter
import java.io.FileOutputStream
import log._
import java.lang.Boolean
import NTupleMacros._
import scala.reflect.api.Symbols

object NTupleMacros {

  def checkMatch[N](c: Context)(key: c.Expr[Any], wttn: c.WeakTypeTag[N]) = {
    name(c)(wttn) == keyName(c)(key)
  }

  def fail(c: Context)(key: c.Expr[Any]) = {
    import c.universe._
    c.abort(c.enclosingPosition, show(c.prefix.tree) + " does not contain key: " + show(key.tree))
  }

  def keyName(c: Context)(key: c.Expr[Any]) = {
    import c.universe._
    key.tree match {
      case Literal(Constant(v)) => v
      case Apply(Select(Select(Ident(scala), symbol), apply), List(Literal(Constant(key))))
                   if (apply.decoded == "apply" && scala.decoded == "scala" && apply.decoded == "apply")
                     => key
      case _ => c.abort(c.enclosingPosition, show(key.tree) + " is not a literal")
    }
  }

  def nameTypeFromExpr(c: Context)(name: c.Expr[String]): c.universe.Type = {
    import c.universe._
    nameType(c)(keyName(c)(name))
  }

  def nameType(c: Context)(name: Any): c.universe.Type = {
    import c.universe._
    ConstantType(Constant(name))
  }

  def name[N](c: Context)(wttn: c.WeakTypeTag[N]) = {
    import c.universe._
    wttn.tpe match {
      case ConstantType(Constant(name)) => name
      case _ => c.abort(c.enclosingPosition, showRaw(wttn.tpe) + " type is not understood")
    }
  }

  def `new`(c: Context)(t: c.Type, params: List[c.universe.Tree]) = {
    import c.universe._
    Apply(Select(New(TypeTree(t)), nme.CONSTRUCTOR), params)
  }

  def pairToKV(c: Context)(pair: c.Expr[Any]) = {
    import c.universe._

    (pair.tree match {
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
             => key match {
                 case Literal(Constant(key)) => Some(key, value)
                 case Apply(Select(Select(Ident(scala), symbol), apply), List(Literal(Constant(key))))
                   if (apply.decoded == "apply" && scala.decoded == "scala" && apply.decoded == "apply")
                     => Some(key, value)
                 case _ => None
                }
      // allow identifiers directly
      case value@Ident(name) => Some(name.decoded, value)
      // do we want magically named "expression" -> expression ?
//      case v => Some((show(v), v))
      case v@_ => Log("INVALID KV", showRaw(v)); None
    }) match {
      case Some((key, value)) => (c.Expr[String](Literal(Constant(key))), c.Expr[Any](value))
      case _ => c.abort(c.enclosingPosition, show(pair.tree) + " is not a valid key-value pair")
    }
  }

  def getName[N]: String = macro getNameImpl[N]

  def getNameImpl[N: c.WeakTypeTag](c: Context)(implicit wttn: c.WeakTypeTag[N]): c.Expr[String] = {
    import c.universe._
    val n = name[N](c)(wttn)
    c.Expr[String](Literal(Constant(n)))
  }

  def wttToParams(c: Context)(wtt: c.WeakTypeTag[_]) = {
    import c.universe._
    wtt.tpe match {
      case TypeRef(ThisType(ntuple), name, parameters) if (ntuple.fullName == "ntuple") => parameters
      case _ => c.abort(c.enclosingPosition, showRaw(wtt) + " is not an understood type")
    }
  }

  def keys(c: Context)(params: List[c.universe.Type]) = {
    import c.universe._
    params
      .zipWithIndex
      .filter(_._2 % 2 == 0)
      .map(_._1)
      .map { case ConstantType(Constant(name)) => name }
  }

  def types(c: Context)(params: List[c.universe.Type]) = {
    import c.universe._
    params
      .zipWithIndex
      .filter(_._2 % 2 == 1)
      .map(_._1)
  }

  def derefField(c: Context)(tree: c.universe.Tree, index: Int) = {
    import c.universe._
    Select(tree, newTermName("_" + index))
  }

  def applyImp[T](c: Context)(key: c.Expr[Any])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    val kName = keyName(c)(key)
    val params = wttToParams(c)(wttt)

    val r = keys(c)(params).zipWithIndex.collect {
          case (name, index) if (name == kName) => index + 1
        }

    if (r.isEmpty) fail(c)(key)
    else if (r.size == 1) c.Expr[Any](Select(c.prefix.tree, newTermName("_" + r(0))))
    else c.abort(c.enclosingPosition, "more than one result for key " + kName)
  }

  def plusplusImpl[T1,T2](c: Context)(t: c.Expr[T2])(implicit wttt1: c.WeakTypeTag[T1], wttt2: c.WeakTypeTag[T2]) = {
    import c.universe._
    val params1 = wttToParams(c)(wttt1)
    val params2 = wttToParams(c)(wttt2)
    val finalSize = (params1.size + params2.size) / 2
    val finalKeys = keys(c)(params1 ++ params2)
    val finalTypes = types(c)(params1 ++ params2)
    val t1params = (1 to params1.size / 2) map ((i) => c.Expr[Any](derefField(c)(c.prefix.tree, i)))
    val t2params = (1 to params2.size / 2) map ((i) => c.Expr[Any](derefField(c)(t.tree, i)))
    val finalValues = t1params ++ t2params
    if (finalSize == 0) reify { new NTuple0 }
    else if (finalSize == 1) NTuple1.newTuple0(c)(finalKeys(0), finalValues(0), finalTypes)
    else if (finalSize == 2) NTuple2.newTuple0(c)(finalKeys(0), finalValues(0), finalKeys(1), finalValues(1), finalTypes)
    else c.abort(c.enclosingPosition, "size can only be up to 2. Got " + finalSize)
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
                  derefField(c)(c.prefix.tree, index + 1),
                  Literal(Constant(", "))
              )
            }.dropRight(1)

    val list = c.Expr[List[Any]](Apply(Select(reify(List).tree, newTermName("apply")), toStringParams))

    reify {
      "(" + list.splice.mkString("") + ")"
    }
  }

  def newTupleImpl(c: Context)(pair: c.Expr[Any]*) = {
    import c.universe._
    if (pair.size == 0) reify { new NTuple0 }
    else if (pair.size == 1) NTuple1.newTupleP(c)(pair(0))
    else if (pair.size == 2) NTuple2.newTupleP(c)(pair(0), pair(1))
    else c.abort(c.enclosingPosition, "size can only be up to 2. Got " + pair.size)
  }

}

trait NTuple[T <: NTuple[T]] {

  def apply(key: Any) = macro applyImp[T]

  def ++[T2 <: NTuple[T2]](t: T2) = macro plusplusImpl[T,T2]

  def mkString = macro mkStringImpl[T]

}

object NTuple {

  def t(pair: Any*) = macro newTupleImpl

}

class NTuple0 extends NTuple[NTuple0] {

  def +(pair1: (Any, Any)) = macro NTuple0.plusImpl

  override def toString = "()"
}

object NTuple0 {

  def plusImpl(c: Context)(pair1: c.Expr[(Any, Any)]) = {
    import c.universe._

    NTuple1.newTupleP(c)(pair1)
  }

}

class NTuple1[N1, T1](val _1: T1) extends NTuple[NTuple1[N1, T1]] {

  def +(pair2: (Any, Any)) = macro NTuple1.plusImpl[N1, T1]

  override def toString = (_1).toString

}

object NTuple1 {

  // TODO: does not work
  def plusImpl[N1, T1](c: Context)(pair2: c.Expr[(Any, Any)])(implicit wttn1: c.WeakTypeTag[N1]) = {
    import c.universe._

    val key1 = c.Expr[String](Literal(Constant(name(c)(wttn1))))

    val e = c.Expr[NTuple1[_,_]](c.prefix.tree)
    val value1 = reify { e.splice._1 }

    val (key2, value2) = pairToKV(c)(pair2)

    NTuple2.newTuple(c)(key1, value1, key2, value2)
  }

  def newTupleP(c: Context)(pair: c.Expr[Any]) = {
    import c.universe._

    val (key, value) = pairToKV(c)(pair)

    newTuple(c)(key, value)
  }

  def newTuple(c: Context)(name: c.Expr[String], v: c.Expr[Any]) = {
    import c.universe._

    val valueType1 = v.actualType

    val nameType1 = nameTypeFromExpr(c)(name)

    val t = appliedType(typeOf[ntuple.NTuple1[_,_]].typeConstructor, List(nameType1, valueType1))
    c.Expr[ntuple.NTuple1[_,_]](`new`(c)(t, List(v.tree)))
  }


  def newTuple0(c: Context)(name1: Any, v1: c.Expr[Any], types: List[c.universe.Type]) = {
    import c.universe._
    val nameType1 = nameType(c)(name1)

    val t = appliedType(typeOf[ntuple.NTuple1[_,_]].typeConstructor, List(nameType1, types(0)))
    c.Expr[ntuple.NTuple2[_,_,_,_]](`new`(c)(t, List(v1.tree)))
  }

}

class NTuple2[N1, T1, N2, T2] (val _1: T1, val _2: T2) extends NTuple[NTuple2[N1, T1, N2, T2]] {

  override def toString = (_1, _2).toString

}

object NTuple2 {

  def newTupleP(c: Context)(pair1: c.Expr[Any], pair2: c.Expr[Any]) = {
    import c.universe._

    val (key1, value1) = pairToKV(c)(pair1)
    val (key2, value2) = pairToKV(c)(pair2)

    newTuple(c)(key1, value1, key2, value2)
  }

  def newTuple(c: Context)(name1: c.Expr[String], v1: c.Expr[Any], name2: c.Expr[String], v2: c.Expr[Any]) = {
    import c.universe._
    val nameType1 = nameTypeFromExpr(c)(name1)
    val nameType2 = nameTypeFromExpr(c)(name2)

    val valueType1 = v1.actualType
    val valueType2 = v2.actualType

    val t = appliedType(typeOf[ntuple.NTuple2[_,_,_,_]].typeConstructor, List(nameType1, valueType1, nameType2, valueType2))
    c.Expr[ntuple.NTuple2[_,_,_,_]](`new`(c)(t, List(v1.tree, v2.tree)))
  }

  def newTuple0(c: Context)(name1: Any, v1: c.Expr[Any], name2: Any, v2: c.Expr[Any], types: List[c.universe.Type]) = {
    import c.universe._
    val nameType1 = nameType(c)(name1)
    val nameType2 = nameType(c)(name2)

    val t = appliedType(typeOf[ntuple.NTuple2[_,_,_,_]].typeConstructor, List(nameType1, types(0), nameType2, types(1)))
    c.Expr[ntuple.NTuple2[_,_,_,_]](`new`(c)(t, List(v1.tree, v2.tree)))
  }

}
