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

  def nameTypeFromExpr(c: Context)(name: c.Expr[Any]): c.universe.Type = {
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
      case Some((key, value)) => (c.Expr[Any](Literal(Constant(key))), c.Expr[Any](value))
      case _ => c.abort(c.enclosingPosition, show(pair.tree) + " is not a valid key-value pair")
    }
  }

  def getName[N]: Any = macro getNameImpl[N]

  def getNameImpl[N: c.WeakTypeTag](c: Context)(implicit wttn: c.WeakTypeTag[N]): c.Expr[Any] = {
    import c.universe._
    val n = name[N](c)(wttn)
    c.Expr[Any](Literal(Constant(n)))
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

    val finalTypeParameters = finalKeys.zip(finalTypes).flatMap {
      case (key, value) => List(nameType(c)(key), value)
    }

    val t1params = (1 to params1.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    val t2params = (1 to params2.size / 2) map ((i) => derefField(c)(t.tree, i))
    val finalValues = (t1params ++ t2params).toList

    newTuple0(c)(finalTypeParameters, finalValues)
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

  def finalAppliedType(c: Context)(finalTypeParams: List[c.universe.Type]) = {
    import c.universe._
    val size = finalTypeParams.size / 2
    val t: c.universe.Type =
    if (size == 0) typeOf[ntuple.NTuple0]
    else if (size == 1) typeOf[ntuple.NTuple1[_,_]]
    else if (size == 2) typeOf[ntuple.NTuple2[_,_,_,_]]
    else if (size == 3) typeOf[ntuple.NTuple3[_,_,_,_,_,_]]
    else typeOf[Unit]
    appliedType(t.typeConstructor, finalTypeParams)
  }

  def newTupleImpl(c: Context)(pairs: c.Expr[Any]*) = {
    import c.universe._
    val keyValues = pairs.toList.map(pairToKV(c)(_))

    val finalTypeParams = keyValues.flatMap {
      case (name, value) => List(nameTypeFromExpr(c)(name), value.actualType)
    }
    val finalParams = keyValues.map {
      case (name, value) => value.tree
    }

    newTuple0(c)(finalTypeParams, finalParams)
  }

  def newTuple0(c: Context)(finalTypeParams: List[c.universe.Type], finalParams: List[c.universe.Tree]) = {
    import c.universe._

    val t = finalAppliedType(c)(finalTypeParams)

    c.Expr[Any](`new`(c)(t, finalParams))
  }

  def plusImpl[T](c: Context)(pair: c.Expr[(Any, Any)])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._

    val kv = pairToKV(c)(pair)

    val params = wttToParams(c)(wttt)
    val finalSize = params.size / 2 + 1

    val finalKeys = keys(c)(params) :+  keyName(c)(kv._1)
    val finalTypes = types(c)(params) :+ kv._2.actualType

    val finalTypeParameters = finalKeys.zip(finalTypes).flatMap {
      case (key, value) => List(nameType(c)(key), value)
    }

    val tparams = (1 to params.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    val finalValues = (tparams :+ kv._2.tree).toList

    newTuple0(c)(finalTypeParameters, finalValues)
  }

}

trait NTuple[T <: NTuple[T]] {
  def apply(key: Any) = macro applyImp[T]
  def +(pair: (Any, Any)) = macro plusImpl[T]
  def ++[T2 <: NTuple[T2]](t: T2) = macro plusplusImpl[T,T2]
  def mkString = macro mkStringImpl[T]
}

object NTuple {
  def t(pairs: Any*) = macro newTupleImpl
}

class NTuple0 extends NTuple[NTuple0] {
  override def toString = "()"
}

class NTuple1[N1, T1](val _1: T1) extends NTuple[NTuple1[N1, T1]] {
  override def toString = (_1).toString
}

class NTuple2[N1, T1, N2, T2] (val _1: T1, val _2: T2) extends NTuple[NTuple2[N1, T1, N2, T2]] {
  override def toString = (_1, _2).toString
}

class NTuple3[N1, T1, N2, T2, N3, T3] (val _1: T1, val _2: T2, val _3: T3) extends NTuple[NTuple3[N1, T1, N2, T2, N3, T3]] {
  override def toString = (_1, _2, _3).toString
}

