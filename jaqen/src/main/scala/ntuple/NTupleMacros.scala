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

  def fail(c: Context)(message: String) = {
    import c.universe._
    c.abort(c.enclosingPosition, message)
  }

  def keyName(c: Context)(key: c.Tree): Any = {
    import c.universe._
    key match {
      case Literal(Constant(v)) => v
      case Apply(Select(Select(Ident(scala), symbol), apply), List(Literal(Constant(key))))
                   if (apply.decoded == "apply" && scala.decoded == "scala")
                     => key
      case _ => fail(c)(show(key) + " is not a literal")
    }
  }

  def keyNameToKeyType(c: Context)(name: Any): c.universe.Type = {
    import c.universe._
    ConstantType(Constant(name))
  }

  def keyTypeToKeyName(c: Context)(t: c.Type) = {
    import c.universe._
    t match {
      case ConstantType(Constant(name)) => name
      case _ => fail(c)(showRaw(t) + " type is not understood")
    }
  }

  def `new`(c: Context)(t: c.Type, params: List[c.universe.Tree]) = {
    import c.universe._
    Apply(Select(New(TypeTree(t)), nme.CONSTRUCTOR), params)
  }

  def pairToKV(c: Context)(pair: c.Expr[Any]): (Any, c.universe.Tree) = {
    import c.universe._

    pair.tree match {
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

  def wttToParams(c: Context)(wtt: c.WeakTypeTag[_]) = {
    import c.universe._
    wtt.tpe match {
      case TypeRef(ThisType(ntuple), name, parameters) if (ntuple.fullName == "ntuple") => parameters
      case _ => fail(c)(showRaw(wtt) + " is not an understood type")
    }
  }

  def keys(c: Context)(params: List[c.universe.Type]) = {
    import c.universe._
    params
      .zipWithIndex
      .filter(_._2 % 2 == 0)
      .map((t) => keyTypeToKeyName(c)(t._1))
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

  def finalAppliedType(c: Context)(finalTypeParams: List[c.universe.Type]): c.universe.Type = {
    import c.universe._
    val size = finalTypeParams.size / 2
    val t: c.universe.Type =
    if (size == 0) typeOf[ntuple.NTuple0]
    else if (size == 1) typeOf[ntuple.NTuple1[_,_]]
    else if (size == 2) typeOf[ntuple.NTuple2[_,_,_,_]]
    else if (size == 3) typeOf[ntuple.NTuple3[_,_,_,_,_,_]]
    else c.abort(c.enclosingPosition, "maximum tuple size is 3. Got " + size)
    appliedType(t.typeConstructor, finalTypeParams)
  }

  def newTuple(c: Context)(finalTypeParams: List[c.universe.Type], finalParams: List[c.universe.Tree]) = {
    import c.universe._

    val t = finalAppliedType(c)(finalTypeParams)

    c.Expr[Any](`new`(c)(t, finalParams))
  }

  def applyImp[T](c: Context)(key: c.Expr[Any])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    val kName = keyName(c)(key.tree)
    val params = wttToParams(c)(wttt)

    val r = keys(c)(params).zipWithIndex.collect {
          case (name, index) if (name == kName) => index + 1
        }

    if (r.isEmpty) c.abort(c.enclosingPosition, show(c.prefix.tree) + " does not contain key " + kName)
    else if (r.size == 1) c.Expr[Any](derefField(c)(c.prefix.tree, r(0)))
    else fail(c)("more than one result for key " + kName)
  }

  def plusplusImpl[T1,T2](c: Context)(t: c.Expr[T2])(implicit wttt1: c.WeakTypeTag[T1], wttt2: c.WeakTypeTag[T2]) = {
    import c.universe._
    val params1 = wttToParams(c)(wttt1)
    val params2 = wttToParams(c)(wttt2)
    val finalSize = (params1.size + params2.size) / 2

    val finalKeys = keys(c)(params1 ++ params2)
    val finalTypes = types(c)(params1 ++ params2)

    val finalTypeParameters = finalKeys.zip(finalTypes).flatMap {
      case (key, value) => List(keyNameToKeyType(c)(key), value)
    }

    val t1params = (1 to params1.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    val t2params = (1 to params2.size / 2) map ((i) => derefField(c)(t.tree, i))
    val finalValues = (t1params ++ t2params).toList

    newTuple(c)(finalTypeParameters, finalValues)
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

    val kv = pairToKV(c)(pair)
    val params = wttToParams(c)(wttt)
    val finalSize = params.size / 2 + 1

    val finalKeys = keys(c)(params) :+ kv._1
    val finalTypes = types(c)(params) :+ c.Expr[Any](kv._2).actualType

    val finalTypeParameters = finalKeys.zip(finalTypes).flatMap {
      case (key, value) => List(keyNameToKeyType(c)(key), value)
    }

    val tparams = (1 to params.size / 2) map ((i) => derefField(c)(c.prefix.tree, i))
    val finalValues = (tparams :+ kv._2).toList

    newTuple(c)(finalTypeParameters, finalValues)
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

class NTuple4[N1, T1, N2, T2, N3, T3, N4, T4] (val _1: T1, val _2: T2, val _3: T3, val _4: T4) extends NTuple[NTuple4[N1, T1, N2, T2, N3, T3, N4, T4]] {
  override def toString = (_1, _2, _3, _4).toString
}

class NTuple5[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5) extends NTuple[NTuple5[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5]] {
  override def toString = (_1, _2, _3, _4, _5).toString
}

