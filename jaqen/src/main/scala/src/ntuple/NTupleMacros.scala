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

  def nameType(c: Context)(name: c.Expr[String]): c.universe.Type = {
    import c.universe._
    ConstantType(Constant(keyName(c)(name)))
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

//    Log(showRaw(pair.tree))

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

  def applyImp[T](c: Context)(key: c.Expr[Any])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    val kName = keyName(c)(key)
    val (n, params) = wttt.tpe match {
      case TypeRef(ThisType(ntuple), name, parameters) if (ntuple.fullName == "ntuple") => (name.fullName, parameters)
      case _ => c.abort(c.enclosingPosition, showRaw(wttt) + " is not an understood type")
    }

    val r = params
            .zipWithIndex
            .filter(_._2 % 2 == 0)
            .map((t) => (t._1, t._2 / 2))
            .collect {
          case (ConstantType(Constant(name)), index) if (name == kName) => index + 1
        }

    if (r.isEmpty) fail(c)(key)
    else if (r.size == 1) c.Expr[Any](Select(c.prefix.tree, newTermName("_" + r(0))))
    else c.abort(c.enclosingPosition, "more than one result for key " + kName)
  }

}

trait NTuple[T <: NTuple[T]] {

  def apply(key: Any) = macro applyImp[T]

//  override def toString = myToString[T]

//  def myToString[T] = macro toStringImpl[T]

}

object NTuple {

  def t(pair: Any*) = macro newTuple

  def newTuple(c: Context)(pair: c.Expr[Any]*) = {
    import c.universe._
    if (pair.size == 0) reify { new NTuple0 }
    else if (pair.size == 1) NTuple1.newTupleP(c)(pair(0))
    else if (pair.size == 2) NTuple2.newTupleP(c)(pair(0), pair(1))
    else c.abort(c.enclosingPosition, "size can only be up to 2. Got " + pair.size)
  }

}

class NTuple0 extends NTuple[NTuple0] {

//  def apply(key: Any) = macro NTuple0.applyImpl

  def +(pair1: (Any, Any)) = macro NTuple0.plusImpl

  override def toString = "()"
}

object NTuple0 {

  def plusImpl(c: Context)(pair1: c.Expr[(Any, Any)]) = {
    import c.universe._

    NTuple1.newTupleP(c)(pair1)
  }
//
//  def applyImpl(c: Context)(key: c.Expr[Any]) = {
//    import c.universe._
//    fail(c)(key)
//  }
}

class NTuple1[N1, T1](val _1: T1) extends NTuple[NTuple1[N1, T1]] {

//  def apply(key: Any) = macro NTuple1.applyImpl[N1]

  def +(pair2: (Any, Any)) = macro NTuple1.plusImpl[N1, T1]

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

//  def applyImpl[N1](c: Context)(key: c.Expr[Any])(implicit wttn1: c.WeakTypeTag[N1]) = {
//    import c.universe._
//
//    val e = c.Expr[NTuple1[_,_]](c.prefix.tree)
//    if (checkMatch(c)(key, wttn1)) reify { e.splice._1 }
//    else fail(c)(key)
//  }

//  def toStringImpl[N1](c: Context)(implicit wttn1: c.WeakTypeTag[N1]) = {
//    import c.universe._
//
//    val e = c.Expr[NTuple1[_,_]](c.prefix.tree)
//
//    val name1 = name(c)(wttn1)
//    reify{
//      "(" + show(name1) + "=" +  e.splice._1 + ")"
//    }
//  }

  def newTupleP(c: Context)(pair: c.Expr[Any]) = {
    import c.universe._

    val (key, value) = pairToKV(c)(pair)

    newTuple(c)(key, value)
  }

  def newTuple(c: Context)(name: c.Expr[String], v: c.Expr[Any]) = {
    import c.universe._

    val valueType1 = v.actualType

    val nameType1 = nameType(c)(name)

    val t = appliedType(typeOf[ntuple.NTuple1[_,_]].typeConstructor, List(nameType1, valueType1))
    c.Expr[ntuple.NTuple1[_,_]](`new`(c)(t, List(v.tree)))
  }

}

class NTuple2[N1, T1, N2, T2] (val _1: T1, val _2: T2) extends NTuple[NTuple2[N1, T1, N2, T2]] {

//  def apply[A](key: Any) = macro NTuple2.applyImpl[N1, T1, N2, T2, A]

//  override def toString = "(" + getName[N1] + "=" + _1 + ", " + getName[N2] + "=" + _2 + ")"

}

object NTuple2 {

//  def applyImpl[N1, T1, N2, T2, A: c.WeakTypeTag](c: Context)(key: c.Expr[Any])
//  (implicit wtta: c.WeakTypeTag[A], wttn1: c.WeakTypeTag[N1], wttt1: c.WeakTypeTag[T1], wttn2: c.WeakTypeTag[N2], wttt2: c.WeakTypeTag[T2]) = {
//    import c.universe._
//
//    val e = c.Expr[NTuple2[_,_,_,_]](c.prefix.tree)
//    if (checkMatch(c)(key, wttn1)) reify { e.splice._1 }
//    else if (checkMatch(c)(key, wttn2)) reify { e.splice._2 }
//    else fail(c)(key)
//  }

  def newTupleP(c: Context)(pair1: c.Expr[Any], pair2: c.Expr[Any]) = {
    import c.universe._

    val (key1, value1) = pairToKV(c)(pair1)
    val (key2, value2) = pairToKV(c)(pair2)

    newTuple(c)(key1, value1, key2, value2)
  }

  def newTuple(c: Context)(name1: c.Expr[String], v1: c.Expr[Any], name2: c.Expr[String], v2: c.Expr[Any]) = {
import c.universe._

    val nameType1 = nameType(c)(name1)
    val nameType2 = nameType(c)(name2)

    val valueType1 = v1.actualType
    val valueType2 = v2.actualType

    val t = appliedType(typeOf[ntuple.NTuple2[_,_,_,_]].typeConstructor, List(nameType1, valueType1, nameType2, valueType2))

    c.Expr[ntuple.NTuple2[_,_,_,_]](`new`(c)(t, List(v1.tree, v2.tree)))
  }

}
