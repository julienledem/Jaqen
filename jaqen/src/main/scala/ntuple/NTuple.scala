package ntuple

import scala.language.experimental.macros
import scala.reflect.macros.Context
import log._
import NTupleMacros._
import scala.collection.IterableLike
import scala.collection.immutable.Iterable
import scala.reflect.internal.FlagSets
import scala.reflect.internal.Flags
import scala.reflect.internal.Symbols

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
    Log("wtt.tpe :\n" + wtt.tpe)
    wtt.tpe match {
      case TypeRef(ThisType(ntuplePackage), nTupleName, parameters) if (nTupleName.fullName.contains("NTuple")) => parameters
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

  private def classType(c: Context)(className: String, typeParams: List[c.universe.Type]) = {
    import c.universe._
    val rawType = c.mirror.staticClass(className).toType
    appliedType(rawType.typeConstructor, typeParams)
  }

  private def nTupleType(c: Context)(size: Int, typeParams: List[c.universe.Type]) = {
    classType(c)(classOf[NTuple[_]].getName() + size, typeParams)
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
      val t = classType(c)(classOf[NTuple[_]].getName() + finalParams.size, finalTypeParams)
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

  def mapImpl[T](c: Context)(pair: c.Expr[Any])(f: c.Expr[Any])(implicit wttt: c.WeakTypeTag[T]) = {
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

  def nTupleToStringImpl[T](c: Context)(ntuple: c.Expr[T])(implicit wttt: c.WeakTypeTag[T]) = {
    import c.universe._
    val params = wttToParams(c)(wttt)

    val toStringParams = keys(c)(params)
            .zipWithIndex
            .flatMap {
              case (name, index) => List(
                  Literal(Constant(name)),
                  Literal(Constant(" -> ")),
                  derefField(c)(ntuple.tree, index),
                  Literal(Constant(", "))
              )
            }.dropRight(1)

    val list = c.Expr[List[Any]](Apply(Select(reify(List).tree, newTermName("apply")), toStringParams))

    reify {
      "(" + list.splice.mkString("") + ")"
    }
  }

  def map2Impl[T](c: Context)(pair: c.Expr[Any])(implicit wttt: c.WeakTypeTag[T]) = {
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

    // the key where to save the value
    val newKey = keyName(c)(target)
    // the indices of the key passed as parameter to the function
    val tupleFieldIndices = sources map (keyName(c)(_)) map ((key) => keyIndex(c)(c.Expr[Any](Literal(Constant(key))), wttt))
    // the actual values for those indices + the tuple to append to
    val fParams = tupleFieldIndices.map((index) => derefField(c)(c.prefix.tree, index)) :+ c.prefix.tree
    // the types of the fields passed to the function
    val fieldTypes = types(c)(params)
    // the type for the new key
    val nameType = keyNameToKeyType(c)(newKey)
    // the type parameters for the function
    val fParamTypes = tupleFieldIndices.map((index) => fieldTypes(index) ) :+ nameType
    // the function types
    val fType = classType(c)("ntuple.NFunction" + tupleFieldIndices.size, fParamTypes)

    // generating
    //  new ntuple.NFunction2[T1, T2, Any] (tuple._1, tuple._2, tuple) {
    //    type NTUPLENP1[N, T] = NTuple3[N1, T1, N2, T2, N, T]
    //  }


    c.Expr[Any](
    Block(
        List(
            ClassDef( // declare a class
                Modifiers(Flag.FINAL),
                newTypeName("$anon"), // it's anonymous
                List(),
                Template(
                    List(TypeTree(fType)),
                    emptyValDef,
                    List(
                        DefDef( // constructor
                            Modifiers(), nme.CONSTRUCTOR, List(), List(List()), TypeTree(),
                            Block(
                                List(
                                    Apply(
                                        Select(Super(This(newTypeName("$anon")), tpnme.EMPTY), nme.CONSTRUCTOR),
                                        fParams
                                    )
                                ),
                                Literal(Constant(()))
                            )
                        ),
                        {
                          val n = newTypeName("N")
                          val t = newTypeName("T")
                          val unboudTypeTree = TypeBoundsTree(
                                        TypeTree(typeOf[Nothing]),
                                        TypeTree(typeOf[Any])
                                    )
                           val nTypeTree = TypeTree().setOriginal(Ident(n))
                           val tTypeTree = TypeTree().setOriginal(Ident(t))
                           val ntnp1TypeTrees: List[TypeTree] = params.map(TypeTree(_)) :+ nTypeTree :+ tTypeTree

                        TypeDef(
                            Modifiers(),
                            newTypeName("NTUPLENP1"),
                            List(
                                TypeDef(Modifiers(Flag.PARAM), n, List(), unboudTypeTree),
                                TypeDef(Modifiers(Flag.PARAM), t, List(), unboudTypeTree)
                            ),
                            TypeTree().setOriginal(
                                AppliedTypeTree(
                                    Ident(c.mirror.staticClass("ntuple.NTuple" + (params.size / 2 + 1)).toType.typeSymbol),
                                    ntnp1TypeTrees
                                )
                            )
                        )
                        }
                    )
                )
            )
        ),
        Apply(Select(New(Ident(newTypeName("$anon"))), nme.CONSTRUCTOR), List())
    )
    )
  }
}

/**
 * A tuple where fields can be accessed by name
 *
 * @author Julien Le Dem
 */
trait NTuple[T <: NTuple[T]] {

  /**
   * returns the field named 'key' with the proper type
   * if key does not exist, a compilation error will occur
   * @param key a literal or a Symbol
   * example:
   * <code>
   * val tuple = t('a -> 1, 'b -> "2")
   * tuple('a)
   * => 1 (of type Int)
   * tuple('b)
   * => "2" (of type String)
   * </code>
   */
  def get(key: Any) = macro applyImp[T]
  /** @see get */
  def apply(key: Any) = macro applyImp[T]

  /**
   * adds a pair key -> value to the tuple
   * if key already exists, a compilation error will occur
   * key must be a literal or a symbol.
   * example: <code>
   * val tuple = t('a -> 1, 'b -> 2)
   * tuple + ('c -> 3)
   * => t('a -> 1, 'b -> 2, 'c -> 3)
   * </code>
   */
  def add(pair: (Any, Any)) = macro plusImpl[T]
  /** @see add */
  def +(pair: (Any, Any)) = macro plusImpl[T]

  /**
   * concats another NTuple to this one
   * if a key is defined in both tuples a compilation error will occur
   * <code>
   * val tuple1 = t('a -> 1, 'b -> 2)
   * val tuple2 = t('c -> 3, 'd -> 4)
   * tuple1 ++ tuple2
   * => t('a -> 1, 'b -> 2, 'c -> 3, 'd -> 4)
   * </code>
   */
  def concat[T2 <: NTuple[T2]](t: T2) = macro plusplusImpl[T,T2]
  /** @see concat */
  def ++[T2 <: NTuple[T2]](t: T2) = macro plusplusImpl[T,T2]

  /**
   * removes a key from the tuple
   * if key does not exist, a compilation error will occur
   * <code>
   * val tuple = t('a -> 1, 'b -> 2)
   * tuple - 'a
   * => t('b -> 2)
   * </code>
   */
  def remove(key: Any) = macro minusImpl[T]
  /** @see remove */
  def -(key: Any) = macro minusImpl[T]

  /**
   * takes a key -> value pair and replaces the existing key with the given value
   * if key does not exist, a compilation error will occur
   * example:
   * <code>
   * val tuple = t('a -> 1, 'b -> 2)
   * tuple -+ ('a -> 3)
   * => t('a -> 3, 'b -> 2)
   * </code>
   */
  def replace(pair: (Any, Any)) = macro replaceImpl[T]
  /** @see replace */
  def -+(pair: (Any, Any)) = macro replaceImpl[T]

  /**
   * prefixes all the key names with the given prefix.
   * useful to concatenate 2 tuples
   * example:
   * <code>
   * t('a -> 1, 'b -> 2).prefix("t")
   * => t('ta -> 1, 'tb -> 2)
   * </code>
   */
  def prefix(prefix: String) = macro prefixImpl[T]

  /**
   * takes a pair (inputs -> output) and a function
   * inputs: a tuple of the keys of the values to pass to the function
   * output: the key to set with the result
   * @returns the resulting tuple with the output key set with the result of the function
   * example:
   * <code>
   * val tuple = t('a -> 1, 'b -> 2)
   * tuple.map(('a, 'b) -> 'c) { (a: Int, b: Int) => a + b }
   * => t('a -> 1, 'b -> 2, 'c -> 3)
   * </code>
   */
  def map(pair: Any)(f: Any) = macro mapImpl[T]

  def map2(pair: Any) = macro map2Impl[T]

  /**
   * @returns a string representation of this tuple
   * example:
   * <code>
   * t('a -> 1, 'b -> 2).mkString
   * (a -> 1, b -> 2)
   * </code>
   */
  def mkString = macro mkStringImpl[T]

  /**
   * converts this tuple to a Map.
   * @returns an immutable Map
   */
  def toMap = macro toMapImpl[T]

  def append[N, T](t: T)
}

object NTuple {

  /**
   * creates a new NTuple from a list of key -> value pairs
   * the types of the values are preserved and will be returned accordingly when apply is called
   * if a key is defined twice a compilation error will occur
   * <code>
   * val tuple1 = t('a -> 1, 'b -> "2")
   * </code>
   */
  def t(pairs: Any*) = macro newTupleImpl

  implicit def nTupleToString[T <: NTuple[T]](ntuple: T): String = macro nTupleToStringImpl[T]
}

class NTuple0 extends NTuple[NTuple0] {
  override def toString = "()"

  override def append[N, T](t: T) = new NTuple1[N, T](t)
}

object Generator {
  def main(args: Array[String]) {
    def sig(i: Int) = "NTuple" + i + "[" + (for (j <- 1 to i) yield "N" + j + ", T" + j).mkString(", ") + "]"

    for (i <- 1 to 22) {
      println("class " + sig(i) + "(" + (for (j <- 1 to i) yield "val _" + j + ": T" + j).mkString(", ") + ") extends NTuple[" + sig(i) + "] {")
      println("  def toTuple = (" + (for (j <- 1 to i) yield "_" + j).mkString(", ") + ")")
      println("  override def toString = toTuple.toString")
      println("  override def append[N" + (i + 1) + ", T" + (i + 1) + "](t: T" + (i + 1) + ") = "
          + (if (i == 22) "null" else "new " + sig(i + 1) + "(" + (for (j <- 1 to i) yield "_" + j).mkString(", ") + ", t)"))
      println("}")
    }
    for (i <- 1 to 22) {
      val typesString = (for (j <- 1 to i) yield "T" + j).mkString(", ")
      println("class NFunction" + i + "[" + typesString + ", RESULT_NAME] (" + (for (j <- 1 to i) yield "val _" + j + ": T" + j).mkString(", ") + ", val destination: NTuple[_]) {")
      println("  type NTUPLENP1[_,_]")
      println("  def apply[RESULT_TYPE](f: Function" + i + "[" + typesString + ", RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {")
      println("    destination.append[RESULT_NAME, RESULT_TYPE](f(" + (for (j <- 1 to i) yield "_" + j).mkString(", ") + ")).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]")
      println("  }")
      println("}")
    }
  }
}
// classes bellow have been generated by the object Generator above
class NTuple1[N1, @specialized(Int, Long, Double, Char, Boolean) T1](val _1: T1) extends NTuple[NTuple1[N1, T1]] {
  def toTuple = (_1)
  override def toString = toTuple.toString
  override def append[N2, T2](t: T2) = new NTuple2[N1, T1, N2, T2](_1, t)
}
class NTuple2[N1, @specialized(Int, Long, Double, Char, Boolean) T1, N2, @specialized(Int, Long, Double, Char, Boolean) T2](val _1: T1, val _2: T2) extends NTuple[NTuple2[N1, T1, N2, T2]] {
  def toTuple = (_1, _2)
  override def toString = toTuple.toString
  override def append[N3, T3](t: T3) = new NTuple3[N1, T1, N2, T2, N3, T3](_1, _2, t)
}
class NTuple3[N1, T1, N2, T2, N3, T3](val _1: T1, val _2: T2, val _3: T3) extends NTuple[NTuple3[N1, T1, N2, T2, N3, T3]] {
  def toTuple = (_1, _2, _3)
  override def toString = toTuple.toString
  override def append[N4, T4](t: T4) = new NTuple4[N1, T1, N2, T2, N3, T3, N4, T4](_1, _2, _3, t)
}
class NTuple4[N1, T1, N2, T2, N3, T3, N4, T4](val _1: T1, val _2: T2, val _3: T3, val _4: T4) extends NTuple[NTuple4[N1, T1, N2, T2, N3, T3, N4, T4]] {
  def toTuple = (_1, _2, _3, _4)
  override def toString = toTuple.toString
  override def append[N5, T5](t: T5) = new NTuple5[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5](_1, _2, _3, _4, t)
}
class NTuple5[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5) extends NTuple[NTuple5[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5]] {
  def toTuple = (_1, _2, _3, _4, _5)
  override def toString = toTuple.toString
  override def append[N6, T6](t: T6) = new NTuple6[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6](_1, _2, _3, _4, _5, t)
}
class NTuple6[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6) extends NTuple[NTuple6[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6]] {
  def toTuple = (_1, _2, _3, _4, _5, _6)
  override def toString = toTuple.toString
  override def append[N7, T7](t: T7) = new NTuple7[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7](_1, _2, _3, _4, _5, _6, t)
}
class NTuple7[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7) extends NTuple[NTuple7[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7)
  override def toString = toTuple.toString
  override def append[N8, T8](t: T8) = new NTuple8[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8](_1, _2, _3, _4, _5, _6, _7, t)
}
class NTuple8[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8) extends NTuple[NTuple8[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8)
  override def toString = toTuple.toString
  override def append[N9, T9](t: T9) = new NTuple9[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9](_1, _2, _3, _4, _5, _6, _7, _8, t)
}
class NTuple9[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9) extends NTuple[NTuple9[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9)
  override def toString = toTuple.toString
  override def append[N10, T10](t: T10) = new NTuple10[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10](_1, _2, _3, _4, _5, _6, _7, _8, _9, t)
}
class NTuple10[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10) extends NTuple[NTuple10[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10)
  override def toString = toTuple.toString
  override def append[N11, T11](t: T11) = new NTuple11[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, t)
}
class NTuple11[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11) extends NTuple[NTuple11[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11)
  override def toString = toTuple.toString
  override def append[N12, T12](t: T12) = new NTuple12[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, t)
}
class NTuple12[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12) extends NTuple[NTuple12[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12)
  override def toString = toTuple.toString
  override def append[N13, T13](t: T13) = new NTuple13[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, t)
}
class NTuple13[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13) extends NTuple[NTuple13[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13)
  override def toString = toTuple.toString
  override def append[N14, T14](t: T14) = new NTuple14[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, t)
}
class NTuple14[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14) extends NTuple[NTuple14[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14)
  override def toString = toTuple.toString
  override def append[N15, T15](t: T15) = new NTuple15[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, t)
}
class NTuple15[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15) extends NTuple[NTuple15[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15)
  override def toString = toTuple.toString
  override def append[N16, T16](t: T16) = new NTuple16[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, t)
}
class NTuple16[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16) extends NTuple[NTuple16[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16)
  override def toString = toTuple.toString
  override def append[N17, T17](t: T17) = new NTuple17[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, t)
}
class NTuple17[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17) extends NTuple[NTuple17[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17)
  override def toString = toTuple.toString
  override def append[N18, T18](t: T18) = new NTuple18[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, t)
}
class NTuple18[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18) extends NTuple[NTuple18[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18)
  override def toString = toTuple.toString
  override def append[N19, T19](t: T19) = new NTuple19[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, t)
}
class NTuple19[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19) extends NTuple[NTuple19[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19)
  override def toString = toTuple.toString
  override def append[N20, T20](t: T20) = new NTuple20[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, t)
}
class NTuple20[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20) extends NTuple[NTuple20[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20)
  override def toString = toTuple.toString
  override def append[N21, T21](t: T21) = new NTuple21[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, t)
}
class NTuple21[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20, val _21: T21) extends NTuple[NTuple21[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21)
  override def toString = toTuple.toString
  override def append[N22, T22](t: T22) = new NTuple22[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21, N22, T22](_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, t)
}
class NTuple22[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21, N22, T22](val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20, val _21: T21, val _22: T22) extends NTuple[NTuple22[N1, T1, N2, T2, N3, T3, N4, T4, N5, T5, N6, T6, N7, T7, N8, T8, N9, T9, N10, T10, N11, T11, N12, T12, N13, T13, N14, T14, N15, T15, N16, T16, N17, T17, N18, T18, N19, T19, N20, T20, N21, T21, N22, T22]] {
  def toTuple = (_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, _22)
  override def toString = toTuple.toString
  override def append[N23, T23](t: T23) = null
}
class NFunction1[T1, RESULT_NAME] (val _1: T1, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function1[T1, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction2[T1, T2, RESULT_NAME] (val _1: T1, val _2: T2, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function2[T1, T2, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction3[T1, T2, T3, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function3[T1, T2, T3, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction4[T1, T2, T3, T4, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function4[T1, T2, T3, T4, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction5[T1, T2, T3, T4, T5, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function5[T1, T2, T3, T4, T5, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction6[T1, T2, T3, T4, T5, T6, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function6[T1, T2, T3, T4, T5, T6, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction7[T1, T2, T3, T4, T5, T6, T7, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function7[T1, T2, T3, T4, T5, T6, T7, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction8[T1, T2, T3, T4, T5, T6, T7, T8, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function8[T1, T2, T3, T4, T5, T6, T7, T8, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction9[T1, T2, T3, T4, T5, T6, T7, T8, T9, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function9[T1, T2, T3, T4, T5, T6, T7, T8, T9, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction10[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function10[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction11[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function11[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction12[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function12[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction13[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function13[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction14[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function14[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction15[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function15[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction16[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function16[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction17[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function17[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction18[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function18[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction19[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function19[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction20[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function20[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction21[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20, val _21: T21, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function21[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}
class NFunction22[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, RESULT_NAME] (val _1: T1, val _2: T2, val _3: T3, val _4: T4, val _5: T5, val _6: T6, val _7: T7, val _8: T8, val _9: T9, val _10: T10, val _11: T11, val _12: T12, val _13: T13, val _14: T14, val _15: T15, val _16: T16, val _17: T17, val _18: T18, val _19: T19, val _20: T20, val _21: T21, val _22: T22, val destination: NTuple[_]) {
  type NTUPLENP1[_,_]
  def apply[RESULT_TYPE](f: Function22[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, RESULT_TYPE]): NTUPLENP1[RESULT_NAME, RESULT_TYPE] = {
    destination.append[RESULT_NAME, RESULT_TYPE](f(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, _22)).asInstanceOf[NTUPLENP1[RESULT_NAME, RESULT_TYPE]]
  }
}

